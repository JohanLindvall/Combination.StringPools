using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;

// ReSharper disable InconsistentNaming - We used internal static fields to avoid unnecessary wrapping

namespace Combination.StringPools;

internal sealed class Utf8StringPool : IUtf8DeduplicatedStringPool
{
    private const int
        PoolIndexBits =
            24; // Number of bits to use for pool index in handle (more bits = more pools, but less strings per pool)

    // Number of bits available for the pool-relative offset in a handle.
    private const int OffsetBits = 64 - PoolIndexBits;

    // Mask for the pool-relative offset part of a handle.
    private const ulong OffsetMask = (1UL << OffsetBits) - 1;

    // A deduplication table entry packs an occupancy flag, a hash tag and the pool-relative offset.
    // Since every entry in a pool's table shares the same pool index, those high handle bits would be
    // wasted; instead we store hash tag bits there so probe collisions can be rejected without touching
    // the string data. Layout: bit 63 = occupied, bits 40..62 = hash tag, bits 0..39 = offset.
    private const int TagBits = PoolIndexBits - 1;
    private const ulong OccupiedBit = 1UL << 63;
    private const ulong TagMask = (1UL << TagBits) - 1;

    // Maximum fill factor for deduplication table. Performance degrades when it is close to 1.
    private const float MaxDeduplicationTableFillFactor = 0.9f;

    private static readonly List<Utf8StringPool?> Pools = new();

#pragma warning disable IDE1006 // Naming Styles
    internal static long totalAllocatedBytes;
    internal static long totalUsedBytes;
    internal static long totalAddedBytes;
#pragma warning restore IDE1006 // Naming Styles

    internal int deduplicationFillCount;

    private readonly List<nint> pages = new();
    private readonly int index;
    private long writePosition, usedBytes, addedBytes;

    private ulong[]? deduplicationTable;
    private readonly DisposeLock disposeLock = new();
    private int deduplicationTableBits; // Number of bits to use for deduplication table (2^bits entries)
    private readonly int pageSize;

    private readonly object writeLock = new();

    // ReSharper disable once MemberCanBePrivate.Global
    public Utf8StringPool(int pageSize, int initialPageCount, bool deduplicateStrings, int deduplicationTableBits)
    {
        if (pageSize < 16)
        {
            // We need at least 16 bytes to store the length of the string and an actual string
            throw new ArgumentOutOfRangeException(nameof(pageSize));
        }

        if (deduplicationTableBits < 2 || deduplicationTableBits > 24)
        {
            throw new ArgumentOutOfRangeException(nameof(deduplicationTableBits));
        }

        if (initialPageCount < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(initialPageCount));
        }

        this.deduplicationTableBits = deduplicationTableBits;
        this.pageSize = pageSize;
        if (deduplicateStrings)
        {
            deduplicationTable = new ulong[(1 << deduplicationTableBits)];
        }

        bool didAlloc;
        lock (Pools)
        {
            if (Pools.Count >= (1 << PoolIndexBits) - 1)
            {
                throw new InvalidOperationException("Too many string pools allocated in process");
            }

            Pools.Add(this);
            index = Pools.Count - 1;
            didAlloc = EnsureCapacity(initialPageCount);
        }

        if (didAlloc)
        {
            AllocationChanged?.Invoke(this, EventArgs.Empty);
        }
    }

    PooledUtf8String IUtf8StringPool.Add(ReadOnlySpan<char> value)
    {
        // Encode in a single pass: GetMaxByteCount is cheap arithmetic, avoiding the full
        // scan that GetByteCount would do before the actual GetBytes pass.
        var maxByteCount = Encoding.UTF8.GetMaxByteCount(value.Length);
        if (maxByteCount <= 16384)
        {
            // Use the stack for small strings
            Span<byte> utf8 = stackalloc byte[maxByteCount];
            var utf8ByteCount = Encoding.UTF8.GetBytes(value, utf8);
            return AddInternal(utf8[..utf8ByteCount]);
        }

        var buffer = new byte[maxByteCount];
        var bufferByteCount = Encoding.UTF8.GetBytes(value, buffer);
        return AddInternal(buffer.AsSpan(0, bufferByteCount));
    }

    PooledUtf8String IUtf8StringPool.Add(ReadOnlySpan<byte> value)
        => AddInternal(value);

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    public static int GetAllocationSize(int length) => length + 1 + (BitOperations.Log2((uint)length) / 7);


    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    private PooledUtf8String AddInternal(ReadOnlySpan<byte> value)
    {
        var length = value.Length;
        if (length == 0)
        {
            return PooledUtf8String.Empty;
        }

        var structLength = GetAllocationSize(length);
        if (structLength > pageSize)
        {
            throw new ArgumentOutOfRangeException(nameof(value), "String is too long to be pooled");
        }

        ulong stringHash = 0;
        var didAlloc = false;
        var oldSize = Interlocked.Read(ref usedBytes);

        Interlocked.Add(ref totalAddedBytes, structLength);
        Interlocked.Add(ref addedBytes, structLength);

        if (deduplicationTable is not null)
        {
            stringHash = StringHash.Compute(value);
            if (TryDeduplicate(stringHash, value, out var result))
            {
                return new PooledUtf8String(result);
            }
        }

        lock (writeLock)
        {
            if (disposeLock.IsDisposed)
            {
                throw new ObjectDisposedException("String pool is already disposed");
            }

            if (oldSize != Interlocked.Read(ref usedBytes) && TryDeduplicate(stringHash, value, out var result))
            {
                return new PooledUtf8String(result);
            }

            var currentPageIndex = checked((int)(writePosition / pageSize));
            var pageWritePosition = writePosition % pageSize;

            nint writePtr;
            int pageStartOffset;
            if (pageSize - pageWritePosition >= structLength)
            {
                if (pageWritePosition == 0)
                {
                    didAlloc = EnsureCapacity(currentPageIndex + 1);
                }

                writePtr = pages[currentPageIndex];
                pageStartOffset = (int)pageWritePosition;
                writePosition += structLength;
            }
            else
            {
                ++currentPageIndex;
                writePosition = (currentPageIndex * (long)pageSize) + structLength;
                didAlloc = EnsureCapacity(currentPageIndex + 1);
                writePtr = pages[currentPageIndex];
                pageStartOffset = 0;
            }

            unsafe
            {
                var ptr = (byte*)(writePtr + pageStartOffset);
                var write = length;
                while (true)
                {
                    if (write > 0x7f)
                    {
                        *ptr++ = unchecked((byte)(0x80 | (write & 0x7f)));
                    }
                    else
                    {
                        *ptr++ = unchecked((byte)write);
                        break;
                    }

                    write >>= 7;
                }

                var stringWritePtr = new Span<byte>(ptr, length);
                value.CopyTo(stringWritePtr);
            }

            var handle = ((ulong)index << (64 - PoolIndexBits)) | (ulong)(writePosition - structLength);

            if (deduplicationTable is not null)
            {
                AddToDeduplicationTable(deduplicationTable, deduplicationTableBits, stringHash, handle);
            }
            Interlocked.Add(ref totalUsedBytes, structLength);
            Interlocked.Add(ref usedBytes, structLength);

            if (didAlloc)
            {
                AllocationChanged?.Invoke(this, EventArgs.Empty);
            }

            StringAdded?.Invoke(this, EventArgs.Empty);

            return new PooledUtf8String(handle);
        }
    }

    long IStringPool.AddedBytes => addedBytes;

    long IStringPool.UsedBytes => usedBytes;

    long IStringPool.AllocatedBytes => pages.Count * pageSize;

    PooledUtf8String? IUtf8DeduplicatedStringPool.TryGet(ReadOnlySpan<char> value)
    {
        // Encode in a single pass: GetMaxByteCount is cheap arithmetic, avoiding the full
        // scan that GetByteCount would do before the actual GetBytes pass.
        var maxByteCount = Encoding.UTF8.GetMaxByteCount(value.Length);
        if (maxByteCount <= 16384)
        {
            // Use the stack for small strings
            Span<byte> utf8 = stackalloc byte[maxByteCount];
            var utf8ByteCount = Encoding.UTF8.GetBytes(value, utf8);
            return TryGetInternal(utf8[..utf8ByteCount]);
        }

        var buffer = new byte[maxByteCount];
        var bufferByteCount = Encoding.UTF8.GetBytes(value, buffer);
        return TryGetInternal(buffer.AsSpan(0, bufferByteCount));
    }

    PooledUtf8String? IUtf8DeduplicatedStringPool.TryGet(ReadOnlySpan<byte> value)
        => TryGetInternal(value);

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    private PooledUtf8String? TryGetInternal(ReadOnlySpan<byte> value)
    {
        if (value.Length == 0)
        {
            return PooledUtf8String.Empty;
        }

        if (deduplicationTable is null)
        {
            throw new InvalidOperationException("Deduplication is not enabled for this pool");
        }

        if (!TryDeduplicate(StringHash.Compute(value), value, out var result))
        {
            return null;
        }

        return new PooledUtf8String(result);
    }

    private bool TryDeduplicate(ulong stringHash, ReadOnlySpan<byte> value, out ulong offset)
    {
        using (disposeLock.PreventDispose())
        {
            var table = deduplicationTable;
            if (table == null)
            {
                offset = ulong.MaxValue;
                return false;
            }

            var tableMask = (1 << deduplicationTableBits) - 1;
            var tableIndex = (int)stringHash & tableMask;
            var tag = (stringHash >> (64 - TagBits)) << OffsetBits;
            for (var i = 0; i <= tableMask; i++)
            {
                var tableEntry = table[(tableIndex + i) & tableMask];
                if (tableEntry == 0)
                {
                    offset = ulong.MaxValue;
                    return false;
                }

                // Reject without touching the string data unless the stored hash tag matches.
                if ((tableEntry & (TagMask << OffsetBits)) != tag)
                {
                    continue;
                }

                var poolOffset = tableEntry & OffsetMask;
                var poolBytes = GetStringBytes(poolOffset);
                if (poolBytes.Length == value.Length && value.SequenceEqual(poolBytes))
                {
                    offset = ((ulong)index << OffsetBits) | poolOffset;
                    return true;
                }
            }

            offset = ulong.MaxValue;
            return false;
        }
    }

    private void AddToDeduplicationTable(ulong[]? currentTable, int currentTableBits, ulong stringHash, ulong handle)
    {
        if (currentTable == null)
        {
            return;
        }

        var tableSize = 1 << currentTableBits;
        var tableMask = tableSize - 1;
        var tableIndex = (int)stringHash & tableMask;
        var entry = OccupiedBit | ((stringHash >> (64 - TagBits)) << OffsetBits) | (handle & OffsetMask);
        for (var i = 0; i < tableSize; i++)
        {
            var slot = (tableIndex + i) & tableMask;
            if (currentTable[slot] == 0)
            {
                ++deduplicationFillCount;
                currentTable[slot] = entry;
                if (deduplicationFillCount > tableSize * MaxDeduplicationTableFillFactor)
                {
                    ResizeDeduplicationTable(currentTableBits + 1);
                }
                return;
            }
        }
        ResizeDeduplicationTable(currentTableBits + 1);
    }

    private void ResizeDeduplicationTable(int newBits)
    {
        if (deduplicationTable is null)
        {
            return;
        }
        var newDeduplicationTable = new ulong[1 << newBits];
        deduplicationFillCount = 0;
        var tableSize = 1 << deduplicationTableBits;
        for (var i = 0; i < tableSize; ++i)
        {
            var tableEntry = deduplicationTable[i];
            if (tableEntry != 0)
            {
                var poolOffset = tableEntry & OffsetMask;
                var poolBytes = GetStringBytes(poolOffset);
                AddToDeduplicationTable(newDeduplicationTable, newBits, StringHash.Compute(poolBytes), poolOffset);
            }
        }
        deduplicationTable = newDeduplicationTable;
        deduplicationTableBits = newBits;
    }

    public static string Get(ulong handle)
    {
        if (handle == ulong.MaxValue)
        {
            return string.Empty;
        }

        return Encoding.UTF8.GetString(GetBytes(handle));
    }

    public static ReadOnlySpan<byte> GetBytes(ulong handle)
    {
        if (handle == ulong.MaxValue)
        {
            return Array.Empty<byte>();
        }

        var poolIndex = handle >> (64 - PoolIndexBits);
        if (poolIndex >= (ulong)Pools.Count)
        {
            throw new ArgumentException("Bad string pool offset", nameof(handle));
        }

        var pool = Pools[(int)poolIndex] ?? throw new ObjectDisposedException("String pool is disposed");

        return pool.GetFromPool(handle);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    private ReadOnlySpan<byte> GetFromPool(ulong handle)
    {
        using (disposeLock.PreventDispose())
        {
            var offset = handle & ((1UL << (64 - PoolIndexBits)) - 1);
#if DEBUG
            var poolIndex = handle >> (64 - PoolIndexBits);
            var refPool = Pools[(int)poolIndex];
            if (refPool != this)
            {
                throw new InvalidOperationException($"Internal error: Deduplicated string pool mismatch ({index} != {poolIndex})");
            }
#endif
            return GetStringBytes(offset);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    private ReadOnlySpan<byte> GetStringBytes(ulong offset)
    {
        var page = checked((int)(offset / (ulong)pageSize));
        var pageOffset = (int)(offset % (ulong)pageSize);
        if (page < 0 || page >= pages.Count)
        {
            throw new ArgumentOutOfRangeException(
                nameof(offset),
                $"Invalid handle value, page {page} is out of range 0..{pages.Count}, strings {addedBytes} {usedBytes}  --- {offset}");
        }

        unsafe
        {
            var ptr = (byte*)(pages[page] + pageOffset);
            var length = 0;
            var shl = 0;
            while (true)
            {
                var t = *ptr++;
                length += (t & 0x7f) << shl;
                shl += 7;
                if ((t & 0x80) == 0)
                {
                    break;
                }
            }

            return new ReadOnlySpan<byte>(ptr, length);
        }
    }

    public static int GetLength(ulong handle)
    {
        if (handle == ulong.MaxValue)
        {
            return 0;
        }

        var poolIndex = (handle >> (64 - PoolIndexBits)) & ((1 << PoolIndexBits) - 1);
        if (poolIndex >= (ulong)Pools.Count)
        {
            throw new ArgumentException("Bad string pool offset", nameof(handle));
        }

        var pool = Pools[(int)poolIndex] ?? throw new ObjectDisposedException("String pool is disposed");

        return pool.GetStringLength(handle & ((1L << (64 - PoolIndexBits)) - 1));
    }

    public static IUtf8StringPool? GetStringPool(ulong handle)
    {
        if (handle == ulong.MaxValue)
        {
            return null;
        }

        var poolIndex = handle >> (64 - PoolIndexBits);
        return poolIndex >= (ulong)Pools.Count ? null : Pools[(int)poolIndex];
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    private int GetStringLength(ulong offset)
    {
        using (disposeLock.PreventDispose())
        {
            var page = checked((int)(offset / (ulong)pageSize));
            var pageOffset = (int)(offset % (ulong)pageSize);
            if (page < 0 || page >= pages.Count)
            {
                throw new ArgumentOutOfRangeException(nameof(offset), $"Invalid handle value, page {page} is out of range 0..{pages.Count}");
            }

            unsafe
            {
                var ptr = (byte*)(pages[page] + pageOffset);
                var length = 0;
                var shl = 0;
                while (true)
                {
                    var t = *ptr++;
                    length += (t & 0x7f) << shl;
                    shl += 7;
                    if ((t & 0x80) == 0)
                    {
                        break;
                    }
                }

                return length;
            }
        }
    }

    private bool EnsureCapacity(int numPages)
    {
        if (numPages <= pages.Count)
        {
            return false;
        }

        for (var i = pages.Count; i < numPages; i++)
        {
            pages.Add(Marshal.AllocHGlobal(pageSize));
            Interlocked.Add(ref totalAllocatedBytes, pageSize);
        }

        return true;
    }

    public static event EventHandler? AllocationChanged;

    public static event EventHandler? StringAdded;

    ~Utf8StringPool()
    {
        Deallocate();
    }

    public void Dispose()
    {
        GC.SuppressFinalize(this);
        Deallocate();
    }

    private void Deallocate()
    {
        disposeLock.BeginDispose();
        lock (Pools)
        {
            Pools[index] = null;
        }

        lock (writeLock)
        {
            foreach (var page in pages)
            {
                Interlocked.Add(ref totalAllocatedBytes, -pageSize);
                Marshal.FreeHGlobal(page);
            }

            Interlocked.Add(ref totalUsedBytes, -usedBytes);
            Interlocked.Add(ref totalAddedBytes, -addedBytes);

            usedBytes = addedBytes = 0;

            pages.Clear();
        }

        // Don't send this here since we are being deallocated
        AllocationChanged?.Invoke(null, EventArgs.Empty);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    internal static bool StringsEqual(ulong a, ulong b)
    {
        return StringsCompare(a, b) == 0;
    }

    public override string ToString() =>
        $"Utf8StringPool(bits={deduplicationTableBits}, dedup={deduplicationTable is not null}, pages={pages.Count}, used={usedBytes}, added={addedBytes})";

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    public static int StringsCompare(ulong a, ulong b)
    {
        if (a == ulong.MaxValue)
        {
            return b == ulong.MaxValue ? 0 : -1;
        }

        if (b == ulong.MaxValue)
        {
            return 1;
        }

        if (a == b)
        {
            return 0;
        }

        var aPoolIndex = a >> (64 - PoolIndexBits);
        var bPoolIndex = b >> (64 - PoolIndexBits);
        if (aPoolIndex >= (ulong)Pools.Count)
        {
            throw new ArgumentException("Bad string pool offset", nameof(a));
        }

        if (bPoolIndex >= (ulong)Pools.Count)
        {
            throw new ArgumentException("Bad string pool offset", nameof(b));
        }

        var aOffset = a & ((1L << (64 - PoolIndexBits)) - 1);
        var bOffset = b & ((1L << (64 - PoolIndexBits)) - 1);
        var aPool = Pools[(int)aPoolIndex] ?? throw new ObjectDisposedException("String pool is disposed");

        if (aPoolIndex != bPoolIndex)
        {
            var bPool = Pools[(int)bPoolIndex] ?? throw new ObjectDisposedException("String pool is disposed");

            using (aPool.disposeLock.PreventDispose())
            {
                using (bPool.disposeLock.PreventDispose())
                {
                    return aPool.GetStringBytes(aOffset).SequenceCompareTo(bPool.GetStringBytes(bOffset));
                }
            }
        }

        if (aPool.deduplicationTable is not null && aOffset == bOffset)
        {
            // If the strings are in the same deduplicated pool, we can just compare the offsets
            return 0;
        }

        using (aPool.disposeLock.PreventDispose())
        {
            return aPool.GetStringBytes(aOffset).SequenceCompareTo(aPool.GetStringBytes(bOffset));
        }
    }
}
