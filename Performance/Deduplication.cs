using System.Text;
using BenchmarkDotNet.Attributes;
using Combination.StringPools;

namespace Performance;

#pragma warning disable CS8618
public class Deduplication
{
    internal static readonly Random Random = new();

    [ParamsSource(nameof(CreateDataSet))]
    public string[] DataSet;

    [ParamsSource(nameof(CreatePools))]
    public IUtf8DeduplicatedStringPool Pool;

    [Benchmark]
    public void DoAdd() => Pool.Add(DataSet[Random.Next(0, DataSet.Length)]);

    public IEnumerable<string[]> CreateDataSet()
    {
        foreach (var size in new[] { 10000, 100000, 1000000, 10000000 })
        {
            yield return Enumerable.Range(0, size).Select(_ => RandomString()).ToArray();
        }
    }

    public IEnumerable<IUtf8DeduplicatedStringPool> CreatePools()
        => (new[] { 9, 10, 12, 14, 16 }).Select(bits => StringPool.DeduplicatedUtf8(4096, 1, bits));

    internal static string RandomString()
    {
        var len = Random.Next(6, 12);
        var sb = new StringBuilder(len);
        for (var i = 0; i < len; ++i)
        {
            sb.Append((char)('a' + Random.Next(26)));
        }

        return sb.ToString();
    }
}
