"""Split one list file in two by number of edges, so that each gzipped part stays under a size
limit (GitHub refuses files over 100 MB).

M is the lower median of the edge counts: the least m such that at least half of the graphs have
at most m edges. The script writes nNN.edges_le_M.g6.gz (the graphs with at most M edges) and
nNN.edges_ge_{M+1}.g6.gz (the graphs with at least M+1 edges). Each part keeps the input's order
(C byte order of the graph6 strings), is written with a fixed gzip header (no file name, mtime 0)
so that a rerun gives identical bytes, and must be under the limit; finally the two parts are read
back and checked, as streams, to be the graphs of the input in their ranges, in order, and to
merge to the input, line for line.

The number of edges of a graph6 string on n <= 62 vertices is the number of 1 bits in its data
bytes (each byte after the first carries 6 bits of the upper triangle, offset by 63; the padding
bits are 0).

Usage: python split_by_edges.py INPUT.g6.gz OUTDIR [LIMIT_BYTES]   (default limit 100000000)
"""
import gzip, heapq, os, re, sys
from itertools import islice, zip_longest

POP = bytes(bin(max(b - 63, 0)).count("1") for b in range(256))
BATCH = 1 << 16       # lines per write


def edges(s):
    return sum(s[1:].translate(POP))


def write_gz(path, lines):
    """Write the lines (bytes), each followed by a newline, gzipped with a fixed header, in batches;
    return the size of the file."""
    with open(path, "wb") as raw, \
            gzip.GzipFile(filename="", mode="wb", compresslevel=9, fileobj=raw, mtime=0) as f:
        batch = []
        for s in lines:
            batch.append(s)
            if len(batch) == BATCH:
                f.write(b"\n".join(batch) + b"\n")
                batch = []
        if batch:
            f.write(b"\n".join(batch) + b"\n")
    return os.path.getsize(path)


def read_gz(path):
    """The strings of a gzipped file (as its .read().split()), read as a stream."""
    with gzip.open(path, "rb") as f:
        for line in f:
            yield from line.split()


def same(xs, ys):
    """Whether two iterables have the same elements in the same order."""
    end = object()
    return all(x == y for x, y in zip_longest(xs, ys, fillvalue=end))


def main():
    src, out = sys.argv[1], sys.argv[2]
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else 100_000_000
    n = int(re.fullmatch(r"n(\d+)\.g6(\.gz)?", os.path.basename(src)).group(1))
    with (gzip.open(src, "rb") if src.endswith(".gz") else open(src, "rb")) as f:
        L = f.read().split()
    assert all(x < y for x, y in zip(L, islice(L, 1, None))), "input not sorted and unique"
    assert all(s[0] == n + 63 for s in L), "a string not on n vertices"
    E = [edges(s) for s in L]
    count = {}
    for e in E:
        count[e] = count.get(e, 0) + 1
    acc = 0
    for M in sorted(count):
        acc += count[M]
        if 2 * acc >= len(L):
            break
    a = os.path.join(out, f"n{n:02d}.edges_le_{M}.g6.gz")
    b = os.path.join(out, f"n{n:02d}.edges_ge_{M + 1}.g6.gz")
    sa = write_gz(a, (s for s, e in zip(L, E) if e <= M))
    sb = write_gz(b, (s for s, e in zip(L, E) if e > M))
    nlo = sum(c for e, c in count.items() if e <= M)
    del E
    assert sa < limit and sb < limit, ("a part is over the limit", sa, sb)
    assert (same(read_gz(a), (s for s in L if edges(s) <= M))
            and same(read_gz(b), (s for s in L if edges(s) > M))
            and same(heapq.merge(read_gz(a), read_gz(b)), L)), "the parts do not merge to the input"
    print(f"n={n}: {len(L)} graphs, edges {min(count)}..{max(count)}, M={M}: "
          f"{nlo} graphs with at most {M} edges ({sa} bytes), "
          f"{len(L) - nlo} with at least {M + 1} ({sb} bytes)")


if __name__ == "__main__":
    main()
