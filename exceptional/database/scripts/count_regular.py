"""Count the regular graphs in the database lists, per n (a check against the 187 regular
exceptional graphs of Bussemaker, Cvetkovic and Seidel).  Writes the regular ones to
OUTFILE as 'list n k g6'.  Usage: python count_regular.py DBDIR NWORKERS OUTFILE"""
import sys, os, json
from collections import Counter
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e8common import g6_decode, tri_index, iter_list

CHUNK = 20000


def regular_in(args):
    lines, n = args
    I, J = tri_index(n)
    out = []
    for s in lines:
        _, bits = g6_decode(s)
        deg = np.bincount(I, weights=bits, minlength=n) + np.bincount(J, weights=bits, minlength=n)
        if deg.min() == deg.max():
            out.append((int(deg[0]), s.decode()))
    return n, out


def chunks(db, kind, n):
    """The list `kind` on n vertices in tasks of CHUNK strings, read as a stream as the pool takes
    them, so that no whole list is held in memory."""
    batch = []
    for s in iter_list(db, kind, n):
        batch.append(s)
        if len(batch) == CHUNK:
            yield batch, n
            batch = []
    if batch:
        yield batch, n


def main():
    db, nw, outfile = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    with open(os.path.join(db, "counts.json")) as f:
        C = json.load(f)
    res = []
    with Pool(nw) as pool:
        for kind in ("minus2", "above-minus2"):
            for n in C["complete_for_n"]:
                for m, out in pool.imap_unordered(regular_in, chunks(db, kind, n)):
                    res += [(kind, m, k, s) for k, s in out]
    res.sort()
    with open(outfile, "w") as f:
        for r in res:
            f.write("%s %d %d %s\n" % r)
    print("regular exceptional graphs per (list, n):", sorted(Counter((r[0], r[1]) for r in res).items()))
    print("per (n, valency):", sorted(Counter((r[1], r[2]) for r in res).items()))
    print("total:", len(res))


if __name__ == "__main__":
    main()
