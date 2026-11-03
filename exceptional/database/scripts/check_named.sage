# Literature checks on the database (SageMath).  Usage:
#   sage check_named.sage DBDIR [LEVELDIR]
# LEVELDIR (optional) holds the growth levels nNN.g6 and infoNN.txt (all connected graphs
# represented in E8), used to confirm that the generalized line graphs were generated
# and classified as such.
import sys, os, subprocess, json, bisect
db = sys.argv[1]
# the shared list reader (Sage may run a preparsed copy of this file from elsewhere)
sys.path.insert(0, os.path.join(os.path.abspath(db), "scripts"))
from e8common import read_list
lev = sys.argv[2] if len(sys.argv) > 2 else None

def canon(X):
    s = X.graph6_string()
    return subprocess.run(["labelg", "-q"], input=(s + "\n").encode(),
                          capture_output=True, check=True).stdout.split()[0].decode()

# Only the last list read of each kind is kept (sorted, so a lookup is a bisection): the lists
# (A) on 15 to 21 vertices hold millions of strings each.
_last = {}
def in_list(kind, n, s):
    if _last.get(kind, (None,))[0] != n:
        _last.pop(kind, None)
        _last[kind] = (n, read_list(db, kind, n))
    L = _last[kind][1]
    b = s.encode()
    i = bisect.bisect_left(L, b)
    return i < len(L) and L[i] == b

def info_lookup(n, s):
    if lev is None:
        return None
    p = os.path.join(lev, "info%02d.txt" % n)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        for line in f:
            if line.startswith(s + " "):
                return line.split()
    return "absent"

with open(os.path.join(db, "counts.json")) as f:
    C = json.load(f)
done = set(int(k) for k in C["complete_for_n"])

named = [("Petersen (10,3,0,1)", graphs.PetersenGraph()),
         ("Clebsch (16,10,6,6)", graphs.ClebschGraph().complement()),
         ("Shrikhande (16,6,2,2)", graphs.ShrikhandeGraph()),
         ("Schlaefli (27,16,10,8)", graphs.SchlaefliGraph())]
for i, X in enumerate(graphs.chang_graphs()):
    named.append(("Chang %d (28,12,6,4)" % (i + 1), X))
print("Exceptional strongly regular graphs (should be in list (A)):")
for name, X in named:
    n = X.order()
    assert X.is_strongly_regular() and min(X.spectrum()) == -2
    if n not in done:
        print("  %-26s n=%d: level not complete" % (name, n)); continue
    print("  %-26s n=%d: %s" % (name, n, "PRESENT" if in_list("minus2", n, canon(X)) else "MISSING"))

glg = []
for m in range(3, 10):
    glg.append(("L(K_%d)" % m, graphs.CompleteGraph(m).line_graph()))
for m in range(2, 10):
    glg.append(("CP(%d)" % m, graphs.CompleteMultipartiteGraph([2] * m)))
for a in range(1, 9):
    for b in range(a, 10 - a):
        if a + b >= 3:
            glg.append(("L(K_%d,%d)" % (a, b), graphs.CompleteBipartiteGraph(a, b).line_graph()))
print("Generalized line graphs (should NOT be in the lists):")
bad = 0
for name, X in glg:
    n = X.order()
    if n not in done or not X.is_connected():
        continue
    s = canon(X)
    inA, inB = in_list("minus2", n, s), in_list("above-minus2", n, s)
    bad += inA or inB
    inf = info_lookup(n, s)
    r = (2 * identity_matrix(n) + X.adjacency_matrix()).rank()
    where = "not in growth (rank %d > 8)" % r if r > 8 else ("growth level: %s" % (" ".join(inf[1:3]) if isinstance(inf, list) else inf))
    print("  %-12s n=%2d: in (A) %s, in (B) %s; %s" % (name, n, inA, inB, where))
print("generalized line graphs found in the lists:", bad)

print("(the regular exceptional graphs are counted by count_regular.py)")
