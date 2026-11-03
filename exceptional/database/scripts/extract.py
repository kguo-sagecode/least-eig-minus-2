"""Extract the exceptional graphs on n vertices from the info file of level n and save them
to the database, and update counts.json.  Usage: python extract.py n INFOFILE DBDIR [elapsed]

info line: g6 rank latticedet nvalidextensions   (sorted, LC_ALL=C byte order)
exceptional  <=> (rank, det) in {(6,3),(7,2),(8,1)}  (lattice E6, E7, E8)
list (A)     <=> exceptional and rank < n  (2I+A singular: least eigenvalue -2)
list (B)     <=> exceptional and rank = n  (2I+A positive definite: least eigenvalue > -2)
maximal      <=> exceptional with no one-vertex extension represented in E8
"""
import sys, os, json, gzip, time
EXC = {(6, 3): "E6", (7, 2): "E7", (8, 1): "E8"}
LIMIT = 20 * 10**6
BATCH = 1 << 16       # lines per write


def lattice_type(r, d):
    if (r, d) in EXC:
        return EXC[(r, d)]
    if r >= 4 and d == 4:
        return f"D{r}"
    if d == r + 1:
        return f"A{r}"
    if r <= 5:          # det not computed for r <= 5 (always A or D)
        return "AD"
    raise ValueError((r, d))


def write_lines(f, lines):
    """Write the lines, each followed by a newline, in batches (not as one string of the whole list)."""
    for i in range(0, len(lines), BATCH):
        f.write(("\n".join(lines[i:i + BATCH]) + "\n").encode())


def save(path, lines):
    size = sum(len(l) + 1 for l in lines)       # bytes: graph6 strings are ASCII
    for p in (path, path + ".gz"):
        if os.path.exists(p):
            os.remove(p)
    if size > LIMIT:
        # mtime 0 in the gzip header, so that a rerun gives identical bytes
        with gzip.GzipFile(path + ".gz", "wb", compresslevel=9, mtime=0) as f:
            write_lines(f, lines)
        return os.path.basename(path) + ".gz"
    if lines:
        with open(path, "wb") as f:
            write_lines(f, lines)
        return os.path.basename(path)
    return None


def main():
    n, info, db = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    elapsed = float(sys.argv[4]) if len(sys.argv) > 4 else None
    A, B, MX = [], [], []
    total = 0
    types = {}
    with open(info) as f:
        for line in f:
            s, r, d, k = line.split()
            r, d, k = int(r), int(d), int(k)
            total += 1
            t = lattice_type(r, d)
            types[t] = types.get(t, 0) + 1
            if t in ("E6", "E7", "E8"):
                (A if r < n else B).append(s)
                if k == 0:
                    MX.append(s)
    assert A == sorted(A) and B == sorted(B)
    files = {}
    for sub, L in (("minus2", A), ("above-minus2", B), ("maximal", MX)):
        os.makedirs(os.path.join(db, sub), exist_ok=True)
        files[sub] = save(os.path.join(db, sub, f"n{n:02d}.g6"), L)
    cj = os.path.join(db, "counts.json")
    C = {"per_n": {}}
    if os.path.exists(cj):
        with open(cj) as f:
            C = json.load(f)
    C["per_n"][str(n)] = {
        "status": "complete",
        "minus2": len(A), "above_minus2": len(B), "maximal": len(MX),
        "connected_E8_represented": total,
        "lattice_types": dict(sorted(types.items())),
        "files": files,
        "growth_step_seconds": elapsed,
        "saved": time.strftime("%Y-%m-%d %H:%M:%S"),
    }
    C["per_n"] = dict(sorted(C["per_n"].items(), key=lambda kv: int(kv[0])))
    done = sorted(int(k) for k, v in C["per_n"].items() if v["status"] == "complete")
    C["complete_for_n"] = done
    C["totals_over_complete_n"] = {
        "minus2": sum(C["per_n"][str(m)]["minus2"] for m in done),
        "above_minus2": sum(C["per_n"][str(m)]["above_minus2"] for m in done),
        "maximal": sum(C["per_n"][str(m)]["maximal"] for m in done)}
    tmp = cj + ".tmp"
    with open(tmp, "w") as f:      # closed, hence flushed, before the rename
        json.dump(C, f, indent=1)
    os.replace(tmp, cj)
    print(f"n={n}: E8-represented {total}, (A) {len(A)}, (B) {len(B)}, maximal {len(MX)}, types {types}")


main()
