"""Exact checks for the coordinate data in remark311.tex.

Run with python3 checks/models.py from cgss/proofs/remark311; requires SymPy.
These checks are independent sanity checks, not proofs used by the manuscript.
All root arithmetic uses fractions; all matrix arithmetic uses SymPy rationals.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from collections import Counter
import sympy as s


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def vec(n, entries):
    x = [Q(0)] * n
    for i, a in entries:
        x[i] += Q(a)
    return tuple(x)


def pairs(n):
    return {vec(n, [(i, a), (j, b)]) for i, j in combinations(range(n), 2)
            for a, b in product((-1, 1), repeat=2)}


def cartan(kind, n):
    m = 2 * s.eye(n)
    if kind in ("A", "B", "C"):
        for i in range(n - 1):
            m[i, i + 1] = m[i + 1, i] = -1
        if n >= 2 and kind == "B":
            m[n - 2, n - 1] = -2
        if n >= 2 and kind == "C":
            m[n - 1, n - 2] = -2
    elif kind == "D":
        if n > 2:
            for i in range(n - 3):
                m[i, i + 1] = m[i + 1, i] = -1
            for j in (n - 2, n - 1):
                m[n - 3, j] = m[j, n - 3] = -1
    elif kind == "E":
        for i, j in [(0, 2), (1, 3)] + [(i, i + 1) for i in range(2, n - 1)]:
            if i < n and j < n:
                m[i, j] = m[j, i] = -1
    elif kind == "F":
        m = s.Matrix([[2, -1, 0, 0], [-1, 2, -2, 0],
                      [0, -1, 2, -1], [0, 0, -1, 2]])
    elif kind == "G":
        m = s.Matrix([[2, -3], [-1, 2]])
    else:
        raise ValueError(kind)
    return m


def model(kind, n):
    if kind == "A":
        roots = {vec(n + 1, [(i, 1), (j, -1)])
                 for i in range(n + 1) for j in range(n + 1) if i != j}
        base = [vec(n + 1, [(i, 1), (i + 1, -1)]) for i in range(n)]
    elif kind in ("B", "C", "D"):
        roots = pairs(n)
        if kind != "D":
            a = 1 if kind == "B" else 2
            roots |= {vec(n, [(i, a * sign)]) for i in range(n) for sign in (-1, 1)}
        base = [vec(n, [(i, 1), (i + 1, -1)]) for i in range(n - 1)]
        base.append(vec(n, [(n - 1, 1)]) if kind == "B" else
                    vec(n, [(n - 1, 2)]) if kind == "C" else
                    vec(n, [(n - 2, 1), (n - 1, 1)]))
    elif kind == "E":
        roots = pairs(8) | {tuple(Q(a, 2) for a in signs)
                           for signs in product((-1, 1), repeat=8)
                           if signs.count(-1) % 2 == 0}
        base = [tuple(Q(a, 2) for a in (1, -1, -1, -1, -1, -1, -1, 1)),
                vec(8, [(0, 1), (1, 1)])]
        base += [vec(8, [(i, 1), (i - 1, -1)]) for i in range(1, 7)]
        base = base[:n]
        if n == 7:
            roots = {x for x in roots if x[6] + x[7] == 0}
        if n == 6:
            roots = {x for x in roots if x[5] == x[6] == -x[7]}
    elif kind == "F":
        roots = pairs(4) | {vec(4, [(i, a)]) for i in range(4) for a in (-1, 1)}
        roots |= {tuple(Q(a, 2) for a in signs) for signs in product((-1, 1), repeat=4)}
        base = [vec(4, [(1, 1), (2, -1)]), vec(4, [(2, 1), (3, -1)]),
                vec(4, [(3, 1)]), tuple(Q(a, 2) for a in (1, -1, -1, -1))]
    elif kind == "G":
        roots = {vec(3, [(i, 1), (j, -1)]) for i in range(3) for j in range(3) if i != j}
        roots |= {tuple(Q(sign * (2 if k == i else -1)) for k in range(3))
                  for i in range(3) for sign in (-1, 1)}
        base = [vec(3, [(0, 1), (1, -2), (2, 1)]), vec(3, [(1, 1), (2, -1)])]
    else:
        raise ValueError(kind)
    return sorted(roots), base


def canonical_line(x):
    first = next(a for a in x if a)
    return tuple(a / first for a in x)


def check(kind, n):
    roots, base = model(kind, n)
    rootset = set(roots)
    assert len(base) == n and set(base) <= rootset
    lengths = {x: dot(x, x) for x in roots}
    assert all(q > 0 for q in lengths.values())
    lines = {canonical_line(x) for x in roots}
    assert len(roots) == 2 * len(lines)
    assert all(tuple(-a for a in x) in rootset for x in roots)
    angles = set()
    for r in roots:
        for t in roots:
            c = 2 * dot(r, t) / lengths[r]
            assert c.denominator == 1, (kind, n, r, t, c)
            reflected = tuple(tj - c * rj for rj, tj in zip(r, t))
            assert reflected in rootset, (kind, n, r, t, reflected)
            angle = dot(r, t) ** 2 / (lengths[r] * lengths[t])
            if angle != 1:
                angles.add(angle)
    a = s.Matrix.hstack(*(s.Matrix(x) for x in base))
    gram = a.T * a
    expected_gram_det = {"A": n+1, "B": 1, "C": 4, "D": 4,
                         "E": 9-n, "F": Q(1, 4), "G": 3}[kind]
    assert gram.det() == expected_gram_det
    m = s.Matrix(n, n, lambda i, j: 2 * gram[i, j] / gram[j, j])
    assert m == cartan(kind, n), (kind, n, m)
    coeffs = gram.inv() * a.T * s.Matrix.hstack(*(s.Matrix(x) for x in roots))
    assert a * coeffs == s.Matrix.hstack(*(s.Matrix(x) for x in roots))
    for col in coeffs.columnspace():
        # The full column-by-column assertion follows below; columnspace is also exact.
        assert all(v.q == 1 for v in col)
    for j in range(coeffs.cols):
        col = list(coeffs[:, j])
        assert all(v.q == 1 for v in col)
        assert all(v >= 0 for v in col) or all(v <= 0 for v in col)
    dimension = len(roots[0])
    frame = s.zeros(dimension)
    for x in roots:
        col = s.Matrix(x)
        frame += col * col.T / (2 * lengths[x])
    projector = a * gram.inv() * a.T
    assert frame == Q(len(lines), n) * projector
    expected_count = {"A": n * (n + 1), "B": 2*n*n, "C": 2*n*n,
                      "D": 2*n*(n-1), "E": {6: 72, 7: 126, 8: 240}.get(n),
                      "F": 48, "G": 12}[kind]
    assert len(roots) == expected_count
    if kind in ("A", "D", "E"):
        expected_lengths = {Q(2): len(roots)}
        expected_angles = set() if n == 1 else {Q(1, 4)} if kind == "A" and n == 2 else {Q(0), Q(1, 4)}
    elif kind == "B":
        expected_lengths = {Q(1): 2*n, Q(2): 2*n*(n-1)}
        expected_angles = {Q(0), Q(1, 2)} | ({Q(1, 4)} if n >= 3 else set())
    elif kind == "C":
        expected_lengths = {Q(2): 2*n*(n-1), Q(4): 2*n}
        expected_angles = {Q(0), Q(1, 2)} | ({Q(1, 4)} if n >= 3 else set())
    elif kind == "F":
        expected_lengths = {Q(1): 24, Q(2): 24}
        expected_angles = {Q(0), Q(1, 4), Q(1, 2)}
    else:
        expected_lengths = {Q(2): 6, Q(6): 6}
        expected_angles = {Q(0), Q(1, 4), Q(3, 4)}
    assert Counter(lengths.values()) == expected_lengths
    assert angles == expected_angles
    print(f"{kind}{n}: roots={len(roots)}, lines={len(lines)}, "
          f"length_counts={dict(sorted(Counter(lengths.values()).items()))}, "
          f"det_Gram={gram.det()}, angles_cos2={sorted(angles)}, frame={Q(len(lines), n)}")


if __name__ == "__main__":
    for kind, ranks in [("A", range(1, 9)), ("B", range(2, 9)),
                        ("C", range(2, 9)), ("D", range(4, 9)),
                        ("E", (6, 7, 8)), ("F", (4,)), ("G", (2,))]:
        for n in ranks:
            check(kind, n)
    for n in range(2, 9):
        assert {canonical_line(x) for x in model("B", n)[0]} == {
            canonical_line(x) for x in model("C", n)[0]}
    t = s.Matrix([[1, 1], [-1, 1]])
    assert {tuple(t*s.Matrix(x)) for x in model("B", 2)[0]} == set(model("C", 2)[0])
    assert t.T * t == 2 * s.eye(2)
    print("All exact model checks passed, including B/C line equality and the B2/C2 similarity.")
