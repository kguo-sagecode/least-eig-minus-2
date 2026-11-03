#!/usr/bin/env python3
"""Exact checks for sec5-hallconnor.tex; no search for a (15,5,2) design.

Run with python3; requires SymPy. The displayed certificates
are read from the TeX itself, so an independent copy cannot hide a typo.
The formula diagnostics re-evaluate displayed identities, not their derivations.
The graph control cannot test the existence of an integral incidence matrix.
"""

from itertools import combinations, product
from math import isqrt
from pathlib import Path
import re
import sys

import sympy as sp

from check_t7 import check_triangular_graph

HERE = Path(__file__).resolve().parent
SOURCE = (HERE.parents[1] / "sec5-hallconnor.tex").read_text()


def displayed_matrix(name):
    section = re.search(
        rf"% BEGIN MATRIX {name}\n(.*?)% END MATRIX {name}",
        SOURCE, re.DOTALL,
    )
    assert section, name
    body = re.search(
        r"\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}",
        section.group(1), re.DOTALL,
    ).group(1)
    rows = [row.strip() for row in body.split(r"\\") if row.strip()]
    return sp.Matrix([[int(x.strip()) for x in row.split("&")] for row in rows])


def symmetric_from_upper(rows):
    n = len(rows)
    assert [len(row) for row in rows] == list(range(n, 0, -1))
    return sp.Matrix(n, n, lambda i, j: rows[min(i, j)][abs(i - j)])


def characteristic(intersections, k=5):
    n = intersections.rows
    assert intersections == intersections.T
    assert all(intersections[i, j] in (1, 2)
               for i in range(n) for j in range(n) if i != j)
    return sp.Matrix(n, n, lambda i, j:
                     2*k if i == j else k-2 if intersections[i, j] == 1 else -4)


def seven_pattern(j):
    assert 0 <= j <= 2
    q = sp.zeros(7)
    for i in range(7):
        q[i, i] = 10
    def put(i, h, value):
        q[i, h] = q[h, i] = value
    for i, h in combinations(range(3), 2):
        put(i, h, 3)
    u = list(range(3, 3+j))
    v = list(range(3+j, 7))
    for i in u:
        for h, value in enumerate([3, -4, -4]):
            put(h, i, value)
    for i in v:
        for h, value in enumerate([-4, 3, 3]):
            put(h, i, value)
    for group in (u, v):
        for i, h in combinations(group, 2):
            put(i, h, 3)
    for i in u:
        for h in v:
            put(i, h, -4)
    return q


def check_counts_and_algebra():
    assert [(i-1)*(i-2) for i in range(6)] == [2, 0, 0, 2, 6, 12]
    assert 20 - 2*30 + 2*20 == 0
    for s, expected in [(1, (5, 4, 4, 6)), (2, (4, 6, 6, 3))]:
        x22 = (50-5*s) - 2*(30-s) + 19
        x12 = (30-s) - 19 - x22
        x11 = 19 - 2*x12 - x22
        assert (x11, x12, x12, x22) == expected
    # Multiplication table on the span of I,G,J:
    # G^2=5G+50J, GJ=35J, J^2=21J.
    basis_products = {
        (0, 0): sp.Matrix([1, 0, 0]),
        (0, 1): sp.Matrix([0, 1, 0]),
        (0, 2): sp.Matrix([0, 0, 1]),
        (1, 1): sp.Matrix([0, 5, 50]),
        (1, 2): sp.Matrix([0, 0, 35]),
        (2, 2): sp.Matrix([0, 0, 21]),
    }
    coeffs = sp.Matrix([35, -7, 10])
    square = sp.zeros(3, 1)
    for i, j in product(range(3), repeat=2):
        square += coeffs[i]*coeffs[j]*basis_products[tuple(sorted((i, j)))]
    assert square == 35*coeffs
    assert 35*sp.Matrix([1, 0]) - 7*sp.Matrix([5, 10]) + 10*sp.Matrix([0, 7]) == sp.zeros(2, 1)
    assert 30 - 3*30 + 4*15 == 0
    print("PASS: moment counts, both common-neighbour tables, C^2=35C, CN^T=0")


def check_local_certificates():
    claw = displayed_matrix("claw")
    five = displayed_matrix("five")
    x = sp.Matrix([-1, 1, 1, 1])
    y = sp.Matrix([-1, 1, 1, 1, -1])
    assert (x.T*claw*x)[0] == -2
    assert (y.T*five*y)[0] == -4
    source_patterns = [
        symmetric_from_upper([[5, 1, 1, 1, 1, 2], [5, 1, 2, 2, 1],
                              [5, 2, 2, 1], [5, 2, 2], [5, 2], [5]]),
        symmetric_from_upper([[5, 1, 1, 2, 2], [5, 1, 1, 1],
                              [5, 1, 1], [5, 2], [5]]),
        symmetric_from_upper([[5, 1, 1, 1, 2], [5, 1, 2, 1],
                              [5, 2, 1], [5, 1], [5]]),
    ]
    bad = [characteristic(s) for s in source_patterns]
    assert bad[0].extract([0, 1, 3, 4], [0, 1, 3, 4]) == claw
    assert bad[1].extract([1, 0, 3, 4], [1, 0, 3, 4]) == claw
    assert bad[2] == five
    assert [m.det() for m in bad] == [-268912, -38416, -28812]
    print("PASS: displayed quadratic certificates -2, -4; source Lemmas 4.3-4.5")
    for j in (1, 2):
        q = displayed_matrix(f"Q{j}")
        k = displayed_matrix(f"K{j}")
        assert q == seven_pattern(j)
        assert k*q == q*k == 14*sp.eye(7)
        assert q.det() == 2*7**6 == 235298
        # Sylvester's criterion confirms why nonnegativity cannot exclude these.
        assert all(q[:i, :i].det() > 0 for i in range(1, 8))
        print(f"PASS: Q{j}, all 49 entries of K{j}Q{j}=14I; det=235298; positive definite")
    q0 = seven_pattern(0)
    assert q0.det() == 0 and q0.rank() == 6
    print("PASS: j=0 matrix has determinant zero and rank six")


def biplane_controls():
    # Residual sizes k=3,4 do not exercise the structural argument at k=5.
    d11 = {1, 3, 4, 5, 9}
    p11 = list(range(11))
    b11 = [frozenset((d+g) % 11 for d in d11) for g in p11]
    p16 = list(product((0, 1), repeat=4))
    d16 = [(0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0),
           (0, 0, 1, 0), (0, 0, 0, 1), (1, 1, 1, 1)]
    b16 = [frozenset(tuple((x+y) % 2 for x, y in zip(d, g)) for d in d16)
           for g in p16]
    for points, blocks in [(p11, b11), (p16, b16)]:
        size = len(blocks[0])
        full = sp.Matrix([[int(p in b) for b in blocks] for p in points])
        assert full*full.T == (size-2)*sp.eye(len(points)) + 2*sp.ones(len(points))
        residual_points = [p for p in points if p not in blocks[0]]
        residual_blocks = [b-blocks[0] for b in blocks[1:]]
        n = sp.Matrix([[int(p in b) for b in residual_blocks] for p in residual_points])
        v, b = n.shape
        k, r = size-2, size
        assert n*sp.ones(b, 1) == r*sp.ones(v, 1)
        assert n.T*sp.ones(v, 1) == k*sp.ones(b, 1)
        assert n*n.T == (r-2)*sp.eye(v) + 2*sp.ones(v)
        s = n.T*n
        c = r*(r-2)*sp.eye(b) - r*s + 2*k*sp.ones(b)
        assert c == characteristic(s, k)
        assert c*c == r*(r-2)*c and c*n.T == sp.zeros(b, v)
        assert c.rank() == b-v
        cliques = [q for q in combinations(range(b), k+1)
                   if all(s[i, j] == 1 for i, j in combinations(q, 2))]
        t = sp.Matrix(b, len(cliques), lambda i, j: int(i in cliques[j]))
        assert len(cliques) == k+2
        assert t*sp.ones(k+2, 1) == 2*sp.ones(b, 1)
        assert n*t == 2*sp.ones(v, k+2)
        assert t.T*t == k*sp.eye(k+2) + sp.ones(k+2)
        extended = n.row_join(sp.zeros(v, 1)).col_join(t.T.row_join(sp.ones(k+2, 1)))
        assert extended.rows == extended.cols == len(points)
        assert extended*extended.T == k*sp.eye(len(points)) + 2*sp.ones(len(points))
        print(f"PASS: ({len(points)},{size},2) biplane residual and reconstruction, all exact")


def check_obstruction():
    s, t = sp.symbols("s t")
    for n in range(1, 6):
        assert sp.expand((s*sp.eye(n)+t*sp.ones(n)).det() - s**(n-1)*(s+n*t)) == 0
    assert (5*sp.eye(15)+2*sp.ones(15)).det() == 35*5**14 != 0
    value = 49*5**21
    assert (5*sp.eye(22)+2*sp.ones(22)).det() == value == 23365020751953125
    assert {d*d % 5 for d in range(5)} == {0, 1, 4}
    assert all((d*d % 5 == 0) == (d % 5 == 0) for d in range(5))
    root = isqrt(value)
    assert root**2 < value < (root+1)**2
    exponent, remaining = 0, value
    while remaining % 5 == 0:
        exponent += 1
        remaining //= 5
    assert (exponent, remaining) == (21, 49)
    print(f"PASS: determinant {value}; 5-adic exponent 21; integer square root bound {root}")


if __name__ == "__main__":
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}; exact arithmetic")
    check_counts_and_algebra()
    check_local_certificates()
    check_triangular_graph()
    biplane_controls()
    check_obstruction()
    print("ALL CHECKS PASSED. These checks supplement the written proof.")
    print("LIMIT: formulas are diagnostics; controls do not prove the quantified argument")
    print("or supply the excluded design's integral incidence matrix.")
