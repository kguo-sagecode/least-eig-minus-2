"""Literal transcription of the Mathlib definitions in
Mathlib/LinearAlgebra/Matrix/Cartan.lean from the pinned Lake dependency, written directly from the
`if` conditions in the Lean source, independently of checks/models.py.

Requires Python 3 with SymPy. We first compare the literal defining
bodies with the read-only Mathlib source, ignoring whitespace only. We then compare
the independent Python transcription with checks/models.py for ranks 0 through 16,
the index formulas of Section 6, and the identities of Remark 6.1. This is a source
comparison and a Python sanity check, not a Lean proof or Lean evaluation.

By default, read .lake/packages/mathlib under the repository root. Pass
--mathlib PATH to use a different Mathlib checkout.
"""
from pathlib import Path
import argparse
import hashlib
import re
import sympy as s
from models import cartan


def verify_source(mathlib):
    source_path = mathlib / "Mathlib/LinearAlgebra/Matrix/Cartan.lean"
    if not source_path.is_file():
        raise SystemExit(
            f"Mathlib source not found: {source_path}. "
            "Run `lake exe cache get` in the repository root, "
            "or pass --mathlib PATH to a Mathlib checkout."
        )
    source = source_path.read_text()
    bodies = {
        "A": """Matrix.of fun i j =>
            if i = j then 2
            else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
            else 0""",
        "B": """Matrix.of fun i j =>
            if i = j then 2
            else if i.val + 1 = j.val then
              if j.val = n - 1 then -2 else -1
            else if j.val + 1 = i.val then -1
            else 0""",
        "C": """Matrix.of fun i j =>
            if i = j then 2
            else if i.val + 1 = j.val then -1
            else if j.val + 1 = i.val then
              if i.val = n - 1 then -2 else -1
            else 0""",
        "D": """Matrix.of fun i j =>
            if i = j then 2
            else if n ≤ 2 then 0
            else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
            else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
            else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
            else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
            else 0""",
        "E": """.of fun i j =>
            if i = j then 2
            else if (i.val = 0 ∧ j.val = 2) ∨ (j.val = 0 ∧ i.val = 2) ∨
              (i.val = 1 ∧ j.val = 3) ∨ (j.val = 1 ∧ i.val = 3) ∨
              (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)
            then -1 else 0""",
        "F₄": """!![ 2, -1,  0,  0;
                         -1,  2, -2,  0;
                          0, -1,  2, -1;
                          0,  0, -1,  2]""",
        "G₂": """!![ 2, -3;
                         -1,  2]""",
    }
    for name, expected in bodies.items():
        match = re.search(r"^def " + re.escape(name) + r"\s[^\n]*:=\n(.*?)(?=\n\n)",
                          source, flags=re.M | re.S)
        assert match, (source_path, name)
        normalize = lambda value: re.sub(r"\s+", "", value)
        assert normalize(match[1]) == normalize(expected), (source_path, name, "source changed")
    print(f"All seven defining bodies match {source_path} (whitespace ignored).")
    print("Source SHA256:", hashlib.sha256(source.encode()).hexdigest())


def A(n):
    return s.Matrix(n, n, lambda i, j: 2 if i == j else (-1 if (i + 1 == j or j + 1 == i) else 0))


def B(n):
    def f(i, j):
        if i == j: return 2
        if i + 1 == j: return -2 if j == n - 1 else -1
        if j + 1 == i: return -1
        return 0
    return s.Matrix(n, n, f)


def C(n):
    def f(i, j):
        if i == j: return 2
        if i + 1 == j: return -1
        if j + 1 == i: return -2 if i == n - 1 else -1
        return 0
    return s.Matrix(n, n, f)


def D(n):
    def f(i, j):
        if i == j: return 2
        if n <= 2: return 0
        if i + 1 == j and j + 2 < n: return -1
        if j + 1 == i and i + 2 < n: return -1
        if i + 3 == n and (j + 2 == n or j + 1 == n): return -1
        if j + 3 == n and (i + 2 == n or i + 1 == n): return -1
        return 0
    return s.Matrix(n, n, f)


def E(n):
    def f(i, j):
        if i == j: return 2
        if ((i == 0 and j == 2) or (j == 0 and i == 2) or (i == 1 and j == 3) or (j == 1 and i == 3)
                or (2 <= i and i + 1 == j) or (2 <= j and j + 1 == i)):
            return -1
        return 0
    return s.Matrix(n, n, f)


F4 = s.Matrix([[2, -1, 0, 0], [-1, 2, -2, 0], [0, -1, 2, -1], [0, 0, -1, 2]])
G2 = s.Matrix([[2, -3], [-1, 2]])


def from_edges(n, edges):
    m = 2 * s.eye(n)
    for i, j, a, b in edges:
        m[i, j], m[j, i] = a, b
    return m


def doc_formula(kind, l):
    """Section 6 of remark311.tex, before the proof of Theorem A."""
    path = [(i, i + 1, -1, -1) for i in range(l - 1)]
    if kind == "A":
        return from_edges(l, path)
    if kind == "B":
        return from_edges(l, path[:-1] + [(l - 2, l - 1, -2, -1)])
    if kind == "C":
        return from_edges(l, path[:-1] + [(l - 2, l - 1, -1, -2)])
    if kind == "D":
        return from_edges(l, [(i, i + 1, -1, -1) for i in range(0, l - 2)] + [(l - 3, l - 1, -1, -1)])
    if kind == "E":
        return from_edges(l, [(0, 2, -1, -1), (1, 3, -1, -1)] + [(i, i + 1, -1, -1) for i in range(2, l - 1)])


def perm(m, order):
    """New index k corresponds to old index order[k]."""
    return m.extract(order, order)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mathlib", type=Path,
        default=Path(__file__).resolve().parents[4] / ".lake/packages/mathlib",
        help="Mathlib checkout (default: repository .lake/packages/mathlib)",
    )
    verify_source(parser.parse_args().mathlib)
    for kind, literal in [("A", A), ("B", B), ("C", C), ("D", D), ("E", E)]:
        for n in range(17):
            assert cartan(kind, n) == literal(n), (kind, n)
    assert cartan("F", 4) == F4 and cartan("G", 2) == G2
    for l in range(2, 15):
        assert doc_formula("A", l) == A(l)
        assert doc_formula("B", l) == B(l), l
        assert doc_formula("C", l) == C(l), l
        assert B(l).T == C(l)
    for l in range(3, 15):
        assert doc_formula("D", l) == D(l), l
    for l in range(4, 15):
        assert doc_formula("E", l) == E(l), l
    # Remark 6.1 (rem:small)
    for M in (B, C, D, E):
        assert M(1) == A(1) == s.Matrix([[2]])
    assert D(2) == 2 * s.eye(2) and E(2) == 2 * s.eye(2)
    assert perm(B(2), [1, 0]) == C(2)
    assert perm(D(3), [1, 0, 2]) == A(3)
    assert perm(E(3), [0, 2, 1]) == s.diag(A(2), A(1))
    assert perm(E(4), [0, 2, 3, 1]) == A(4)
    assert perm(E(5), [0, 2, 3, 1, 4]) == D(5)
    # Mathlib's own literal lemmas
    assert D(4) == s.Matrix([[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]])
    assert E(6)[3, :] == s.Matrix([[0, -1, -1, 2, -1, 0]])
    # Mathlib's E_det: det (E n) = 9 - n for n >= 3
    for l in range(3, 15):
        assert E(l).det() == 9 - l, l
    # F4 orientation: reversing the path interchanges the orientation
    rev = perm(F4, [3, 2, 1, 0])
    assert rev[1, 2] == -1 and rev[2, 1] == -2
    print("Literal Mathlib transcription agrees with models.cartan (0 <= n <= 16),")
    print("the Section 6 formulas (n <= 14), Remark 6.1 and E_det; F4 reversal checked.")
