"""Exact affine eigenvectors, leading determinants, and small-rank identifications."""
import sympy as s
from models import cartan


def check(edges, values):
    n = len(values)
    b = s.zeros(n)
    for i, j, w in edges:
        b[i, j] = b[j, i] = w
    v = s.Matrix(values)
    assert all(x > 0 for x in v)
    assert (b * v - 2 * v).applyfunc(s.simplify) == s.zeros(n, 1)
    assert (2 * s.eye(n) - b).rank() == n - 1


def arm_tree(arms, centre):
    edges, values = [], [s.Integer(centre)]
    for a in arms:
        prev = 0
        for t in range(1, a + 1):
            new = len(values)
            edges.append((prev, new, 1))
            values.append(s.Rational(centre * (a + 1 - t), a + 1))
            prev = new
    check(edges, values)


def exceptional_certificates():
    """Check the literal rational LDL^T certificates printed in Appendix A.2."""
    data = {
        "E": ([2, 2, s.Rational(3, 2), s.Rational(5, 6), s.Rational(4, 5),
               s.Rational(3, 4), s.Rational(2, 3), s.Rational(1, 2)],
              [(2, 0, -1, 2), (3, 1, -1, 2), (3, 2, -2, 3),
               (4, 3, -6, 5), (5, 4, -5, 4), (6, 5, -4, 3), (7, 6, -3, 2)]),
        "F": ([2, s.Rational(3, 2), s.Rational(4, 3), 1],
              [(1, 0, -1, 2), (2, 1, -4, 3), (3, 2, -3, 2)]),
        "G": ([2, s.Rational(3, 2)], [(1, 0, -3, 2)]),
    }
    for kind, n, d in [("E", 6, [1]*6), ("E", 7, [1]*7), ("E", 8, [1]*8),
                       ("F", 4, [1, 1, 2, 2]), ("G", 2, [1, 3])]:
        q, lower = data[kind]
        lower_matrix = s.eye(n)
        for i, j, numerator, denominator in lower:
            if i < n:
                lower_matrix[i, j] = s.Rational(numerator, denominator)
        assert all(v > 0 for v in q[:n])
        assert lower_matrix.det() == 1
        assert lower_matrix * s.diag(*q[:n]) * lower_matrix.T == s.diag(*d)*cartan(kind, n)
    print("All five exceptional rational LDL^T certificates passed by exact multiplication.")


if __name__ == "__main__":
    exceptional_certificates()
    r2, r3 = s.sqrt(2), s.sqrt(3)
    for n in range(3, 17):
        check([(i, (i + 1) % n, 1) for i in range(n)], [1] * n)
        check([(i, i + 1, r2 if i in (0, n - 2) else 1)
               for i in range(n - 1)], [1] + [r2]*(n - 2) + [1])
    check([(0, i, 1) for i in range(1, 5)], [2, 1, 1, 1, 1])
    for ell in range(5, 17):
        k = ell - 3  # number of vertices on the path between the forks
        edges = [(i, i + 1, 1) for i in range(k - 1)]
        edges += [(0, k, 1), (0, k + 1, 1), (k - 1, k + 2, 1), (k - 1, k + 3, 1)]
        check(edges, [2]*k + [1]*4)
    for k in range(1, 17):
        edges = [(0, k + 1, 1), (0, k + 2, 1)]
        edges += [(i, i + 1, r2 if i == k - 1 else 1) for i in range(k)]
        check(edges, [2]*k + [r2, 1, 1])
    for arms, centre in [((2, 2, 2), 3), ((1, 3, 3), 4), ((1, 2, 5), 6)]:
        arm_tree(arms, centre)
    check([(0, 1, 1), (1, 2, 1), (2, 3, r2), (3, 4, 1)], [1, 2, 3, 2*r2, r2])
    check([(0, 1, r3), (1, 2, 1)], [r3, 2, 1])
    print("All affine eigenvectors and one-dimensional kernels passed (families through parameter 16).")
    # Symbolic local identities for arbitrary arms and chains.
    a, t, c = s.symbols("a t c", positive=True)
    f = lambda j: c * (a + 1 - j) / (a + 1)
    assert s.simplify(f(t-1) + f(t+1) - 2*f(t)) == 0
    assert s.simplify(f(a-1) - 2*f(a)) == 0
    for kind, ranks in [("A", range(1, 17)), ("B", range(2, 17)),
                        ("C", range(2, 17)), ("D", range(4, 17)),
                        ("E", (6, 7, 8)), ("F", (4,)), ("G", (2,))]:
        for n in ranks:
            m = cartan(kind, n)
            d = [1] * n
            if kind == "B": d[-1] = 2
            if kind == "C": d = [2]*(n-1) + [1]
            if kind == "F": d = [1, 1, 2, 2]
            if kind == "G": d = [1, 3]
            h = s.diag(*d) * m
            assert h == h.T
            minors = [m[:k, :k].det() for k in range(1, n+1)]
            if kind == "A": expected = list(range(2, n+2))
            if kind in ("B", "C"): expected = list(range(2, n+1)) + [2]
            if kind == "D": expected = list(range(2, n+1)) + [4]
            if kind == "E": expected = [2, 4, 6, 5, 4, 3, 2, 1][:n]
            if kind == "F": expected = [2, 3, 2, 1]
            if kind == "G": expected = [2, 1]
            assert minors == expected, (kind, n, minors)
            assert all(v > 0 for v in minors)
            # General leaf expansion, including every D and E leaf; the
            # neighbour need not be the preceding matrix index.
            for leaf in range(n):
                neighbours = [j for j in range(n) if j != leaf and m[leaf, j] != 0]
                if len(neighbours) != 1:
                    continue
                neighbour = neighbours[0]
                keep = [i for i in range(n) if i != leaf]
                keep_both = [i for i in keep if i != neighbour]
                edge_product = m[leaf, neighbour]*m[neighbour, leaf]
                assert m.det() == (2*m.extract(keep, keep).det()
                                   - edge_product*m.extract(keep_both, keep_both).det())
    for kind in "ABCDE":
        assert cartan(kind, 0).shape == (0, 0)
        assert cartan(kind, 1) == s.Matrix([[2]])
    for kind in "DE": assert cartan(kind, 2) == 2*s.eye(2)
    assert cartan("B", 2)[[1, 0], [1, 0]] == cartan("C", 2)
    assert cartan("D", 3)[[1, 0, 2], [1, 0, 2]] == cartan("A", 3)
    assert cartan("E", 3)[[0, 2, 1], [0, 2, 1]] == s.diag(cartan("A", 2), s.Matrix([[2]]))
    assert cartan("E", 4)[[0, 2, 3, 1], [0, 2, 3, 1]] == cartan("A", 4)
    assert cartan("E", 5)[[0, 2, 3, 1, 4], [0, 2, 3, 1, 4]] == cartan("D", 5)
    assert cartan("E", 9).det() == 0
    print("All determinant formulas, symmetrizers and small-rank identifications passed.")
