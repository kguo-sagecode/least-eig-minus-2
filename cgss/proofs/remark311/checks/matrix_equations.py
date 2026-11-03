"""Direct check of the matrix equations of Theorem C and of Theorem 3.7 with the convention
C = 2G - 2I, G the Gram matrix of unit vectors on the lines (random signs), computed exactly
in sympy.  checks/models.py only checks the equivalent frame identity."""
import random
import sympy as s
from models import model, canonical_line


def unit_gram(kind, n, seed):
    roots, _ = model(kind, n)
    reps = {}
    for r in roots:
        reps.setdefault(canonical_line(r), r)
    rng = random.Random(seed)
    vecs = []
    for r in reps.values():
        sign = rng.choice((1, -1))
        v = s.Matrix([sign * s.Rational(x.numerator, x.denominator) for x in r])
        vecs.append(v / s.sqrt((v.T * v)[0]))
    U = s.Matrix.hstack(*vecs)
    return U.T * U, len(vecs)


def check(kind, n, theta, seed=0):
    G, N = unit_gram(kind, n, seed)
    C = 2 * G - 2 * s.eye(N)
    P = ((C + 2 * s.eye(N)) * (C - theta * s.eye(N))).applyfunc(s.simplify)
    assert P == s.zeros(N), (kind, n)
    return N


if __name__ == "__main__":
    for n in range(2, 6):
        assert check("B", n, 2 * (n - 1), seed=n) == n * n
        assert check("C", n, 2 * (n - 1), seed=10 + n) == n * n
    assert check("F", 4, 10, seed=3) == 24
    assert check("G", 2, 4, seed=4) == 6
    for n in range(1, 6):
        check("A", n, n - 1, seed=n)
    for n in range(4, 7):
        check("D", n, 2 * (n - 2), seed=n)
    check("E", 6, 10); check("E", 7, 16)
    N = check("E", 8, 28)
    # the printed 18 fails for E8
    G, N = unit_gram("E", 8, 0)
    C = 2 * G - 2 * s.eye(N)
    residual = ((C + 2 * s.eye(N)) * (C - 18 * s.eye(N))).applyfunc(s.simplify)
    assert residual == 20*G and residual != s.zeros(N)
    print("Theorem C equations (B_n, C_n for n<=5, F4, G2) and Theorem 3.7 equations")
    print("(A_n n<=5, D_n n<=6, E6, E7, E8 with 28; 18 fails) hold exactly with C = 2G - 2I.")
