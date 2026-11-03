"""Symbolic coefficient inverses and small algebraic identities in the appendix."""
import sympy as s
from models import model


if __name__ == "__main__":
    x = s.Matrix(s.symbols("x1:9"))
    a = s.Matrix.hstack(*(s.Matrix(v) for v in model("E", 8)[1]))
    c = [2*x[7], sum(x)/2 + 2*x[7]]
    c.append(c[1] + x[7] - x[0])
    c += [sum(x[k-1:7]) + (8-k)*x[7] for k in range(3, 8)]
    assert (a*s.Matrix(c)-x).applyfunc(s.expand) == s.zeros(8, 1)
    assert s.expand(c[7] - x[6] - x[7]) == 0
    assert s.expand(c[6] - x[5] - x[6] - 2*x[7]) == 0
    a = s.Matrix.hstack(*(s.Matrix(v) for v in model("F", 4)[1]))
    c = [x[0]+x[1], 2*x[0]+x[1]+x[2],
         3*x[0]+x[1]+x[2]+x[3], 2*x[0]]
    assert (a*s.Matrix(c)-x[:4, :]).applyfunc(s.expand) == s.zeros(4, 1)
    n, k = s.symbols("n k", integer=True, positive=True)
    assert s.expand(2*k-(k-1)-(k+1)) == 0  # A recurrence
    assert s.expand(2*n-2*(n-1)-2) == 0  # B,C last minor
    assert s.expand(2*n-2*(n-2)-4) == 0  # D last minor
    assert s.expand(2*(9-(k-1))-(9-(k-2))-(9-k)) == 0  # E recurrence
    c = 1/s.sqrt(2)
    v = s.Matrix.hstack(s.Matrix([1, 0, 0]), s.Matrix([c, c, 0]),
                       s.Matrix([c, 1-c, s.sqrt(2*c-1)]))
    assert (v.T*v).applyfunc(s.simplify) == (1-c)*s.eye(3)+c*s.ones(3)
    assert v.det() > 0
    e1, e2 = s.Matrix([1, 0]), s.Matrix([0, 1])
    assert ((e1+e2)*(e1+e2).T+(e1-e2)*(e1-e2).T)/2 == s.eye(2)
    p = s.eye(3)-s.ones(3)/3
    short = s.zeros(3)
    long = s.zeros(3)
    for i in range(3):
        for j in range(i+1, 3):
            v = s.eye(3)[:, i]-s.eye(3)[:, j]
            short += v*v.T/2
        v = 3*s.eye(3)[:, i]-s.ones(3, 1)
        long += v*v.T/6
    assert short == long == 3*p/2
    assert p*p == p and p.T == p
    assert 2*s.Rational(120, 8)-2 == 28
    print("E and F coefficient inverses, scalar recurrence identities, the three-line example,")
    print("pairwise and G2 frame identities, and arithmetic 2*(120/8)-2=28 passed exactly.")
    print("Matrix determinants are checked in affine.py; matrix equations in matrix_equations.py.")
