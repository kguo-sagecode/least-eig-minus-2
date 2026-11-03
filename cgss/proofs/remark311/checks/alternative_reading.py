"""Test the alternative reading of the matrix C in Remark 3.11: one actual root per line
(unequal lengths).  Then K = Gram matrix satisfies K^2 = tK with t = eigenvalue of the frame
sum over lines of r r^T.  We compare t with the value 2 + (printed constant)/1 that the
unit-vector reading (2G = 2I + C) predicts, i.e. we show that only the unit-vector reading
reproduces the printed constants 2(n-1), 10, 4."""
import sympy as s
from models import model, canonical_line


def frame_factor(kind, n, normalize):
    roots, base = model(kind, n)
    reps = {}
    for r in roots:
        reps.setdefault(canonical_line(r), r)
    dim = len(roots[0])
    T = s.zeros(dim)
    for r in reps.values():
        v = s.Matrix([s.Rational(x.numerator, x.denominator) for x in r])
        T += (v * v.T) / ((v.T * v)[0] if normalize else 1)
    a = s.Matrix.hstack(*(s.Matrix([s.Rational(x.numerator, x.denominator) for x in b]) for b in base))
    proj = a * (a.T * a).inv() * a.T
    # T = t * proj on the span
    col0 = a[:, 0]
    k0 = next(i for i in range(dim) if col0[i] != 0)
    t = (T * col0)[k0] / col0[k0]
    for k in range(a.cols):
        col = a[:, k]
        assert T * col == t * col, (kind, n, normalize)
    return t, len(reps)


if __name__ == "__main__":
    for kind, n, printed in [("B", 3, 4), ("B", 4, 6), ("B", 5, 8), ("C", 4, 6), ("F", 4, 10), ("G", 2, 4)]:
        t_unit, N = frame_factor(kind, n, True)
        t_raw, _ = frame_factor(kind, n, False)
        # unit reading: 2G = 2I + C, G^2 = t G  =>  theta = 2t - 2
        assert 2 * t_unit - 2 == printed
        expected_raw = {"B": 2*n-1, "C": 2*n+2, "F": 9, "G": 12}[kind]
        assert t_raw == expected_raw
        print(f"{kind}{n}: lines={N}, unit reading theta={2*t_unit-2} (printed {printed}); "
              f"actual-root Gram K has K^2 = {t_raw} K")
