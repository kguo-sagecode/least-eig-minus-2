import Mathlib.Tactic

/-!
# Computation C14 for [CGSS], Remark 5.12

The finite `t = 2` case and the unrestricted lower bound for `t ≥ 3`.
The oddness of `s` when `t = 1` and finiteness of the possible `s` at fixed `t > 1`
are not packaged as separate lemmas here.
-/

namespace Computations.C14

/-- C14, [CGSS] Remark 5.12, `s5512lam`: isolate the positive remainder. -/
theorem lambda_remainder (s t lam : ℤ)
    (h : lam * (s - 1) = 2 * t * (s * t - 1)) :
    (lam - 2 * t ^ 2) * (s - 1) = 2 * t * (t - 1) := by
  linear_combination h

/-- C14, [CGSS] Remark 5.12, `s5512t1`: the case `t = 1`. -/
theorem lambda_eq_two (s lam : ℤ) (hs : 2 ≤ s)
    (h : lam * (s - 1) = 2 * (s - 1)) : lam = 2 := by
  exact mul_right_cancel₀ (show s - 1 ≠ 0 by omega) h

/-- C14, [CGSS] Remark 5.12, `s5512s`: the exhaustive case `t = 2`. -/
theorem eq_three_or_five (s : ℤ) (hs : 3 ≤ s) (h : (s - 1) ∣ 4) : s = 3 ∨ s = 5 := by
  have hle : s - 1 ≤ 4 := Int.le_of_dvd (by norm_num) h
  have hupper : s ≤ 5 := by omega
  interval_cases s <;> norm_num at *

/-- C14, [CGSS] Remark 5.12, `s5512t3`: a bound for all `t ≥ 3`, without a search cutoff. -/
theorem lambda_ge_nineteen (s t lam : ℤ) (hs : 2 ≤ s) (ht : 3 ≤ t)
    (h : lam * (s - 1) = 2 * t * (s * t - 1)) : 19 ≤ lam := by
  have hr := lambda_remainder s t lam h
  have hp : 0 < 2 * t * (t - 1) := by
    have : 0 < t - 1 := by omega
    positivity
  have hlt : 2 * t ^ 2 < lam := by
    by_contra hn
    have hz : (lam - 2 * t ^ 2) * (s - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    omega
  nlinarith [sq_nonneg (t - 3)]

/-- C14, [CGSS] Remark 5.12: the lower bound is attained at `(s,t,λ) = (13,3,19)`. -/
theorem nineteen_sharp : (19 : ℤ) * (13 - 1) = 2 * 3 * (13 * 3 - 1) := by decide

/-- C14, [CGSS] Remark 5.12, `s5512s3` and `s5512s5`: the remaining parameter tuples. -/
theorem t2_parameters :
    ((3 * (3 + 1) / 2, 3 * 2, (3 + 1) * (3 + 2) / 2, (3 + 2) * 2,
      2 * 2 * (3 * 2 - 1) / (3 - 1)) : ℚ × ℚ × ℚ × ℚ × ℚ) = (6, 6, 10, 10, 10) ∧
    ((5 * (5 + 1) / 2, 5 * 2, (5 + 1) * (5 + 2) / 2, (5 + 2) * 2,
      2 * 2 * (5 * 2 - 1) / (5 - 1)) : ℚ × ℚ × ℚ × ℚ × ℚ) = (15, 10, 21, 14, 9) := by
  norm_num

end Computations.C14
