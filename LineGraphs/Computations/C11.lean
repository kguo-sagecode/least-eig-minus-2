import Mathlib.Tactic

/-!
# Computation C11 for [CGSS], Theorem 5.8

Parameter identities for the nonbipartite alternative.
-/

namespace Computations.C11

/-- C11, [CGSS] Theorem 5.8, `s558nbt`: the positive half-difference is integral. -/
theorem exists_positive_half_difference (r k : ℤ) (h : k < r) (he : Even (r + k)) :
    ∃ t : ℤ, 1 ≤ t ∧ r = k + 2 * t := by
  obtain ⟨a, ha⟩ := he
  exact ⟨a - k, by omega, by omega⟩

/-- C11, [CGSS] Theorem 5.8, `s558nbv`: eliminate the block count. -/
theorem parameter_equation (v k b r : ℤ) (hbk : b * k = v * r)
    (hh : (r + k) * (v + b - 1) = 4 * v * r) :
    v * (r - k) ^ 2 = k * (r + k) := by
  linear_combination k * hh - (r + k) * hbk

/-- C11, [CGSS] Theorem 5.8: the rational formula for the number of points. -/
theorem points_eq (v k r : ℚ) (h : v * (r - k) ^ 2 = k * (r + k))
    (hrk : r ≠ k) : v = k * (r + k) / (r - k) ^ 2 := by
  apply (eq_div_iff (pow_ne_zero _ (sub_ne_zero.mpr hrk))).mpr
  exact h

/-- C11, [CGSS] Theorem 5.8, `s558nbtk`: substitute `r = k + 2t`. -/
theorem two_mul_sq_mul_points (v k r t : ℤ) (hr : r = k + 2 * t)
    (h : v * (r - k) ^ 2 = k * (r + k)) : 2 * t ^ 2 * v = k * (k + t) := by
  subst r
  nlinarith [h]

/-- C11, [CGSS] Theorem 5.8, `s558nbtk`: the difference of block and point counts. -/
theorem mul_blocks_sub_points (v k b r t : ℤ) (hk : k ≠ 0)
    (hr : r = k + 2 * t) (hbk : b * k = v * r)
    (hv : 2 * t ^ 2 * v = k * (k + t)) : t * (b - v) = k + t := by
  apply mul_left_cancel₀ hk
  linear_combination t * hbk + t * v * hr + hv

/-- C11, [CGSS] Theorem 5.8, `s558nbtk`: the integer `t` divides `k`. -/
theorem dvd_block_size (b v k t : ℤ) (h : t * (b - v) = k + t) : t ∣ k := by
  refine ⟨b - v - 1, ?_⟩
  linear_combination -h

/-- C11, [CGSS] Theorem 5.8, `s558nbparams`: all four parameter formulas. -/
theorem parameters (v k b r s t : ℤ) (ht : t ≠ 0) (hs : s ≠ 0)
    (hk : k = s * t) (hr : r = k + 2 * t)
    (hv : 2 * t ^ 2 * v = k * (k + t)) (hb : b * k = v * r) :
    2 * v = s * (s + 1) ∧ 2 * b = (s + 1) * (s + 2) ∧ r = (s + 2) * t := by
  subst k r
  have hpoint : 2 * v = s * (s + 1) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ht)
    linear_combination hv
  have hblock : 2 * b = (s + 1) * (s + 2) := by
    apply mul_left_cancel₀ (mul_ne_zero hs ht)
    linear_combination 2 * hb + (s + 2) * t * hpoint
  exact ⟨hpoint, hblock, by ring⟩

/-- C11, [CGSS] Theorem 5.8, `s558nbs`: more than one point forces `s ≥ 2`. -/
theorem two_le_parameter (v s : ℤ) (hv : 1 < v) (hs : 0 < s)
    (h : 2 * v = s * (s + 1)) : 2 ≤ s := by
  by_contra hlt
  have : s = 1 := by omega
  subst s
  omega

/-- C11, [CGSS] Theorem 5.8, `s558nblam`: the pair-count parameter identity. -/
theorem lambda_equation (v k r s t lam : ℤ) (hs : 2 ≤ s)
    (hv : 2 * v = s * (s + 1)) (hk : k = s * t) (hr : r = (s + 2) * t)
    (hl : r * (k - 1) = lam * (v - 1)) : lam * (s - 1) = 2 * t * (s * t - 1) := by
  apply mul_left_cancel₀ (show s + 2 ≠ 0 by omega)
  linear_combination -2 * hl + 2 * (k - 1) * hr + 2 * (s + 2) * t * hk - lam * hv

/-- C11, [CGSS] Theorem 5.8, `s558nblam`: the divisibility remainder. -/
theorem lambda_remainder (s t lam : ℤ)
    (h : lam * (s - 1) = 2 * t * (s * t - 1)) :
    2 * t * (t - 1) = (s - 1) * (lam - 2 * t ^ 2) := by
  linear_combination -h

/-- C11, [CGSS] Theorem 5.8, `s558nblam`: the necessary divisibility condition. -/
theorem parameter_dvd (s t lam : ℤ)
    (h : lam * (s - 1) = 2 * t * (s * t - 1)) : (s - 1) ∣ 2 * t * (t - 1) :=
  ⟨lam - 2 * t ^ 2, lambda_remainder s t lam h⟩

/-- C11, [CGSS] Theorem 5.8, `s558nbineq`: the corrected direction in Error 4. -/
theorem two_mul_sub_one_le (v k s t : ℤ) (hs : 0 < s)
    (hv : 2 * v = s * (s + 1)) (hk : k = s * t) (hkv : k ≤ v) : 2 * t - 1 ≤ s := by
  nlinarith

/-- C11, [CGSS] Theorem 5.8, `s558nbc`: the nonprincipal eigenvalue square. -/
theorem nonprincipal_square (s t : ℝ) (hs : s ≠ 1) :
    (s + 2) * t - 2 * t * (s * t - 1) / (s - 1) + t ^ 2 =
      t * (s + 1) * (s - t) / (s - 1) := by
  field_simp
  ring

/-- C11, [CGSS] Theorem 5.8, `s558nbc`: the spectral multiplicities and order. -/
theorem spectral_parameters (s : ℚ) :
    s * (s + 1) / 2 - 1 = (s - 1) * (s + 2) / 2 ∧
    (s + 1) * (s + 2) / 2 - s * (s + 1) / 2 = s + 1 ∧
    1 + (s + 1) + 2 * ((s - 1) * (s + 2) / 2) = s * (s + 2) := by
  constructor
  · ring
  constructor <;> ring

/-- C11, [CGSS] Theorem 5.8, `s558nbhp`: evaluate the Hoffman polynomial. -/
theorem hoffman_value (s t : ℝ) (hs : s ≠ 1) :
    ((s + 1) * t + t) *
        (((s + 1) * t) ^ 2 - t * (s + 1) * (s - t) / (s - 1)) =
      s * (s + 2) * (t ^ 2 * (s + 1) * (s * t - 1) / (s - 1)) := by
  field_simp
  ring

/-- C11, [CGSS] Theorem 5.8, `s558nbdiag`: the diagonal of the cubic identity. -/
theorem triangle_diagonal (s t : ℝ) (hs : s ≠ 1) :
    t ^ 2 * (s + 1) * (s * t - 1) / (s - 1) +
        t * (s + 1) * (s - t) / (s - 1) * t - t ^ 2 * (s + 1) =
      t ^ 3 * (s + 1) := by
  field_simp
  ring

/-- C11, [CGSS] Theorem 5.8, `s558nbeven`: triangle parity implies the stated parity. -/
theorem even_mul_of_even_cube (s t : ℤ) (h : Even (t ^ 3 * (s + 1))) :
    Even (t * (s + 1)) := by
  simpa [Int.even_mul, Int.even_pow] using h

end Computations.C11
