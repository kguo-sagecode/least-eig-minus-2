/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# C19: the determinant is not a square

The descent at five in `hc:lem:odd-power` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13).
-/

namespace Computations.C19

/-- Descent at five, `hcOddAll` of `hc:lem:odd-power` (C19; [CGSS], Remark 5.12). -/
theorem not_sq_eq_49_mul_5_pow_odd (m : ℕ) (d : ℤ) : d ^ 2 ≠ 49 * 5 ^ (2 * m + 1) := by
  have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_five
  have hdivide (n : ℕ) (z : ℤ) (h : z ^ 2 = 49 * 5 ^ (2 * n + 1)) :
      ∃ e : ℤ, z = 5 * e := by
    apply hp.dvd_of_dvd_pow (n := 2)
    refine ⟨49 * 5 ^ (2 * n), ?_⟩
    rw [h, pow_succ]
    ring
  induction m generalizing d with
  | zero =>
    intro h
    obtain ⟨e, rfl⟩ := hdivide 0 d h
    norm_num at h
    have he : 5 * e ^ 2 = 49 := by nlinarith only [h]
    have hbad : (5 : ℤ) ∣ 49 := ⟨e ^ 2, he.symm⟩
    norm_num at hbad
  | succ m ih =>
    intro h
    obtain ⟨e, rfl⟩ := hdivide (m + 1) d h
    have hpow : (5 : ℤ) ^ (2 * (m + 1) + 1) = 25 * 5 ^ (2 * m + 1) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, pow_add]
      ring
    rw [hpow] at h
    apply ih e
    nlinarith only [h]

/-- The order-22 determinant obstruction, `hc:lem:odd-power` (C19;
[CGSS], Remark 5.12 and Example 5.13). -/
theorem not_sq_eq_49_mul_5_pow_21 (d : ℤ) : d ^ 2 ≠ 49 * 5 ^ 21 :=
  not_sq_eq_49_mul_5_pow_odd 10 d

end Computations.C19
