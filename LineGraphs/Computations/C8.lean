/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Tactic

/-!
# The finite quadratic bound

C8 for Theorem 4.4 of [CGSS]. The positive denominator is cleared over the
reals; the resulting bounded integer assertion is checked by the kernel.
-/

namespace Computations.C8

/-- C8 for Theorem 4.4 of [CGSS]: the complete bounded integer check after
clearing the positive denominator. -/
theorem quadratic_checked : ∀ n d : Fin 29,
    d.val ≤ n.val - 1 → n.val < 2 * d.val + 4 →
    0 ≤ ((d.val : ℤ) - 2 * n.val + 16) * (2 * d.val + 4 - n.val) +
      14 * (2 * n.val - 2 * d.val - 4) →
    d.val ≤ 16 ∨ n.val = 28 ∧ d.val = 17 := by
  decide +kernel

/-- C8 for Theorem 4.4 of [CGSS]: the trace inequality permits valency at
most 16, apart from the pair `(n,d) = (28,17)`. -/
theorem quadratic_bound (n d : ℕ) (hn : n ≤ 28) (hd : d ≤ n - 1)
    (hlt : n < 2 * d + 4)
    (hq : 0 ≤ ((d : ℝ) - 2 * n + 16) +
      14 * (2 * n - 2 * d - 4) / (2 * d + 4 - n)) :
    d ≤ 16 ∨ n = 28 ∧ d = 17 := by
  have hden : (0 : ℝ) < 2 * d + 4 - n := by
    have h : (n : ℝ) < 2 * d + 4 := by exact_mod_cast hlt
    linarith
  have hmul := mul_nonneg hq hden.le
  rw [add_mul, div_mul_cancel₀ _ hden.ne'] at hmul
  have hi : (0 : ℤ) ≤ ((d : ℤ) - 2 * n + 16) * (2 * d + 4 - n) +
      14 * (2 * n - 2 * d - 4) := by exact_mod_cast hmul
  exact quadratic_checked ⟨n, by omega⟩ ⟨d, by omega⟩ hd hlt hi

end Computations.C8
