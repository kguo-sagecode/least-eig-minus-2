/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Rational eigenvalues of integer matrices

Theorem 9.6 of the spectral toolkit. Symmetry is not needed.
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A rational eigenvalue of an integer matrix, witnessed over the reals, is an integer. -/
theorem eigenvalue_isInteger_of_rat (A : Matrix n n ℤ) {b : ℚ} {v : n → ℝ}
    (hv : v ≠ 0) (he : A.map (Int.castRingHom ℝ) *ᵥ v = (b : ℝ) • v) :
    ∃ z : ℤ, (z : ℚ) = b := by
  classical
  -- Step `rat-realzero`: the shifted real matrix has a nonzero kernel vector.
  have hker : (scalar n (b : ℝ) - A.map (Int.castRingHom ℝ)) *ᵥ v = 0 := by
    rw [sub_mulVec, he]
    ext i
    simp [scalar, mulVec_diagonal, Pi.smul_def]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hd : (scalar n (b : ℝ) - A.map (Int.castRingHom ℝ)).det = 0 :=
    det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
      (mem_nonZeroDivisors_iff_ne_zero.mpr hi)
  -- Step `rat-cast`: descend the characteristic-polynomial root from ℝ to ℚ.
  have hr : aeval (b : ℝ) A.charpoly = 0 := by
    rw [← eval_charpoly, charpoly_map] at hd
    rw [show Int.castRingHom ℝ = algebraMap ℤ ℝ from Subsingleton.elim _ _] at hd
    simpa only [eval_map_algebraMap] using hd
  have hq : aeval b A.charpoly = 0 :=
    (aeval_algebraMap_eq_zero_iff ℝ b A.charpoly).mp hr
  -- Steps `rat-monic`, `rat-integrality`: apply the monic integral-root theorem over ℤ.
  have hint := isInteger_of_is_root_of_monic A.charpoly_monic hq
  exact hint

end Matrix
