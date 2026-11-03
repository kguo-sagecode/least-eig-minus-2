/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Determinant
import LineGraphs.Computations.C19Arithmetic

/-!
# The Bruck–Ryser–Chowla obstruction at order 22

The determinant proof `hc:thm:BRC` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13).
-/

namespace Matrix

/-- The even-order Bruck–Ryser–Chowla instance `hc:thm:BRC`
([CGSS], Remark 5.12 and Example 5.13). The integral determinant cannot square to `49 * 5^21`. -/
theorem bruck_ryser_chowla_twenty_two (M : Matrix (Fin 22) (Fin 22) ℤ) :
    M * M.transpose ≠ (5 : ℤ) • 1 + (2 : ℤ) • Matrix.of (fun _ _ ↦ (1 : ℤ)) := by
  intro h
  have hrat : M.map (Int.castRingHom ℚ) * (M.map (Int.castRingHom ℚ)).transpose =
      (5 : ℚ) • (1 : Matrix (Fin 22) (Fin 22) ℚ) +
        (2 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, smul_eq_mul]
    by_cases hij : i = j <;> norm_num [hij]
  have hcast : (M.map (Int.castRingHom ℚ)).det = (M.det : ℚ) := by
    change (M.map (fun z : ℤ ↦ (z : ℚ))).det = _
    exact (Int.cast_det M).symm
  have hdet := congrArg Matrix.det hrat
  rw [Matrix.det_mul, Matrix.det_transpose, hcast,
    Matrix.det_smul_one_add_smul_J (by decide) 5 2 (by norm_num)] at hdet
  have hsquare : (M.det : ℚ) ^ 2 = 49 * 5 ^ 21 := by
    norm_num at hdet ⊢
    nlinarith only [hdet]
  apply Computations.C19.not_sq_eq_49_mul_5_pow_21 M.det
  exact_mod_cast hsquare

end Matrix
