/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A scalar matrix plus an all-ones matrix

The determinant lemma `hc:lem:det` of the Hall–Connor blueprint, used in the proof cited
in Remark 5.12 and Example 5.13 of [CGSS].
-/

namespace Matrix

/-- The determinant in `hc:lem:det` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13). The nonempty hypothesis justifies the exponent `n - 1`. -/
theorem det_smul_one_add_smul_J {U : Type*} [Fintype U] [DecidableEq U]
    (hn : 1 ≤ Fintype.card U) (α β : ℚ) (hα : α ≠ 0) :
    (α • (1 : Matrix U U ℚ) + β • Matrix.of (fun _ _ ↦ (1 : ℚ))).det =
      α ^ (Fintype.card U - 1) * (α + Fintype.card U * β) := by
  have hfactor : α • (1 + replicateCol Unit (fun _ : U ↦ β / α) *
      replicateRow Unit (fun _ : U ↦ (1 : ℚ))) =
      α • (1 : Matrix U U ℚ) + β • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Matrix.of_apply, smul_eq_mul,
      mul_one, Fintype.sum_unique]
    field_simp
  rw [← hfactor, det_smul, det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn' : Fintype.card U = (Fintype.card U - 1) + 1 := by omega
  conv_lhs =>
    lhs
    rw [hn', pow_succ]
  field_simp

end Matrix
