/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Checker

/-!
# C16: the order-4 example

Kernel verification of the certificate matrix and Hypothesis 6.1 of [CGSS].
-/

namespace Computations.C16

/-- The explicit order-4 matrix in the C16 certificate. -/
def h4 : Matrix (Fin 4) (Fin 4) ℤ := toMatrix 4 h4Rows

/-- C16: the order-4 matrix is Hadamard. -/
theorem h4_isHadamard : h4.IsHadamard := by
  simp only [Matrix.isHadamard_iff, Unitary.mem_iff_eq_one_or_eq_neg_one,
    ← Matrix.ext_iff, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Fintype.card_fin, Matrix.one_apply,
    h4, toMatrix, Int.cast_id]
  decide +kernel

/-- C16: the list check of Hypothesis 6.1 at `x = 4`. -/
theorem h4_agreement_checked : checkFourRowAgreement 4 4 h4Rows = true := by
  decide +kernel

/-- C16: Hypothesis 6.1 for the order-4 matrix, with `x = 4`. -/
theorem h4_fourRowAgreement : h4_isHadamard.FourRowAgreement 4 :=
  checkFourRowAgreement_sound h4_isHadamard h4_agreement_checked

end Computations.C16
