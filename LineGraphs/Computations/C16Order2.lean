/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Checker

/-!
# C16: the order-2 example

Kernel verification of the certificate matrix and Hypothesis 6.1 of [CGSS].
-/

namespace Computations.C16

/-- The explicit order-2 matrix in the C16 certificate. -/
def h2 : Matrix (Fin 2) (Fin 2) ℤ := toMatrix 2 h2Rows

/-- C16: the order-2 matrix is Hadamard. -/
theorem h2_isHadamard : h2.IsHadamard := by
  simp only [Matrix.isHadamard_iff, Unitary.mem_iff_eq_one_or_eq_neg_one,
    ← Matrix.ext_iff, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Fintype.card_fin, Matrix.one_apply,
    h2, toMatrix, Int.cast_id]
  decide +kernel

/-- C16: the list check of Hypothesis 6.1 at `x = 2`. -/
theorem h2_agreement_checked : checkFourRowAgreement 2 2 h2Rows = true := by
  decide +kernel

/-- C16: Hypothesis 6.1 for the order-2 matrix, with `x = 2`. -/
theorem h2_fourRowAgreement : h2_isHadamard.FourRowAgreement 2 :=
  checkFourRowAgreement_sound h2_isHadamard h2_agreement_checked

end Computations.C16
