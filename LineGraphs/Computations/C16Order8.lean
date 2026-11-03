/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Checker

/-!
# C16: the order-8 example

Kernel verification of the certificate matrix and Hypothesis 6.1 of [CGSS].
-/

namespace Computations.C16

/-- The explicit order-8 matrix in the C16 certificate. -/
def h8 : Matrix (Fin 8) (Fin 8) ℤ := toMatrix 8 h8Rows

/-- C16: the order-8 matrix is Hadamard. -/
theorem h8_isHadamard : h8.IsHadamard := by
  simp only [Matrix.isHadamard_iff, Unitary.mem_iff_eq_one_or_eq_neg_one,
    ← Matrix.ext_iff, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Fintype.card_fin, Matrix.one_apply,
    h8, toMatrix, Int.cast_id]
  decide +kernel

/-- C16: the list check of Hypothesis 6.1 at `x = 8`. -/
theorem h8_agreement_checked : checkFourRowAgreement 8 8 h8Rows = true := by
  decide +kernel

/-- C16: Hypothesis 6.1 for the order-8 matrix, with `x = 8`. -/
theorem h8_fourRowAgreement : h8_isHadamard.FourRowAgreement 8 :=
  checkFourRowAgreement_sound h8_isHadamard h8_agreement_checked

end Computations.C16
