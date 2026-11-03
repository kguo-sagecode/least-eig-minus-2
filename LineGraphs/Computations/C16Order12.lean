/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Checker

/-!
# C16: the order-12 example

Kernel verification of the certificate matrix and Hypothesis 6.1 of [CGSS].
-/

namespace Computations.C16

/-- The explicit order-12 matrix in the C16 certificate. -/
def h12 : Matrix (Fin 12) (Fin 12) ℤ := toMatrix 12 h12Rows

/-- C16: the order-12 matrix is Hadamard. -/
theorem h12_isHadamard : h12.IsHadamard := by
  simp only [Matrix.isHadamard_iff, Unitary.mem_iff_eq_one_or_eq_neg_one,
    ← Matrix.ext_iff, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Fintype.card_fin, Matrix.one_apply,
    h12, toMatrix, Int.cast_id]
  decide +kernel

/-- C16: the list check of Hypothesis 6.1 at `x = 4`. -/
theorem h12_agreement_checked : checkFourRowAgreement 12 4 h12Rows = true := by
  decide +kernel

/-- C16: Hypothesis 6.1 for the order-12 matrix, with `x = 4`. -/
theorem h12_fourRowAgreement : h12_isHadamard.FourRowAgreement 4 :=
  checkFourRowAgreement_sound h12_isHadamard h12_agreement_checked

end Computations.C16
