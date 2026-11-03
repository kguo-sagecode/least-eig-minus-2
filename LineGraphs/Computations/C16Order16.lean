/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Order16Rows0
import LineGraphs.Computations.C16Order16Rows1
import LineGraphs.Computations.C16Order16Rows2
import LineGraphs.Computations.C16Order16Rows3

/-!
# C16: the order-16 example

Kernel verification of the certificate matrix and Hypothesis 6.1 of [CGSS].
-/

namespace Computations.C16

/-- The explicit order-16 matrix in the C16 certificate. -/
def h16 : Matrix (Fin 16) (Fin 16) ℤ := toMatrix 16 h16Rows

/-- C16: the order-16 matrix is Hadamard. -/
theorem h16_isHadamard : h16.IsHadamard := by
  simp only [Matrix.isHadamard_iff, Unitary.mem_iff_eq_one_or_eq_neg_one,
    ← Matrix.ext_iff, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.smul_apply, smul_eq_mul, Fintype.card_fin, Matrix.one_apply,
    h16, toMatrix, Int.cast_id]
  decide +kernel

/-- C16: the list check of Hypothesis 6.1 at `x = 16`. -/
theorem h16_agreement_checked : checkFourRowAgreement 16 16 h16Rows = true := by
  unfold checkFourRowAgreement
  rw [show List.range 16 = List.range' 0 4 ++ List.range' 4 4 ++
    List.range' 8 4 ++ List.range' 12 4 by decide]
  simp only [List.all_append, h16_agreement_chunk0, h16_agreement_chunk1,
    h16_agreement_chunk2, h16_agreement_chunk3, Bool.and_true]
  decide +kernel

/-- C16: Hypothesis 6.1 for the order-16 matrix, with `x = 16`. -/
theorem h16_fourRowAgreement : h16_isHadamard.FourRowAgreement 16 :=
  checkFourRowAgreement_sound h16_isHadamard h16_agreement_checked

end Computations.C16
