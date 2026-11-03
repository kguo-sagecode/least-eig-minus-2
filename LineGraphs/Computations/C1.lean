/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C1Certificate

/-! # C1: the determinant in [CGSS, Lemma 2.10] -/

namespace Computations.C1

variable {R : Type*} [CommRing R]

/-- The five block sums in step 210gram of `lem:2.10` ([CGSS, Lemma 2.10]).
The entry in position `(3,1)` in the paper's numbering is zero (errata Error 3). -/
def blockSumMatrix (k : R) : Matrix (Fin 5) (Fin 5) R :=
  !![2, 1, 0, 0, k;
     1, 2, 0, k, 0;
     0, 0, k ^ 2 + k, k ^ 2 - k, k ^ 2 - k;
     0, k, k ^ 2 - k, k ^ 2 + k, k;
     k, 0, k ^ 2 - k, k, k ^ 2 + k]

/-- The principal minor obtained by deleting the first row and column in step 210Dgram
of `comp:C1` ([CGSS, Lemma 2.10]). -/
def blockSumMinor (k : R) : Matrix (Fin 4) (Fin 4) R :=
  !![2, 0, k, 0;
     0, k ^ 2 + k, k ^ 2 - k, k ^ 2 - k;
     k, k ^ 2 - k, k ^ 2 + k, k;
     0, k ^ 2 - k, k, k ^ 2 + k]

/-- Step 210Dgram of `comp:C1` ([CGSS, Lemma 2.10]): deleting row and column one
of the block-sum matrix gives `blockSumMinor`. -/
theorem blockSumMinor_eq_submatrix (k : R) :
    blockSumMinor k = (blockSumMatrix k).submatrix Fin.succ Fin.succ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The first minor evaluation in step 210det of `comp:C1` ([CGSS, Lemma 2.10]),
transported from the kernel-checked coefficient list. -/
theorem det_minor_zero (k : R) :
    Matrix.det !![k ^ 2 + k, k ^ 2 - k, k ^ 2 - k;
      k ^ 2 - k, k ^ 2 + k, k; k ^ 2 - k, k, k ^ 2 + k] = k ^ 5 * (7 - k) := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom R) k)
    (polynomialOfCoeffs_detCoeffsThree [0, 1, 1] [0, -1, 1] [0, -1, 1]
      [0, -1, 1] [0, 1, 1] [0, 1] [0, -1, 1] [0, 1] [0, 1, 1])
  rw [minor_zero_checked] at h
  simp only [Matrix.det_fin_three, polynomialOfCoeffs] at h
  simp only [eq_intCast, Int.cast_zero, Int.cast_ofNat, Int.reduceNeg, Int.cast_neg,
    Int.cast_one, mul_zero, add_zero, mul_neg, mul_one, zero_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_add, Polynomial.eval₂_ofNat, Polynomial.eval₂_neg,
    Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val, Polynomial.eval₂_sub,
    Polynomial.eval₂_one] at h
  rw [Matrix.det_fin_three]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination -h

/-- The second minor evaluation in step 210det of `comp:C1` ([CGSS, Lemma 2.10]),
transported from the kernel-checked coefficient list. -/
theorem det_minor_two (k : R) :
    Matrix.det !![0, k ^ 2 + k, k ^ 2 - k;
      k, k ^ 2 - k, k; 0, k ^ 2 - k, k ^ 2 + k] = -4 * k ^ 4 := by
  have h := congrArg (Polynomial.eval₂ (Int.castRingHom R) k)
    (polynomialOfCoeffs_detCoeffsThree [] [0, 1, 1] [0, -1, 1]
      [0, 1] [0, -1, 1] [0, 1] [] [0, -1, 1] [0, 1, 1])
  rw [minor_two_checked] at h
  simp only [Matrix.det_fin_three, polynomialOfCoeffs] at h
  simp only [eq_intCast, Int.cast_zero, Int.reduceNeg, Int.cast_neg, Int.cast_ofNat,
    mul_zero, add_zero, mul_neg, zero_add, Polynomial.eval₂_neg, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Int.cast_one, mul_one, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, zero_mul, Matrix.cons_val, sub_self, zero_sub, sub_zero,
    Polynomial.eval₂_add, Polynomial.eval₂_one] at h
  rw [Matrix.det_fin_three]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, zero_mul, Matrix.cons_val, sub_self,
    zero_sub, mul_zero, add_zero, sub_zero, neg_mul]
  linear_combination -h

-- Lemma 2.10 (Computation C1)
/-- Computation C1 (`comp:C1`, step 210det of [CGSS, Lemma 2.10]):
the determinant of the corrected principal block-sum minor is `2k^5(5-k)`. -/
theorem det_blockSumMinor (k : R) : (blockSumMinor k).det = 2 * k ^ 5 * (5 - k) := by
  -- Expand row `(2,0,k,0)` and use the two certified three-by-three minors.
  have hm₀ : (blockSumMinor k).submatrix Fin.succ (0 : Fin 4).succAbove =
      !![k ^ 2 + k, k ^ 2 - k, k ^ 2 - k;
        k ^ 2 - k, k ^ 2 + k, k; k ^ 2 - k, k, k ^ 2 + k] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm₂ : (blockSumMinor k).submatrix Fin.succ (2 : Fin 4).succAbove =
      !![0, k ^ 2 + k, k ^ 2 - k; k, k ^ 2 - k, k; 0, k ^ 2 - k, k ^ 2 + k] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  calc
    (blockSumMinor k).det =
        2 * ((blockSumMinor k).submatrix Fin.succ (0 : Fin 4).succAbove).det +
          k * ((blockSumMinor k).submatrix Fin.succ (2 : Fin 4).succAbove).det := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, blockSumMinor]
    _ = 2 * k ^ 5 * (5 - k) := by
      rw [hm₀, hm₂, det_minor_zero, det_minor_two]
      ring

end Computations.C1
