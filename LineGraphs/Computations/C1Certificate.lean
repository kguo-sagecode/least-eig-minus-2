/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.Checkers

/-! # List polynomial certificates for C1 in [CGSS, Lemma 2.10]

`Computations.polynomialOfCoeffs` interprets lists of ascending integer coefficients.
The determinant certificate adds zero-padded list arithmetic to that interface; its concrete
checks use kernel reduction on lists, with no matrix or real arithmetic in the executable part.
-/

namespace Computations.C1

/-- Zero-padded coefficient addition for the polynomial identity in `comp:C1`
([CGSS, Lemma 2.10]). -/
def coeffAdd : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: coeffAdd as bs

/-- Coefficient multiplication for the polynomial identity in `comp:C1`
([CGSS, Lemma 2.10]). -/
def coeffMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => coeffAdd (b.map (a * ·)) (0 :: coeffMul as b)

/-- Coefficient subtraction for the polynomial identity in `comp:C1`
([CGSS, Lemma 2.10]). -/
def coeffSub (a b : List ℤ) : List ℤ := coeffAdd a (b.map Neg.neg)

/-- Soundness of coefficient addition in `comp:C1` ([CGSS, Lemma 2.10]). -/
theorem polynomialOfCoeffs_add (a b : List ℤ) :
    polynomialOfCoeffs (coeffAdd a b) = polynomialOfCoeffs a + polynomialOfCoeffs b := by
  induction a generalizing b with
  | nil => simp [coeffAdd, polynomialOfCoeffs]
  | cons a as ih =>
    cases b with
    | nil => simp [coeffAdd, polynomialOfCoeffs]
    | cons b bs => simp only [coeffAdd, polynomialOfCoeffs, ih, map_add]; ring

/-- Soundness of scaling coefficients in `comp:C1` ([CGSS, Lemma 2.10]). -/
theorem polynomialOfCoeffs_scale (c : ℤ) (a : List ℤ) :
    polynomialOfCoeffs (a.map (c * ·)) = Polynomial.C c * polynomialOfCoeffs a := by
  induction a with
  | nil => simp [polynomialOfCoeffs]
  | cons a as ih => simp only [List.map_cons, polynomialOfCoeffs, ih, map_mul]; ring

/-- Soundness of coefficient multiplication in `comp:C1` ([CGSS, Lemma 2.10]). -/
theorem polynomialOfCoeffs_mul (a b : List ℤ) :
    polynomialOfCoeffs (coeffMul a b) = polynomialOfCoeffs a * polynomialOfCoeffs b := by
  induction a with
  | nil => simp [coeffMul, polynomialOfCoeffs]
  | cons a as ih =>
    simp only [coeffMul, polynomialOfCoeffs_add, polynomialOfCoeffs_scale,
      polynomialOfCoeffs, ih, map_zero]
    ring

/-- Soundness of coefficient subtraction in `comp:C1` ([CGSS, Lemma 2.10]). -/
theorem polynomialOfCoeffs_sub (a b : List ℤ) :
    polynomialOfCoeffs (coeffSub a b) = polynomialOfCoeffs a - polynomialOfCoeffs b := by
  have hn : polynomialOfCoeffs (b.map Neg.neg) = -polynomialOfCoeffs b := by
    simpa only [neg_one_mul, map_neg, map_one] using polynomialOfCoeffs_scale (-1) b
  simp [coeffSub, polynomialOfCoeffs_add, hn, sub_eq_add_neg]

/-- The six-term `3 × 3` determinant on coefficient lists in `comp:C1`
([CGSS, Lemma 2.10]), with the entries given in row order. -/
def detCoeffsThree (a b c d e f g h i : List ℤ) : List ℤ :=
  coeffSub
    (coeffAdd
      (coeffAdd
        (coeffSub (coeffSub (coeffMul (coeffMul a e) i) (coeffMul (coeffMul a f) h))
          (coeffMul (coeffMul b d) i))
        (coeffMul (coeffMul b f) g))
      (coeffMul (coeffMul c d) h))
    (coeffMul (coeffMul c e) g)

/-- Soundness of the six-term list determinant for `comp:C1` ([CGSS, Lemma 2.10]). -/
theorem polynomialOfCoeffs_detCoeffsThree (a b c d e f g h i : List ℤ) :
    polynomialOfCoeffs (detCoeffsThree a b c d e f g h i) =
      (Matrix.det !![polynomialOfCoeffs a, polynomialOfCoeffs b, polynomialOfCoeffs c;
        polynomialOfCoeffs d, polynomialOfCoeffs e, polynomialOfCoeffs f;
        polynomialOfCoeffs g, polynomialOfCoeffs h, polynomialOfCoeffs i]) := by
  simp [detCoeffsThree, polynomialOfCoeffs_add, polynomialOfCoeffs_sub,
    polynomialOfCoeffs_mul, Matrix.det_fin_three]

/-- First `3 × 3` minor in step 210det of `comp:C1` ([CGSS, Lemma 2.10]):
its coefficients represent `k^5(7-k)`. -/
theorem minor_zero_checked :
    detCoeffsThree [0, 1, 1] [0, -1, 1] [0, -1, 1]
      [0, -1, 1] [0, 1, 1] [0, 1] [0, -1, 1] [0, 1] [0, 1, 1] =
        [0, 0, 0, 0, 0, 7, -1] := by
  decide +kernel

/-- Second nonzero minor in step 210det of `comp:C1` ([CGSS, Lemma 2.10]):
its coefficients represent `-4k^4` (with a trailing zero coefficient). -/
theorem minor_two_checked :
    detCoeffsThree [] [0, 1, 1] [0, -1, 1]
      [0, 1] [0, -1, 1] [0, 1] [] [0, -1, 1] [0, 1, 1] =
        [0, 0, 0, 0, -4, 0] := by
  decide +kernel

end Computations.C1
