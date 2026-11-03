/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Basic

/-!
# Incidence identities for Hall–Connor

The lemma `hc:lem:incidence` of the Hall–Connor blueprint, used in Remark 5.12 and
Example 5.13 of [CGSS]. Incidence matrices are integral, and block Gram matrices are rational.
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable {v k b r lam : ℕ}

/-- Counting a row of the incidence matrix (`hcIncRow`; [CGSS], Remark 5.12). -/
theorem incMatrix_row_sum (D : Design P B v k b r lam) (p : P) :
    ∑ label, D.incMatrix p label = (r : ℤ) := by
  simp [incMatrix, D.card_blocksThrough]

/-- Counting a column of the incidence matrix (`hcIncCol`; [CGSS], Remark 5.12). -/
theorem incMatrix_col_sum (D : Design P B v k b r lam) (label : B) :
    ∑ p, D.incMatrix p label = (k : ℤ) := by
  simp [incMatrix, D.card_block]

/-- Point-pair counts as entries of the incidence product (`hcIncDiag`, `hcIncOff`;
[CGSS], Remark 5.12). -/
theorem incMatrix_mul_transpose_apply (D : Design P B v k b r lam) (p q : P) :
    (D.incMatrix * D.incMatrix.transpose) p q = if p = q then (r : ℤ) else lam := by
  have hmul (label : B) : D.incMatrix p label * D.incMatrix q label =
      if p ∈ D.block label ∧ q ∈ D.block label then (1 : ℤ) else 0 := by
    by_cases hp : p ∈ D.block label <;> by_cases hq : q ∈ D.block label <;>
      simp [incMatrix, hp, hq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hmul]
  by_cases hpq : p = q
  · subst q
    simp [D.card_blocksThrough]
  · simp [hpq, D.card_blocksThroughPair p q hpq]

/-- Gram entries count block intersections (`hcIncG`; [CGSS], Remark 5.12). -/
theorem G_apply (D : Design P B v k b r lam) (X Y : B) :
    D.G X Y = ((D.block X ∩ D.block Y).card : ℚ) := by
  have hmul (p : P) :
      (D.incMatrix.map (Int.castRingHom ℚ)) p X *
          (D.incMatrix.map (Int.castRingHom ℚ)) p Y =
        if p ∈ D.block X ∩ D.block Y then (1 : ℚ) else 0 := by
    by_cases hX : p ∈ D.block X <;> by_cases hY : p ∈ D.block Y <;>
      simp [incMatrix, Matrix.map_apply, hX, hY]
  simp only [G, Matrix.mul_apply, Matrix.transpose_apply, hmul]
  simp only [Finset.sum_boole]
  congr 2
  ext p
  simp

/-- Symmetry of the block Gram matrix (`hcIncG`; [CGSS], Remark 5.12). -/
theorem G_transpose (D : Design P B v k b r lam) : D.G.transpose = D.G := by
  simp [G, Matrix.transpose_mul]

variable (D : Design P B 15 5 21 7 2)

/-- The integral incidence product, `hcIncNN` of `hc:lem:incidence`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem incMatrix_mul_transpose_15_5_2 :
    D.incMatrix * D.incMatrix.transpose =
      (5 : ℤ) • (1 : Matrix P P ℤ) + (2 : ℤ) • Matrix.of (fun _ _ ↦ (1 : ℤ)) := by
  ext p q
  rw [D.incMatrix_mul_transpose_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul]
  by_cases hpq : p = q <;> simp [hpq]

/-- The row sums, `hcIncRow` of `hc:lem:incidence` ([CGSS], Remark 5.12). -/
theorem incMatrix_row_sum_15_5_2 :
    D.incMatrix *ᵥ (fun _ ↦ (1 : ℤ)) = fun _ ↦ (7 : ℤ) := by
  ext p
  simpa [Matrix.mulVec, dotProduct] using D.incMatrix_row_sum p

/-- The column sums, `hcIncCol` of `hc:lem:incidence` ([CGSS], Remark 5.12). -/
theorem incMatrix_col_sum_15_5_2 :
    D.incMatrix.transpose *ᵥ (fun _ ↦ (1 : ℤ)) = fun _ ↦ (5 : ℤ) := by
  ext label
  simpa [Matrix.mulVec, dotProduct] using D.incMatrix_col_sum label

/-- Rational transport of `hcIncNN` ([CGSS], Remark 5.12). -/
theorem incMatrix_rat_mul_transpose_15_5_2 :
    D.incMatrix.map (Int.castRingHom ℚ) *
        (D.incMatrix.map (Int.castRingHom ℚ)).transpose =
      (5 : ℚ) • (1 : Matrix P P ℚ) + (2 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, D.incMatrix_mul_transpose_15_5_2]
  ext p q
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  by_cases hpq : p = q <;> norm_num [hpq]

/-- The Gram row sum, `hcIncGJ` ([CGSS], Remark 5.12). -/
theorem G_row_sum (X : B) : ∑ Y, D.G X Y = (35 : ℚ) := by
  simp only [G, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hrow (p : P) : ∑ Y, (D.incMatrix.map (Int.castRingHom ℚ)) p Y = (7 : ℚ) := by
    change ∑ Y, (D.incMatrix p Y : ℚ) = 7
    exact_mod_cast D.incMatrix_row_sum p
  simp only [hrow, ← Finset.sum_mul]
  have hcol : ∑ p, (D.incMatrix.map (Int.castRingHom ℚ)) p X = (5 : ℚ) := by
    change ∑ p, (D.incMatrix p X : ℚ) = 5
    exact_mod_cast D.incMatrix_col_sum X
  rw [hcol]
  norm_num

/-- Multiplication by the all-ones matrix, `hcIncGJ` ([CGSS], Remark 5.12). -/
theorem G_mul_J :
    D.G * Matrix.of (fun _ _ ↦ (1 : ℚ)) =
      (35 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
  ext X Y
  simpa [Matrix.mul_apply] using D.G_row_sum X

/-- The transpose of `hcIncGJ`, namely `hcIncJG` ([CGSS], Remark 5.12). -/
theorem J_mul_G :
    Matrix.of (fun _ _ ↦ (1 : ℚ)) * D.G =
      (35 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
  have h := congrArg Matrix.transpose D.G_mul_J
  rw [Matrix.transpose_mul, D.G_transpose] at h
  exact h

include D in
/-- The square of the all-ones block matrix, `hcIncJJ` ([CGSS], Remark 5.12). -/
theorem J_mul_J :
    (Matrix.of (fun _ _ ↦ (1 : ℚ)) : Matrix B B ℚ) *
        Matrix.of (fun _ _ ↦ (1 : ℚ)) =
      (21 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
  ext X Y
  simp [Matrix.mul_apply, D.card_blocks]

/-- The Gram square identity, `hcIncSquare` of `hc:lem:incidence`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem G_mul_G :
    D.G * D.G = (5 : ℚ) • D.G + (50 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
  let N := D.incMatrix.map (Int.castRingHom ℚ)
  have hNN : N * N.transpose =
      (5 : ℚ) • (1 : Matrix P P ℚ) + (2 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) :=
    D.incMatrix_rat_mul_transpose_15_5_2
  have hNJ : N.transpose * Matrix.of (fun _ _ ↦ (1 : ℚ)) * N =
      (25 : ℚ) • (Matrix.of (fun _ _ ↦ (1 : ℚ)) : Matrix B B ℚ) := by
    ext X Y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_one]
    have hcol (Z : B) : ∑ p, N p Z = (5 : ℚ) := by
      change ∑ p, (D.incMatrix p Z : ℚ) = 5
      exact_mod_cast D.incMatrix_col_sum Z
    simp only [hcol, ← Finset.mul_sum]
    norm_num
  change (N.transpose * N) * (N.transpose * N) = _
  rw [Matrix.mul_assoc N.transpose N, ← Matrix.mul_assoc N N.transpose, hNN]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_smul, ← Matrix.mul_assoc, hNJ, smul_smul]
  norm_num
  rfl

end Design
