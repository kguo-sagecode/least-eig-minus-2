/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.CommonNeighbors
import LineGraphs.Cited.HallConnor.Determinant
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Connor's matrix

The identities, quadratic inequality, and rank bound `hc:lem:Connor`, `hc:lem:rank`, and
`hc:lem:principal` of the Hall–Connor blueprint. These support the cited nonexistence theorem
used in Remark 5.12 and Example 5.13 of [CGSS].
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- Symmetry of Connor's matrix (`hcCSym`; [CGSS], Remark 5.12). -/
theorem C_transpose : D.C.transpose = D.C := by
  simp only [C, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, D.G_transpose]
  rfl

/-- The three entries of Connor's matrix (`hcCDiag`, `hcCAdj`, `hcCNonadj`;
[CGSS], Remark 5.12): ten on the diagonal, three on edges, and minus four otherwise. -/
theorem C_apply (X Y : B) :
    D.C X Y = if X = Y then 10 else if D.Z.Adj X Y then 3 else -4 := by
  simp only [C, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, D.G_apply, smul_eq_mul]
  by_cases hXY : X = Y
  · subst Y
    norm_num [D.card_block]
  · rw [ite_eq_right hXY, ite_eq_right hXY]
    by_cases hadj : D.Z.Adj X Y
    · rw [ite_eq_left hadj, hadj.2]
      norm_num
    · have hi : (D.block X ∩ D.block Y).card = 2 :=
        (D.inter_card_eq_one_or_two hXY).resolve_left (fun h ↦ hadj ⟨hXY, h⟩)
      rw [ite_eq_right hadj, hi]
      norm_num

/-- The quadratic identity `hcCSquare` of `hc:lem:Connor`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem C_mul_C : D.C * D.C = (35 : ℚ) • D.C := by
  unfold C
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    D.G_mul_G, D.G_mul_J, D.J_mul_G, D.J_mul_J]
  ext X Y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul]
  ring

/-- The annihilation identity `hcCZero` of `hc:lem:Connor`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem C_mul_incMatrix_transpose :
    D.C * (D.incMatrix.map (Int.castRingHom ℚ)).transpose = 0 := by
  let N := D.incMatrix.map (Int.castRingHom ℚ)
  have hNN : N * N.transpose =
      (5 : ℚ) • (1 : Matrix P P ℚ) + (2 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) :=
    D.incMatrix_rat_mul_transpose_15_5_2
  have hNJ : N.transpose * Matrix.of (fun _ _ ↦ (1 : ℚ)) =
      (5 : ℚ) • (Matrix.of (fun _ _ ↦ (1 : ℚ)) : Matrix B P ℚ) := by
    ext X p
    change (∑ q, (D.incMatrix q X : ℚ) * 1) = 5 * 1
    simp only [mul_one]
    exact_mod_cast D.incMatrix_col_sum X
  have hJN : (Matrix.of (fun _ _ ↦ (1 : ℚ)) : Matrix B B ℚ) * N.transpose =
      (7 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ)) := by
    ext X p
    change (∑ Y, (1 : ℚ) * D.incMatrix p Y) = 7 * 1
    simp only [one_mul, mul_one]
    exact_mod_cast D.incMatrix_row_sum p
  change ((35 : ℚ) • (1 : Matrix B B ℚ) - (7 : ℚ) • (N.transpose * N) +
    (10 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ))) * N.transpose = 0
  rw [Matrix.add_mul, Matrix.sub_mul]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
    hNN, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_one, hNJ, hJN]
  ext X p
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.of_apply, smul_eq_mul]
  ring

/-- The sum-of-squares identity `hcRankQuad` ([CGSS], Remark 5.12). -/
theorem C_quadratic_identity (x : B → ℚ) :
    35 * (x ⬝ᵥ (D.C *ᵥ x)) = (D.C *ᵥ x) ⬝ᵥ (D.C *ᵥ x) := by
  rw [← Matrix.dotProduct_transpose_mulVec D.C x (D.C *ᵥ x), D.C_transpose,
    Matrix.mulVec_mulVec,
    D.C_mul_C, Matrix.smul_mulVec, dotProduct_smul]
  rfl

/-- The quadratic inequality `hcRankNonneg` of `hc:lem:rank`
([CGSS], Remark 5.12 and Example 5.13), proved over `ℚ`. -/
theorem C_quadratic_nonneg (x : B → ℚ) : 0 ≤ x ⬝ᵥ (D.C *ᵥ x) := by
  have h : 0 ≤ (D.C *ᵥ x) ⬝ᵥ (D.C *ᵥ x) :=
    Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg _)
  rw [← D.C_quadratic_identity] at h
  linarith

/-- Full row rank of the incidence matrix (`hcRankDet`, `hcRankN`;
[CGSS], Remark 5.12). -/
theorem rank_incMatrix_rat : (D.incMatrix.map (Int.castRingHom ℚ)).rank = 15 := by
  have hdet : ((D.incMatrix.map (Int.castRingHom ℚ)) *
      (D.incMatrix.map (Int.castRingHom ℚ)).transpose).det ≠ 0 := by
    rw [D.incMatrix_rat_mul_transpose_15_5_2,
      Matrix.det_smul_one_add_smul_J (by rw [D.card_points]; decide) 5 2 (by norm_num)]
    rw [D.card_points]
    norm_num
  have h := Matrix.rank_of_det_ne_zero hdet
  simpa only [Matrix.rank_self_mul_transpose, D.card_points] using h

/-- Connor's rank bound `hcRankBound` of `hc:lem:rank`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem rank_C_le_six : D.C.rank ≤ 6 := by
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero D.C_mul_incMatrix_transpose
  rw [Matrix.rank_transpose, D.rank_incMatrix_rat, D.card_blocks] at h
  omega

variable {U : Type*}

/-- A Gram factorization of each labelled principal matrix (`hcPrinValue`;
[CGSS], Remark 5.12). It gives the same quadratic value as extending by zero. -/
theorem C_submatrix_gram (e : U ↪ B) :
    (D.C.submatrix id e).transpose * D.C.submatrix id e =
      (35 : ℚ) • D.C.submatrix e e := by
  have hT : (D.C.submatrix id e).transpose = D.C.submatrix e id := by
    ext u X
    exact congrFun (congrFun D.C_transpose (e u)) X
  rw [hT]
  ext u w
  exact congrFun (congrFun D.C_mul_C (e u)) (e w)

variable [Fintype U]

/-- Nonnegative quadratic values for a labelled principal matrix, `hcPrinValue` of
`hc:lem:principal` ([CGSS], Remark 5.12). The injection is bundled as an embedding. -/
theorem C_submatrix_quadratic_nonneg (e : U ↪ B) (x : U → ℚ) :
    0 ≤ x ⬝ᵥ (D.C.submatrix e e *ᵥ x) := by
  let A := D.C.submatrix id e
  have h := Matrix.dotProduct_transpose_mulVec A x (A *ᵥ x)
  rw [Matrix.mulVec_mulVec, D.C_submatrix_gram e, Matrix.smul_mulVec, dotProduct_smul] at h
  have hn : 0 ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg _)
  change (35 : ℚ) * (x ⬝ᵥ (D.C.submatrix e e *ᵥ x)) = _ at h
  linarith

/-- The rank bound for principal matrices, `hcPrinRank` of `hc:lem:principal`
([CGSS], Remark 5.12). -/
theorem rank_C_submatrix_le_six (e : U ↪ B) : (D.C.submatrix e e).rank ≤ 6 :=
  (Matrix.rank_submatrix_le D.C e e).trans D.rank_C_le_six

/-- Every principal matrix on at least seven distinct labels is singular,
`hcPrinSingular` of `hc:lem:principal` ([CGSS], Remark 5.12). -/
theorem det_C_submatrix_eq_zero [DecidableEq U] (e : U ↪ B) (hU : 7 ≤ Fintype.card U) :
    (D.C.submatrix e e).det = 0 := by
  by_contra hdet
  have hrank := Matrix.rank_of_det_ne_zero hdet
  have h := D.rank_C_submatrix_le_six e
  rw [hrank] at h
  omega

end Design
