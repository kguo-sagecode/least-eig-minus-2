/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Extension

/-!
# The integral Hall–Connor matrix

The products `hc:lem:extension-products` and the matrix form `hc:thm:matrix`
of Hall–Connor ([CGSS], Remark 5.12 and Example 5.13).
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- The old–new incidence product `hcProductsNT` ([CGSS], Remark 5.12). -/
theorem incMatrix_mul_sixCliqueIncMatrix :
    D.incMatrix * D.sixCliqueIncMatrix =
      (2 : ℤ) • Matrix.of (fun _ _ ↦ (1 : ℤ)) := by
  ext p S
  have hm (X : B) : D.incMatrix p X * D.sixCliqueIncMatrix X S =
      if X ∈ S.1 ∧ p ∈ D.block X then (1 : ℤ) else 0 := by
    by_cases hX : X ∈ S.1 <;> by_cases hp : p ∈ D.block X <;>
      simp [incMatrix, sixCliqueIncMatrix, hX, hp]
  have he : Finset.univ.filter (fun X ↦ X ∈ S.1 ∧ p ∈ D.block X) =
      S.1.filter (fun X ↦ p ∈ D.block X) := by ext X; simp
  simp [Matrix.mul_apply, hm, he, D.card_blocksThrough_in_sixClique S.2 p]

/-- The new-point Gram matrix, `hcProductsTTDiag`–`hcProductsTT`
([CGSS], Remark 5.12). -/
theorem sixCliqueIncMatrix_transpose_mul :
    D.sixCliqueIncMatrix.transpose * D.sixCliqueIncMatrix =
      (5 : ℤ) • (1 : Matrix D.SixClique D.SixClique ℤ) +
        Matrix.of (fun _ _ ↦ (1 : ℤ)) := by
  ext S T
  have hm (X : B) : D.sixCliqueIncMatrix X S * D.sixCliqueIncMatrix X T =
      if X ∈ S.1 ∩ T.1 then (1 : ℤ) else 0 := by
    by_cases hS : X ∈ S.1 <;> by_cases hT : X ∈ T.1 <;>
      simp [sixCliqueIncMatrix, hS, hT]
  have he : Finset.univ.filter (fun X ↦ X ∈ S.1 ∩ T.1) = S.1 ∩ T.1 := by
    ext X
    simp
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hm, Finset.sum_boole,
    he, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  by_cases hST : S = T
  · subst T
    simp [((D.mem_sixCliques S.1).mp S.2).card_eq]
  · have hne : S.1 ≠ T.1 := fun h ↦ hST (Subtype.ext h)
    simp [hST, D.sixClique_inter_card S.2 T.2 hne]

/-- The four blocks of the integral extended incidence product, `hcProductsOO`–`hcProductsNN`
of `hc:lem:extension-products` ([CGSS], Remark 5.12 and Example 5.13). -/
theorem hallConnorIncMatrix_mul_transpose :
    D.hallConnorIncMatrix * D.hallConnorIncMatrix.transpose =
      (5 : ℤ) • (1 : Matrix (P ⊕ D.SixClique) (P ⊕ D.SixClique) ℤ) +
        (2 : ℤ) • Matrix.of (fun _ _ ↦ (1 : ℤ)) := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_option,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have h := congrFun (congrFun D.incMatrix_mul_transpose_15_5_2 p) q
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul] at h
      simpa [hallConnorIncMatrix] using h
    | inr S =>
      have h := congrFun (congrFun D.incMatrix_mul_sixCliqueIncMatrix p) S
      simpa [hallConnorIncMatrix, Matrix.mul_apply] using h
  | inr S =>
    cases q with
    | inl q =>
      have h := congrFun (congrFun D.incMatrix_mul_sixCliqueIncMatrix q) S
      simpa [hallConnorIncMatrix, Matrix.mul_apply, mul_comm] using h
    | inr T =>
      have h := congrFun (congrFun D.sixCliqueIncMatrix_transpose_mul S) T
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul] at h
      simp only [hallConnorIncMatrix, Sum.inr.injEq, mul_one]
      linarith only [h]

include D in
/-- Hall–Connor at `k = 5`, in the integral matrix form `hc:thm:matrix`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem hall_connor : ∃ M : Matrix (Fin 22) (Fin 22) ℤ,
    M * M.transpose = (5 : ℤ) • 1 + (2 : ℤ) • Matrix.of (fun _ _ ↦ (1 : ℤ)) := by
  let a : Fin 22 ≃ P ⊕ D.SixClique :=
    (Fintype.equivFinOfCardEq D.hallConnorBlocks_parameters.1).symm
  let b : Fin 22 ≃ Option B :=
    (Fintype.equivFinOfCardEq D.hallConnorBlocks_parameters.2.1).symm
  refine ⟨D.hallConnorIncMatrix.submatrix a b, ?_⟩
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    D.hallConnorIncMatrix_mul_transpose]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  simp

end Design
