/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination

/-!
# The leaf determinant expansion

`lem:rem-leaf-det` of the blueprint for Remark 3.11 of [CGSS]: if the row and the column
of `v` vanish off the diagonal except at `w`, and `M v v = 2`, then
`det M = 2 det M₋ᵥ - M v w * M w v * det M₋ᵥ,₋w`, for principal deletions `M₋ᵥ` and
`M₋ᵥ,₋w`. The proof splits the row of `v` by multilinearity: the part `2 eᵥ` gives the
permutations fixing `v` (`rldfixed`), and the part at `w` those interchanging `v` and `w`
(`rldmoving`, `rldsum`), with the sign of the transposition.
-/

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A row vanishing off the diagonal, in step `rldfixed` of Remark 3.11: the determinant is
the diagonal entry times the principal minor. -/
theorem det_eq_mul_det_of_row_eq_zero (A : Matrix n n R) (v : n)
    (h : ∀ j, j ≠ v → A v j = 0) :
    A.det = A v v * (A.submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val).det := by
  rw [A.twoBlockTriangular_det (fun i ↦ i ≠ v) (fun i hi j hj ↦ by
    rw [not_not] at hi
    subst hi
    exact h j hj), mul_comm]
  congr 1
  have : Subsingleton {i // ¬i ≠ v} :=
    ⟨fun a b ↦ Subtype.ext ((not_not.mp a.2).trans (not_not.mp b.2).symm)⟩
  exact det_eq_elem_of_subsingleton _ (⟨v, not_not.mpr rfl⟩ : {i // ¬i ≠ v})

/-- A column vanishing off the diagonal, the transpose of
`det_eq_mul_det_of_row_eq_zero` (step `rldcolumn` of Remark 3.11). -/
theorem det_eq_mul_det_of_col_eq_zero (A : Matrix n n R) (v : n)
    (h : ∀ i, i ≠ v → A i v = 0) :
    A.det = A v v * (A.submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val).det := by
  rw [← det_transpose, Aᵀ.det_eq_mul_det_of_row_eq_zero v (fun j hj ↦ h j hj), transpose_apply,
    ← transpose_submatrix, det_transpose]

-- Remark 3.11, lem:rem-leaf-det
/-- The leaf determinant expansion, `lem:rem-leaf-det` of Remark 3.11 of [CGSS]: for
`v ≠ w` with `M v v = 2`, and the row and column of `v` zero off the diagonal except at
`w`, `det M = 2 det M₋ᵥ - p det M₋ᵥ,₋w` with `p = M v w * M w v`. -/
theorem det_eq_of_leaf (M : Matrix n n R) {v w : n} (hvw : v ≠ w) (hv : M v v = 2)
    (hrow : ∀ j, j ≠ v → j ≠ w → M v j = 0) (hcol : ∀ i, i ≠ v → i ≠ w → M i v = 0) :
    M.det = 2 * (M.submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val).det -
      M v w * M w v *
        (M.submatrix (Subtype.val : {i // i ≠ v ∧ i ≠ w} → n) Subtype.val).det := by
  -- the row of `v` is `2 eᵥ + M v w e_w`
  have hrowv : M v = Pi.single v 2 + M v w • Pi.single w 1 := by
    funext j
    by_cases hj : j = v
    · subst hj
      simp [hv, hvw]
    by_cases hj' : j = w
    · subst hj'
      simp [hj]
    · simp [hj, hj', hrow j hj hj']
  have hsplit : M.det = (M.updateRow v (Pi.single v 2)).det +
      M v w * (M.updateRow v (Pi.single w 1)).det := by
    conv_lhs => rw [← M.updateRow_eq_self v, hrowv]
    rw [det_updateRow_add, det_updateRow_smul]
  -- step `rldfixed`
  have hfixed : (M.updateRow v (Pi.single v 2)).det =
      2 * (M.submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val).det := by
    rw [det_eq_mul_det_of_row_eq_zero _ v (fun j hj ↦ by simp [hj])]
    congr 1
    · simp
    · congr 1
      ext i j
      simp [updateRow_ne i.2]
  -- step `rldcolumn`: the column of `v` in the second summand is `M w v e_w`
  have hcolQ : (fun i ↦ M.updateRow v (Pi.single w 1) i v) = M w v • Pi.single w 1 := by
    funext i
    by_cases hi : i = v
    · subst hi
      simp [hvw]
    by_cases hi' : i = w
    · subst hi'
      simp [updateRow_ne hi]
    · simp [updateRow_ne hi, hi', hcol i hi hi']
  have hmove : (M.updateRow v (Pi.single w 1)).det =
      M w v * ((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).det := by
    conv_lhs => rw [← (M.updateRow v (Pi.single w 1)).updateCol_eq_self v, hcolQ]
    rw [det_updateCol_smul]
  -- step `rldrow`: interchange the rows of `v` and `w`
  have hswap : (((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).submatrix
      (Equiv.swap v w) id).det =
      -((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).det := by
    rw [det_permute, Equiv.Perm.sign_swap hvw]
    simp
  have hPcol : ∀ i, i ≠ v →
      ((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).submatrix
        (Equiv.swap v w) id i v = 0 := by
    intro i hi
    simp [Equiv.swap_apply_eq_iff, hi]
  have h1 := det_eq_mul_det_of_col_eq_zero _ v hPcol
  have hPvv : ((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).submatrix
      (Equiv.swap v w) id v v = 1 := by
    simp
  let w' : {i // i ≠ v} := ⟨w, hvw.symm⟩
  have hNrow : ∀ j, j ≠ w' →
      (((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).submatrix
        (Equiv.swap v w) id).submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val w' j = 0 := by
    intro j hj
    have hjw : (j : n) ≠ w := fun h ↦ hj (Subtype.ext h)
    simp [w', updateCol_ne j.2, hjw]
  have h2 := det_eq_mul_det_of_row_eq_zero _ w' hNrow
  have hNww : (((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).submatrix
      (Equiv.swap v w) id).submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val w' w' = 1 := by
    simp [w', updateCol_ne hvw.symm]
  let e : {i // i ≠ v ∧ i ≠ w} ≃ {j : {i // i ≠ v} // j ≠ w'} :=
    { toFun := fun i ↦ ⟨⟨i.1, i.2.1⟩, fun h ↦ i.2.2 (congrArg Subtype.val h)⟩
      invFun := fun j ↦ ⟨j.1.1, j.1.2, fun h ↦ j.2 (Subtype.ext h)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have h3 : ((((M.updateRow v (Pi.single w 1)).updateCol v (Pi.single w 1)).submatrix
      (Equiv.swap v w) id).submatrix (Subtype.val : {i // i ≠ v} → n) Subtype.val).submatrix
        (Subtype.val : {j : {i // i ≠ v} // j ≠ w'} → {i // i ≠ v}) Subtype.val =
      (M.submatrix (Subtype.val : {i // i ≠ v ∧ i ≠ w} → n) Subtype.val).submatrix e.symm
        e.symm := by
    ext i j
    have hi : ((i : {i // i ≠ v}) : n) ≠ v ∧ ((i : {i // i ≠ v}) : n) ≠ w := (e.symm i).2
    have hj : ((j : {i // i ≠ v}) : n) ≠ v ∧ ((j : {i // i ≠ v}) : n) ≠ w := (e.symm j).2
    simp [e, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, updateCol_ne hj.1, updateRow_ne hi.1]
  have hfin := hswap
  rw [h1, hPvv, one_mul, h2, hNww, one_mul, h3, det_submatrix_equiv_self] at hfin
  rw [hsplit, hfixed, hmove]
  linear_combination (M v w * M w v) * hfin

end Matrix
