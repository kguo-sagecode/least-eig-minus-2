/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.CertificateDefs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Sylvester's criterion for integer certificates

The ordering independence following Definition `def:certificate` (Definition 3.2) of [Exc].
The reverse direction of Sylvester's criterion is proved by Schur-complement induction.
-/

namespace Matrix

-- Definition 3.2 [Exc]
/-- Sylvester's criterion used after `def:certificate` (Definition 3.2) of [Exc]:
a real symmetric matrix with positive leading principal minors is positive definite. -/
theorem posDef_of_positive_leading_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (hpos : M.HasPositiveLeadingMinors) : M.PosDef := by
  induction n with
  | zero =>
    exact PosDef.of_dotProduct_mulVec_pos hM (fun x hx => (hx (Subsingleton.elim _ _)).elim)
  | succ n ih =>
    let A := M.submatrix Fin.castSucc Fin.castSucc
    have hA : A.PosDef := ih A (hM.submatrix _) (by
      intro k hk
      convert hpos k (hk.trans (Nat.le_succ n)) using 1
      congr 1)
    let := hA.isUnit.invertible
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => M i.castSucc (Fin.last n)
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => M (Fin.last n) (Fin.last n)
    have hblock : fromBlocks A B Bᴴ D = M.submatrix e e := by
      ext (i | i) (j | j)
      · rfl
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      · have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change M j.castSucc (Fin.last n) = M (Fin.last n) j.castSucc
        simpa only [conjTranspose_apply, star_trivial]
          using congrFun (congrFun hM.eq (Fin.last n)) (Fin.castSucc j)
      · have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst i
        subst j
        rfl
    have hdet : 0 < M.det := by simpa using hpos (n + 1) le_rfl
    have hschur : 0 < (D - Bᴴ * A⁻¹ * B).det := by
      have heq := det_fromBlocks₁₁ A B Bᴴ D
      rw [hblock, det_submatrix_equiv_self, invOf_eq_nonsing_inv] at heq
      exact (mul_pos_iff_of_pos_left hA.det_pos).mp (heq ▸ hdet)
    have hschurPos : (D - Bᴴ * A⁻¹ * B).PosSemidef := by
      have heq : D - Bᴴ * A⁻¹ * B = diagonal (fun _ => (D - Bᴴ * A⁻¹ * B) 0 0) := by
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst i
        subst j
        simp
      rw [heq]
      exact PosSemidef.diagonal (fun _ => (by simpa [det_fin_one] using hschur.le))
    have hp := (PosDef.fromBlocks₁₁ B D hA).mpr hschurPos
    rw [hblock, posSemidef_submatrix_equiv] at hp
    exact hp.posDef_iff_det_ne_zero.mpr hdet.ne'

-- Definition 3.2 [Exc]
/-- Sylvester's criterion used after `def:certificate` (Definition 3.2) of [Exc]:
positive definiteness is equivalent to positivity of the leading principal minors. -/
theorem positive_leading_minors_iff_posDef {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) : M.HasPositiveLeadingMinors ↔ M.PosDef := by
  refine ⟨posDef_of_positive_leading_minors M hM, fun h k hk => ?_⟩
  exact (h.submatrix (Fin.castLE_injective hk)).det_pos

-- Definition 3.2 [Exc]
/-- The exact integer version of Sylvester's criterion following `def:certificate`
(Definition 3.2) of [Exc]. Positivity is tested on the real cast. -/
theorem positive_leading_minors_iff_posDef_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : M.IsSymm) :
    M.HasPositiveLeadingMinors ↔ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hs : (M.map (Int.cast : ℤ → ℝ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map, hM.eq]
  rw [← positive_leading_minors_iff_posDef _ hs]
  unfold HasPositiveLeadingMinors
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  rw [submatrix_map, ← Int.cast_det]
  exact Int.cast_pos.symm

-- Definition 3.2 [Exc]
/-- The first certificate condition in `def:certificate` (Definition 3.2) of [Exc]
does not depend on the ordering of the principal matrix. -/
theorem positive_leading_minors_order_independent {V : Type*}
    (G : Matrix V V ℤ) (hG : G.IsSymm) {r : ℕ} (e f : Fin r ≃ V) :
    (G.submatrix e e).HasPositiveLeadingMinors ↔
      (G.submatrix f f).HasPositiveLeadingMinors := by
  rw [positive_leading_minors_iff_posDef_map _ (hG.submatrix _),
    positive_leading_minors_iff_posDef_map _ (hG.submatrix _)]
  constructor
  · intro h
    have h' := h.submatrix (e.symm.injective.comp f.injective)
    simpa only [submatrix_map, submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply]
      using h'
  · intro h
    have h' := h.submatrix (f.symm.injective.comp e.injective)
    simpa only [submatrix_map, submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply]
      using h'

end Matrix
