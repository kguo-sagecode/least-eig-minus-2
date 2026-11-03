/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.CertificateSylvester
import LineGraphs.Spectral.Gram

/-! # Positive semidefiniteness certified by integer matrices

Definition `def:certificate` (Definition 3.2) and Lemma `lem:certificate` (Lemma 3.3) of [Exc].
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
  {M : Matrix V V ℤ} {B : Finset V}

omit [Fintype V] [DecidableEq V] in
-- Definition 3.2 [Exc]
/-- The ordering condition of `def:certificate` (Definition 3.2) of [Exc] is equivalent
to positive definiteness of the real principal matrix. -/
theorem certificate_positive_iff (hM : M.IsSymm) :
    (∃ e : Fin B.card ≃ B,
      ((M.certificateMatrix B).submatrix e e).HasPositiveLeadingMinors) ↔
    ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ)).PosDef := by
  have hs : (M.certificateMatrix B).IsSymm := hM.submatrix _
  constructor
  · rintro ⟨e, he⟩
    have hp := (positive_leading_minors_iff_posDef_map _ (hs.submatrix e)).mp he
    have hp' := hp.submatrix e.symm.injective
    convert hp' using 1
    ext i j
    simp
  · intro hp
    let e : Fin B.card ≃ B := (Finset.equivFin B).symm
    refine ⟨e, (positive_leading_minors_iff_posDef_map _ (hs.submatrix e)).mpr ?_⟩
    simpa only [submatrix_map] using hp.submatrix e.injective

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: the principal matrix of a certificate
is positive definite. -/
theorem IsGramCertificate.posDef (hB : M.IsGramCertificate B) (hM : M.IsSymm) :
    ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ)).PosDef :=
  (certificate_positive_iff hM).mp hB.positive

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: a certificate determinant is positive,
including the determinant one of the empty principal matrix. -/
theorem IsGramCertificate.det_pos (hB : M.IsGramCertificate B) (hM : M.IsSymm) :
    0 < M.certificateDet B := by
  have h := (hB.posDef hM).det_pos
  rw [← Int.cast_det] at h
  exact_mod_cast h

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- The real cast of the exact identity in `lem:certificate` (Lemma 3.3) of [Exc]. -/
theorem IsGramCertificate.identity_map (hB : M.IsGramCertificate B) :
    ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ)).det • M.map (Int.cast : ℤ → ℝ) =
      (M.map (Int.cast : ℤ → ℝ)).submatrix id (Subtype.val : B → V) *
      ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ)).adjugate *
      (M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id := by
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have h := congrArg (fun A : Matrix V V ℤ => A.map f) hB.identity
  have hsmul : ((M.certificateDet B) • M).map f =
      f (M.certificateDet B) • M.map f := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((M.certificateDet B) • M).map f = _ at h
  rw [hsmul, Matrix.map_mul, Matrix.map_mul] at h
  have hadj : (M.certificateMatrix B).adjugate.map f =
      ((M.certificateMatrix B).map f).adjugate := f.map_adjugate _
  change f (M.certificateDet B) • M.map f =
    (M.submatrix id (Subtype.val : B → V)).map f *
      (M.certificateMatrix B).adjugate.map f *
      (M.submatrix (Subtype.val : B → V) id).map f at h
  rw [hadj] at h
  change ((M.certificateMatrix B).det : ℝ) • M.map (Int.cast : ℤ → ℝ) = _ at h
  rw [Int.cast_det] at h
  simpa only [submatrix_map, f, Int.coe_castRingHom] using h

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- The inverse factorization in the proof of `lem:certificate` (Lemma 3.3) of [Exc]. -/
theorem IsGramCertificate.factorization (hB : M.IsGramCertificate B) (hM : M.IsSymm) :
    M.map (Int.cast : ℤ → ℝ) =
      (M.map (Int.cast : ℤ → ℝ)).submatrix id (Subtype.val : B → V) *
      ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ))⁻¹ *
      (M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id := by
  rw [inv_def, Ring.inverse_eq_inv, Matrix.mul_smul, Matrix.smul_mul,
    ← hB.identity_map, smul_smul, inv_mul_cancel₀ (hB.posDef hM).det_pos.ne', one_smul]

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: a certificate certifies positive
semidefiniteness of the real matrix. -/
theorem IsGramCertificate.posSemidef [Finite V] (hB : M.IsGramCertificate B) (hM : M.IsSymm) :
    (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  have hp := (hB.posDef hM).inv.posSemidef.conjTranspose_mul_mul_same
    ((M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id)
  have ht : ((M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id)ᴴ =
      (M.map (Int.cast : ℤ → ℝ)).submatrix id (Subtype.val : B → V) := by
    ext i j
    simp only [conjTranspose_apply, submatrix_apply, id_eq, map_apply, star_trivial]
    rw [hM.apply]
  rw [ht, ← hB.factorization hM] at hp
  exact hp

-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: every certificate has rank-many vertices. -/
theorem IsGramCertificate.card_eq_rank (hB : M.IsGramCertificate B) (hM : M.IsSymm) :
    B.card = (M.map (Int.cast : ℤ → ℝ)).rank := by
  apply le_antisymm
  · have hr := rank_submatrix_le (M.map (Int.cast : ℤ → ℝ))
      (Subtype.val : B → V) (Subtype.val : B → V)
    have he : ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ)).rank = B.card := by
      simpa using rank_of_isUnit _ (hB.posDef hM).isUnit
    change ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ)).rank ≤ _ at hr
    rw [he] at hr
    exact hr
  · calc
      (M.map (Int.cast : ℤ → ℝ)).rank =
          ((M.map (Int.cast : ℤ → ℝ)).submatrix id (Subtype.val : B → V) *
            ((M.certificateMatrix B).map (Int.cast : ℤ → ℝ))⁻¹ *
            (M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id).rank :=
        congrArg rank (hB.factorization hM)
      _ ≤ ((M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id).rank :=
        rank_mul_le_right _ _
      _ ≤ B.card := by
        simpa using rank_le_card_height
          ((M.map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : B → V) id)

end Matrix
