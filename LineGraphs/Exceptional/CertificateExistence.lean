/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Certificate

/-! # Existence of integer Gram certificates

The converse and the independent-row assertion of `lem:certificate` (Lemma 3.3) of [Exc].
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
-- Lemma 3.3 [Exc]
/-- The Gram argument in `lem:certificate` (Lemma 3.3) of [Exc]: independent rows of a
positive semidefinite matrix select a positive definite principal matrix. -/
theorem PosSemidef.posDef_principal_of_linearIndependent_rows [Finite V] {A : Matrix V V ℝ}
    (hA : A.PosSemidef) (B : Finset V)
    (hi : LinearIndependent ℝ (fun b : B => A b)) :
    (A.submatrix (Subtype.val : B → V) Subtype.val).PosDef := by
  let := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := hA.exists_gram_euclideanSpace (le_refl A.rank)
  let L : EuclideanSpace ℝ (Fin A.rank) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun y u => ⟪y, x u⟫
      map_add' := by intros; ext; simp [inner_add_left]
      map_smul' := by intros; ext; simp [real_inner_smul_left] }
  have hix : LinearIndependent ℝ (fun b : B => x b) := by
    apply LinearIndependent.of_comp L
    convert hi using 1
    ext b u
    exact congrFun (congrFun hx b) u
  have hg : gram ℝ (fun b : B => x b) = A.submatrix (Subtype.val : B → V) Subtype.val := by
    ext b c
    exact congrFun (congrFun hx b) c
  rw [← hg]
  exact posDef_gram_of_linearIndependent hix

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- The row-span identity in the proof of `lem:certificate` (Lemma 3.3) of [Exc].
It does not require positivity or a nonsingular principal matrix. -/
theorem mul_adjugate_mul_eq_det_smul_of_row_span (A : Matrix V V ℝ) (B : Finset V)
    (hs : span ℝ (Set.range (fun b : B => A b)) = span ℝ (Set.range A)) :
    A.submatrix id (Subtype.val : B → V) *
        (A.submatrix (Subtype.val : B → V) Subtype.val).adjugate *
        A.submatrix (Subtype.val : B → V) id =
      (A.submatrix (Subtype.val : B → V) Subtype.val).det • A := by
  have hm (u : V) : A u ∈ span ℝ (Set.range (fun b : B => A b)) := by
    rw [hs]
    exact subset_span (Set.mem_range_self u)
  choose w hw using fun u => (mem_span_range_iff_exists_fun ℝ).mp (hm u)
  let W : Matrix V B ℝ := w
  have hprod : W * A.submatrix (Subtype.val : B → V) id = A := by
    ext u v
    change (∑ b : B, w u b * A b v) = A u v
    simpa only [Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using congrFun (hw u) v
  have hleft : W * A.submatrix (Subtype.val : B → V) Subtype.val =
      A.submatrix id (Subtype.val : B → V) := by
    ext u v
    change (∑ b : B, w u b * A b v) = A u v
    simpa only [Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using congrFun (hw u) v
  rw [← hleft, Matrix.mul_assoc W, mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hprod]

variable {M : Matrix V V ℤ} {B : Finset V}

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: any row basis of a positive
semidefinite integer matrix gives a certificate. -/
theorem isGramCertificate_of_row_basis [Finite V] (hM : M.IsSymm)
    (hp : (M.map (Int.cast : ℤ → ℝ)).PosSemidef)
    (hi : LinearIndependent ℝ (fun b : B => (M.map (Int.cast : ℤ → ℝ)) b))
    (hs : span ℝ (Set.range (fun b : B => (M.map (Int.cast : ℤ → ℝ)) b)) =
      span ℝ (Set.range (M.map (Int.cast : ℤ → ℝ)))) : M.IsGramCertificate B := by
  refine ⟨(certificate_positive_iff hM).mpr ?_, ?_⟩
  · exact hp.posDef_principal_of_linearIndependent_rows B hi
  · have heq := (mul_adjugate_mul_eq_det_smul_of_row_span
      (M.map (Int.cast : ℤ → ℝ)) B hs).symm
    let f : ℤ →+* ℝ := Int.castRingHom ℝ
    apply Matrix.map_injective (f := (f : ℤ → ℝ)) Int.cast_injective
    have hsmul : ((M.certificateDet B) • M).map f =
        f (M.certificateDet B) • M.map f := by
      ext i j
      simp only [map_apply, smul_apply, smul_eq_mul, map_mul]
    change ((M.certificateDet B) • M).map f = _
    dsimp only
    rw [hsmul, Matrix.map_mul, Matrix.map_mul]
    have hadj : (M.certificateMatrix B).adjugate.map f =
        ((M.certificateMatrix B).map f).adjugate := f.map_adjugate _
    change f (M.certificateDet B) • M.map f =
      (M.submatrix id (Subtype.val : B → V)).map f *
        (M.certificateMatrix B).adjugate.map f *
        (M.submatrix (Subtype.val : B → V) id).map f
    rw [hadj]
    simpa only [f, Int.coe_castRingHom, certificateDet, certificateMatrix,
      Int.cast_det, submatrix_map] using heq

-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: rank-many independent rows form a
certificate. Row independence is stated over the reals after casting the integer matrix. -/
theorem isGramCertificate_of_linearIndependent_rows (hM : M.IsSymm)
    (hp : (M.map (Int.cast : ℤ → ℝ)).PosSemidef)
    (hi : LinearIndependent ℝ (fun b : B => (M.map (Int.cast : ℤ → ℝ)) b))
    (hc : B.card = (M.map (Int.cast : ℤ → ℝ)).rank) : M.IsGramCertificate B := by
  apply isGramCertificate_of_row_basis hM hp hi
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_mono
    rintro _ ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rw [finrank_span_eq_card hi, Fintype.card_coe, hc, rank_eq_finrank_span_row]
    rfl

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: positive semidefinite symmetric
integer matrices have certificates. -/
theorem exists_isGramCertificate_of_posSemidef [Finite V] (hM : M.IsSymm)
    (hp : (M.map (Int.cast : ℤ → ℝ)).PosSemidef) : ∃ B, M.IsGramCertificate B := by
  classical
  let := Fintype.ofFinite V
  let A := M.map (Int.cast : ℤ → ℝ)
  obtain ⟨s, _, _, hspan, hi⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty ℝ A) (Set.empty_subset (Set.univ : Set V))
  let B := s.toFinset
  have hsi : LinearIndependent ℝ (fun b : B => A b) := by
    change LinearIndepOn ℝ A (B : Set V)
    simpa only [B, Set.coe_toFinset] using hi
  have hrange : Set.range (fun b : B => A b) = A '' s := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, by simpa only [B, Set.mem_toFinset] using b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, by simpa only [B, Set.mem_toFinset] using hb⟩, rfl⟩
  have hs : span ℝ (Set.range (fun b : B => A b)) = span ℝ (Set.range A) := by
    apply le_antisymm
    · apply span_mono
      rintro _ ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · apply span_le.mpr
      rintro _ ⟨u, rfl⟩
      have hu := hspan (Set.mem_image_of_mem A (Set.mem_univ u))
      rw [hrange]
      exact hu
  exact ⟨B, isGramCertificate_of_row_basis hM hp hsi hs⟩

omit [Fintype V] in
-- Lemma 3.3 [Exc]
/-- Lemma `lem:certificate` (Lemma 3.3) of [Exc]: a symmetric integer matrix has a
certificate if and only if its real cast is positive semidefinite. -/
theorem exists_isGramCertificate_iff_posSemidef [Finite V] (hM : M.IsSymm) :
    (∃ B, M.IsGramCertificate B) ↔ (M.map (Int.cast : ℤ → ℝ)).PosSemidef :=
  ⟨fun ⟨_, hB⟩ => hB.posSemidef hM, exists_isGramCertificate_of_posSemidef hM⟩

end Matrix

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj]

-- Definition 3.2 [Exc]
/-- The matrix used by `def:certificate` (Definition 3.2) of [Exc] is symmetric. -/
theorem integralGramMatrix_isSymm : X.integralGramMatrix.IsSymm := by
  change X.integralGramMatrix.transpose = X.integralGramMatrix
  simp [integralGramMatrix, Matrix.transpose_add, transpose_adjMatrix]

-- Lemma 3.3 [Exc]
/-- The graph specialization of `lem:certificate` (Lemma 3.3) of [Exc]. -/
theorem exists_integralGramMatrix_certificate_iff [Finite V] :
    (∃ B, X.integralGramMatrix.IsGramCertificate B) ↔
      ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosSemidef := by
  simpa using Matrix.exists_isGramCertificate_iff_posSemidef X.integralGramMatrix_isSymm

-- Theorem 3.6 [Exc]
/-- A certificate choice exists for `thm:growth` (Theorem 3.6) of [Exc], by
`lem:certificate` (Lemma 3.3). The growth theorem can use any such choice. -/
noncomputable def certificateChoice : CertificateChoice := by
  classical
  exact
    { indices := fun X => if h : ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosSemidef then
        Classical.choose (X.exists_integralGramMatrix_certificate_iff.mpr h) else ∅
      valid := fun X h => by
        rw [dite_eq_left h]
        exact Classical.choose_spec (X.exists_integralGramMatrix_certificate_iff.mpr h) }

-- Theorem 3.6 [Exc]
/-- A canonical form for `thm:growth` (Theorem 3.6) of [Exc], obtained by choosing
one representative of each isomorphism class. The growth theorem accepts any canonical form. -/
noncomputable def CanonicalForm.ofChoice : CanonicalForm :=
  let s : (n : ℕ) → Setoid (SimpleGraph (Fin n)) := fun _ =>
    { r := fun X Y => Nonempty (X ≃g Y)
      iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩,
        fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩ }
  { canon := fun {n} X => (Quotient.mk (s n) X).out
    iso := fun {n} X => Classical.choice (Quotient.mk_out (s := s n) X)
    eq_iff := fun {n} X Y => by
      constructor
      · intro h
        exact Quotient.exact (Quotient.out_inj.mp h)
      · intro h
        exact congrArg Quotient.out (Quotient.sound (s := s n) h) }

end SimpleGraph
