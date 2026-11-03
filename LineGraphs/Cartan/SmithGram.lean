/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Converse
import LineGraphs.Spectral.Gram

/-!
# Deleting a vertex from a Smith Gram realization

The every-deletion basis clause of Corollary D (Theorem 3.8) in the Remark 3.11
blueprint. This also completes the deletion clause of computation C17, including
the marked vertices, for all ranks rather than just the sampled Sage ranks.
The last section gives the other half of C17: each Smith graph has largest eigenvalue two.
-/

open Matrix Module
open scoped InnerProductSpace

namespace WeightedGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The affine Gram matrix is positive semidefinite at spectral threshold two
(Corollary D, Remark 3.11; C17). -/
theorem posSemidef_two_sub_of_maxRayleigh_eq_two (X : WeightedGraph ι)
    (hmax : maxRayleigh X.isHermitian = 2) :
    ((2 : ℝ) • (1 : Matrix ι ι ℝ) - X.weights).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    ((isHermitian_one.smul (by rfl)).sub X.isHermitian)
  intro x
  have hb := X.isHermitian.quadratic_le_maxRayleigh x
  rw [hmax] at hb
  simpa only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr hb

/-- Every proper one-vertex deletion of `2I - B` is positive definite for a connected
weighted graph with maximum eigenvalue two (Corollary D, Remark 3.11; C17). -/
theorem posDef_two_sub_delete (X : WeightedGraph ι) (hconn : X.support.Connected)
    (hmax : maxRayleigh X.isHermitian = 2) (i₀ : ι) :
    (((2 : ℝ) • (1 : Matrix ι ι ℝ) - X.weights).submatrix
      (fun i : {i : ι // i ≠ i₀} ↦ i.val) (fun i : {i : ι // i ≠ i₀} ↦ i.val)).PosDef := by
  classical
  let Q : Matrix ι ι ℝ := (2 : ℝ) • 1 - X.weights
  have hQ : Q.PosSemidef := X.posSemidef_two_sub_of_maxRayleigh_eq_two hmax
  obtain ⟨w, hw, _, hew⟩ := X.exists_pos_max_eigenvector hconn
  rw [hmax] at hew
  let e : {i : ι // i ≠ i₀} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub := hQ.submatrix e
  apply PosDef.of_dotProduct_mulVec_pos hsub.isHermitian
  intro x hx
  apply lt_of_le_of_ne (hsub.dotProduct_mulVec_nonneg x)
  intro hz
  let y := extendByZero e x
  have hzero : y ⬝ᵥ (Q *ᵥ y) = 0 := by
    rw [quadratic_extendByZero]
    simpa only [star_trivial] using hz.symm
  have hker := (hQ.dotProduct_mulVec_zero_iff y).mp (by simpa only [star_trivial] using hzero)
  have hey : X.weights *ᵥ y = (2 : ℝ) • y := by
    simpa only [Q, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero, eq_comm] using hker
  have hsupport : X.isHermitian.supportGraph.Connected := by
    rwa [← X.support_eq_supportGraph]
  obtain ⟨c, hc⟩ := X.isHermitian.eigenvector_eq_smul_of_pos X.nonneg hsupport hw hew hey
  have hy : y i₀ = 0 := by
    apply extendByZero_eq_zero
    rintro ⟨j, hj⟩
    exact j.property hj
  have hc0 : c = 0 := by
    have h := congr_fun hc i₀
    rw [hy] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (hw i₀).ne'
  apply hx
  funext j
  have h := congr_fun hc (e j)
  simpa only [y, extendByZero_apply, hc0, zero_smul, Pi.zero_apply] using h

/-- In every realization of an affine Gram matrix, every single deletion is a basis
of the full realizing span (Corollary D, Remark 3.11; computation C17). -/
theorem gram_delete_basis (X : WeightedGraph ι) (hconn : X.support.Connected)
    (hmax : maxRayleigh X.isHermitian = 2)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (hgram : gram ℝ v = (2 : ℝ) • 1 - X.weights) (i₀ : ι) :
    ∃ b : Basis {i : ι // i ≠ i₀} ℝ (Submodule.span ℝ (Set.range v)),
      ∀ i, (b i : E) = v i := by
  classical
  let v' : {i : ι // i ≠ i₀} → E := fun i ↦ v i
  have hli : LinearIndependent ℝ v' := by
    apply Matrix.linearIndependent_of_posDef_gram
    change ((gram ℝ v).submatrix Subtype.val Subtype.val).PosDef
    rw [hgram]
    exact X.posDef_two_sub_delete hconn hmax i₀
  obtain ⟨w, hw, _, hew⟩ := X.exists_pos_max_eigenvector hconn
  rw [hmax] at hew
  have hker : gram ℝ v *ᵥ w = 0 := by
    rw [hgram, sub_mulVec, smul_mulVec, one_mulVec, hew, sub_self]
  have hrelation : ∑ i, w i • v i = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← star_dotProduct_gram_mulVec, hker, dotProduct_zero]
  let S := Submodule.span ℝ (Set.range v')
  have hmem (i : ι) (hi : i ≠ i₀) : v i ∈ S :=
    Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hsum : ∑ i ∈ Finset.univ.erase i₀, w i • v i ∈ S := by
    apply Submodule.sum_mem
    intro i hi
    exact S.smul_mem _ (hmem i (Finset.mem_erase.mp hi).1)
  have hsumzero : w i₀ • v i₀ + ∑ i ∈ Finset.univ.erase i₀, w i • v i = 0 := by
    exact (Finset.add_sum_erase Finset.univ (fun i ↦ w i • v i)
      (Finset.mem_univ i₀)).trans hrelation
  have hmem₀ : v i₀ ∈ S := by
    apply (S.smul_mem_iff (hw i₀).ne').mp
    rw [eq_neg_of_add_eq_zero_left hsumzero]
    exact S.neg_mem hsum
  have hspan : Submodule.span ℝ (Set.range v') = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.val, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i = i₀
      · subst i; exact hmem₀
      · exact hmem i hi
  rw [← hspan]
  exact ⟨Basis.span hli, fun i ↦ Basis.coe_span_apply hli i⟩

/-- The affine Gram matrix has rank one less than its order
(Corollary D, Remark 3.11; C17). -/
theorem rank_two_sub_eq_card_sub_one (X : WeightedGraph ι) (hconn : X.support.Connected)
    (hmax : maxRayleigh X.isHermitian = 2) :
    ((2 : ℝ) • (1 : Matrix ι ι ℝ) - X.weights).rank = Fintype.card ι - 1 := by
  classical
  let Q : Matrix ι ι ℝ := (2 : ℝ) • 1 - X.weights
  have hQ := X.posSemidef_two_sub_of_maxRayleigh_eq_two hmax
  obtain ⟨v, hv⟩ := hQ.exists_gram_euclideanSpace (r := Q.rank) le_rfl
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨b, _⟩ := X.gram_delete_basis hconn hmax v hv i₀
  calc
    _ = finrank ℝ (Submodule.span ℝ (Set.range v)) := by
      rw [← hv, rank_gram_eq_finrank_span]
    _ = Fintype.card {i : ι // i ≠ i₀} := finrank_eq_card_basis b
    _ = Fintype.card ι - 1 := by
      simp

/-- A connected graph at spectral threshold two has a spanning Gram realization in
dimension `m-1`, with squared norms two (Corollary D, Remark 3.11; C17). -/
theorem exists_gram_card_sub_one (X : WeightedGraph ι) (hconn : X.support.Connected)
    (hmax : maxRayleigh X.isHermitian = 2) :
    ∃ v : ι → EuclideanSpace ℝ (Fin (Fintype.card ι - 1)),
      gram ℝ v = (2 : ℝ) • 1 - X.weights ∧
      Submodule.span ℝ (Set.range v) = ⊤ ∧ ∀ i, ⟪v i, v i⟫_ℝ = 2 := by
  have hr := X.rank_two_sub_eq_card_sub_one hconn hmax
  have hQ := X.posSemidef_two_sub_of_maxRayleigh_eq_two hmax
  obtain ⟨v, hv⟩ := hQ.exists_gram_euclideanSpace hr.le
  refine ⟨v, hv, ?_, ?_⟩
  · apply Submodule.eq_top_of_finrank_eq
    rw [← rank_gram_eq_finrank_span, hv, hr]
    simp
  · intro i
    have h := congr_fun (congr_fun hv i) i
    simpa [gram_apply, X.diag] using h

omit [Fintype ι] in
/-- The affine certificates already checked for C17 discharge every-deletion bases
through the general Gram theorem (Corollary D, Remark 3.11). -/
theorem IsAffineObstruction.gram_delete_basis [Finite ι] {X : WeightedGraph ι}
    (hX : X.IsAffineObstruction) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (hgram : gram ℝ v = (2 : ℝ) • 1 - X.weights) (i₀ : ι) :
    ∃ b : Basis {i : ι // i ≠ i₀} ℝ (Submodule.span ℝ (Set.range v)),
      ∀ i, (b i : E) = v i := by
  let _ := Fintype.ofFinite ι
  exact X.gram_delete_basis hX.connected hX.maxRayleigh_eq_two v hgram i₀

end WeightedGraph

namespace SimpleGraph

/-- Corollary D of Remark 3.11, the every-deletion basis clause of Theorem 3.8.
This includes the marked-vertex assertion of computation C17. -/
theorem smith_gram_delete_basis {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : SimpleGraph ι) [DecidableRel X.Adj] (hconn : X.Connected)
    (hmax : maxRayleigh (X.isHermitian_adjMatrix ℝ) = 2)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (hgram : gram ℝ v = (2 : ℝ) • 1 - X.adjMatrix ℝ) (i₀ : ι) :
    ∃ b : Basis {i : ι // i ≠ i₀} ℝ (Submodule.span ℝ (Set.range v)),
      ∀ i, (b i : E) = v i := by
  exact (WeightedGraph.unit X).gram_delete_basis (by simpa using hconn) hmax v hgram i₀

end SimpleGraph

/-! ### Computation C17: the Smith graphs have largest eigenvalue two -/

namespace WeightedGraph

variable {ι : Type*}

/-- A graph with weights in `{0,1}` is the unit graph of its support
(computation C17; Corollary D of Remark 3.11). -/
theorem unit_support_eq (X : WeightedGraph ι) [DecidableRel X.support.Adj]
    (h : ∀ i j, X.weights i j = 0 ∨ X.weights i j = 1) : unit X.support = X := by
  apply WeightedGraph.ext
  funext i j
  change X.support.adjMatrix ℝ i j = X.weights i j
  rw [SimpleGraph.adjMatrix_apply]
  by_cases hadj : X.support.Adj i j
  · simp only [hadj, ite_true]
    change 0 < X.weights i j at hadj
    rcases h i j with h | h <;> [(rw [h] at hadj; exact (lt_irrefl _ hadj).elim); exact h.symm]
  · simp only [hadj, ite_false]
    change ¬ 0 < X.weights i j at hadj
    rcases h i j with h | h <;> [exact h.symm; (rw [h] at hadj; norm_num at hadj)]

/-- The affine D graph has unit weights on its support
(computation C17; Corollary D of Remark 3.11). -/
theorem affineD_weights_eq_zero_or_one (ℓ : ℕ) (i j : Fin (ℓ - 4 + 1) ⊕ Fin 4) :
    (affineD ℓ).weights i j = 0 ∨ (affineD ℓ).weights i j = 1 := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [affineD, attachLeaves, path] <;> (try split_ifs) <;> simp

end WeightedGraph

namespace SimpleGraph

open WeightedGraph

/-- The affine A Smith graph (the cycle on `ℓ+1` vertices) has largest eigenvalue two
(computation C17; Theorem 3.8 as Corollary D of Remark 3.11). -/
theorem smithA_maxRayleigh (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    maxRayleigh ((smithA ℓ).isHermitian_adjMatrix ℝ) = 2 :=
  ((unit (smithA ℓ)).eigenvalue_eq_maxRayleigh_of_pos
    (by rw [support_unit]; exact smithA_connected ℓ) (fun _ ↦ one_pos)
    (smithA_mulVec_one ℓ hℓ)).symm

/-- The affine D Smith graph has unit weights (computation C17; Corollary D of Remark 3.11). -/
theorem unit_smithD (ℓ : ℕ) [DecidableRel (smithD ℓ).Adj] : unit (smithD ℓ) = affineD ℓ := by
  let _ : DecidableRel (affineD ℓ).support.Adj := ‹DecidableRel (smithD ℓ).Adj›
  exact (affineD ℓ).unit_support_eq (affineD_weights_eq_zero_or_one ℓ)

/-- The affine D Smith graph has largest eigenvalue two
(computation C17; Theorem 3.8 as Corollary D of Remark 3.11). -/
theorem smithD_maxRayleigh (ℓ : ℕ) [DecidableRel (smithD ℓ).Adj] :
    maxRayleigh ((smithD ℓ).isHermitian_adjMatrix ℝ) = 2 := by
  obtain ⟨hv, heig⟩ := affineD_eigenvector ℓ
  rw [← unit_smithD ℓ] at heig
  exact ((unit (smithD ℓ)).eigenvalue_eq_maxRayleigh_of_pos
    (by rw [support_unit]; exact affineD_connected ℓ) hv heig).symm

/-- The affine E₆ Smith graph has largest eigenvalue two (computation C17). -/
theorem smithE₆_maxRayleigh : maxRayleigh (smithE₆.isHermitian_adjMatrix ℝ) = 2 :=
  ((unit smithE₆).eigenvalue_eq_maxRayleigh_of_pos
    (by rw [support_unit]; exact armTree_connected _) smithE₆_eigenvector.1
    smithE₆_eigenvector.2).symm

/-- The affine E₇ Smith graph has largest eigenvalue two (computation C17). -/
theorem smithE₇_maxRayleigh : maxRayleigh (smithE₇.isHermitian_adjMatrix ℝ) = 2 :=
  ((unit smithE₇).eigenvalue_eq_maxRayleigh_of_pos
    (by rw [support_unit]; exact armTree_connected _) smithE₇_eigenvector.1
    smithE₇_eigenvector.2).symm

/-- The affine E₈ Smith graph has largest eigenvalue two (computation C17). -/
theorem smithE₈_maxRayleigh : maxRayleigh (smithE₈.isHermitian_adjMatrix ℝ) = 2 :=
  ((unit smithE₈).eigenvalue_eq_maxRayleigh_of_pos
    (by rw [support_unit]; exact armTree_connected _) smithE₈_eigenvector.1
    smithE₈_eigenvector.2).symm

end SimpleGraph
