/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.AffineEigenvectors
import LineGraphs.Cartan.AffineDEigenvector
import LineGraphs.Cartan.AffineForkEigenvector
import LineGraphs.Cartan.Symmetrization

/-!
# Spectral exclusion of affine obstructions

The positive vectors in `lem:affine` give maximum Rayleigh value exactly two.
Monotonicity therefore excludes each obstruction from a finite Cartan support.
-/

namespace WeightedGraph

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reindexing preserves a specified eigenvector and its strict positivity. -/
theorem exists_pos_eigenvector_reindex (X : WeightedGraph ι) (e : ι ≃ κ) {t : ℝ}
    (h : ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ X.weights *ᵥ v = t • v) :
    ∃ v : κ → ℝ, (∀ i, 0 < v i) ∧ (X.reindex e).weights *ᵥ v = t • v := by
  obtain ⟨v, hv, heig⟩ := h
  refine ⟨v ∘ e.symm, fun i => hv _, ?_⟩
  change (Matrix.reindex e e X.weights) *ᵥ (v ∘ e.symm) = _
  simp only [Matrix.reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id,
    heig, Pi.smul_comp]

/-- Every affine obstruction has a strictly positive eigenvector with eigenvalue two. -/
theorem IsAffineObstruction.exists_pos_eigenvector {X : WeightedGraph ι}
    (hX : X.IsAffineObstruction) :
    ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ X.weights *ᵥ v = (2 : ℝ) • v := by
  cases hX with
  | cycle ℓ hℓ e h =>
    subst X
    apply exists_pos_eigenvector_reindex
    exact ⟨1, by intro _; norm_num, SimpleGraph.smithA_mulVec_one ℓ hℓ⟩
  | d ℓ _ e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, affineD_eigenvector ℓ⟩
  | e₆ e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, smithE₆_eigenvector⟩
  | e₇ e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, smithE₇_eigenvector⟩
  | e₈ e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, smithE₈_eigenvector⟩
  | ends m hm e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, endPath_eigenvector m hm⟩
  | fork k hk e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, fork_eigenvector k hk⟩
  | middle e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, middlePath_eigenvector⟩
  | triple e h =>
    subst X
    exact exists_pos_eigenvector_reindex _ e ⟨_, triplePath_eigenvector⟩

/-- Every affine obstruction has maximum Rayleigh quotient exactly two (`lem:affine`). -/
theorem IsAffineObstruction.maxRayleigh_eq_two [DecidableEq ι] [Nonempty ι]
    {X : WeightedGraph ι} (hX : X.IsAffineObstruction) :
    maxRayleigh X.isHermitian = 2 := by
  obtain ⟨v, hv, heig⟩ := hX.exists_pos_eigenvector
  exact (X.eigenvalue_eq_maxRayleigh_of_pos hX.connected hv heig).symm

end WeightedGraph

namespace Matrix.IsFiniteCartan

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Finite κ] [Nonempty κ] {M : Matrix ι ι ℤ}

/-- The weighted support of a finite Cartan matrix contains no affine obstruction. -/
theorem not_contains_affine (hM : M.IsFiniteCartan) {X : WeightedGraph κ}
    (hX : X.IsAffineObstruction) (e : κ ↪ ι) : ¬ hM.weightedGraph.Contains X e := by
  classical
  let _ := Fintype.ofFinite κ
  intro h
  have hle := WeightedGraph.maxRayleigh_mono h
  rw [hX.maxRayleigh_eq_two] at hle
  exact (not_le_of_gt hM.maxRayleigh_weightedGraph_lt_two) hle

end Matrix.IsFiniteCartan
