/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ClassificationExists
import LineGraphs.RootSetClassification.Components
import LineGraphs.RootSetClassification.LengthSpectrum
import LineGraphs.RootSetClassification.SmallRankSimilarity

/-!
# Theorem B of the blueprint for Remark 3.11 of [CGSS]

`lem:rem-indecomp-classification` and `thm:B` of the blueprint for Remark 3.11
of [CGSS]. A model means a type together with its rank in the canonical list.
Each component has its own similarity factor. The model assertions of blueprint Theorem B are
`RootSetModel.isIndecomposable`, `RootSetModel.two_lengths_iff` and
`RootSetModel.B₂_C₂_similarity`, and the empty case is `IsRootSet.eq_empty_iff_subsingleton`;
`IsRootSet.classification` states them together.
-/

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- Similarity to a type and rank in the canonical list, in Theorem B of the blueprint for Remark
3.11 of [CGSS]. -/
def IsSimilarToModel (Φ : Set V) (T : (n : ℕ) × CartanMatrix.FiniteType n) : Prop :=
  ∃ f : V ≃ₗ[ℝ] RootSetModel.Space T.2, ∃ a : ℝ,
    IsSimilarity Φ (RootSetModel.roots T.2) f a

-- Remark 3.11, lem:rem-indecomp-classification
/-- The indecomposable classification in Remark 3.11: there is exactly one
coordinate model up to a common positive similarity factor. Uniqueness concerns
the type and rank, not the map or a choice of base. -/
theorem classification_of_isIndecomposable (hΦ : IsRootSet Φ) (hI : hΦ.IsIndecomposable) :
    ∃! T : (n : ℕ) × CartanMatrix.FiniteType n, IsSimilarToModel Φ T := by
  obtain ⟨n, t, f, a, hf⟩ := hΦ.exists_similarity_model hI
  refine ⟨⟨n, t⟩, ⟨f, a, hf⟩, ?_⟩
  rintro ⟨m, s⟩ ⟨g, b, hg⟩
  exact RootSetModel.type_eq_of_similarity s t (similarity_comp (similarity_symm hg) hf)

open scoped Classical in
-- Remark 3.11, thm:B
/-- Theorem B of the blueprint for Remark 3.11 of [CGSS], steps `rBmain`--`rBmodelindecomp`: a
nonempty
indecomposable root set is similar, by one positive factor, to exactly one model of the
canonical list; exactly the B, C, F and G models have two lengths; the coordinate `C₂` is
similar to `B₂` (and `C` starts at rank 3 in the list); in general each graph component
is similar to exactly one model, with independent scales, the models are indecomposable,
and the component spans form an orthogonal internal direct sum of the ambient space,
which is the zero space exactly when there are no roots. -/
theorem classification (hΦ : IsRootSet Φ) :
    (hΦ.IsIndecomposable →
      ∃! T : (n : ℕ) × CartanMatrix.FiniteType n, IsSimilarToModel Φ T) ∧
    (∀ {n : ℕ} (t : CartanMatrix.FiniteType n),
      (squaredLengths (RootSetModel.roots t)).ncard = 2 ↔ ¬ RootSetModel.IsSimplyLaced t) ∧
    IsSimilarity (RootSetModel.Bn 2) (RootSetModel.Cn 2) RootSetModel.b₂ToC₂ 2 ∧
    (∀ C : (rootGraph Φ).ConnectedComponent,
      ∃! T : (n : ℕ) × CartanMatrix.FiniteType n,
        IsSimilarToModel ((Subtype.val : componentSpan C → V) ⁻¹' componentRoots C) T) ∧
    (∀ {n : ℕ} (t : CartanMatrix.FiniteType n), (RootSetModel.isRootSet t).IsIndecomposable) ∧
    OrthogonalFamily ℝ (fun C : (rootGraph Φ).ConnectedComponent ↦ componentSpan C)
      (fun C ↦ (componentSpan C).subtypeₗᵢ) ∧
    DirectSum.IsInternal (fun C : (rootGraph Φ).ConnectedComponent ↦ componentSpan C) ∧
    (Φ = ∅ ↔ Subsingleton V) :=
  ⟨hΦ.classification_of_isIndecomposable, RootSetModel.two_lengths_iff,
    RootSetModel.B₂_C₂_similarity,
    fun C ↦ (hΦ.component_isRootSet C).classification_of_isIndecomposable
      (hΦ.component_isIndecomposable C), RootSetModel.isIndecomposable,
    hΦ.orthogonal_components.2.1, hΦ.orthogonal_components.2.2, hΦ.eq_empty_iff_subsingleton⟩

end IsRootSet
