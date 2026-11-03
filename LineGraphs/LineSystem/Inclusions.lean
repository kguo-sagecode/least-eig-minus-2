/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Hyp24
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Isometric inclusions of line systems

An isometric inclusion of `S` in `T` (`blueprint/sec3-rootsystems.tex`, opening paragraph) is a
linear isometry of the spans of the root sets carrying the roots of `S` into those of `T`; it is
proper when the inclusion of root sets is proper. Computation C5 and Theorem 3.6 use them.

## Main definitions

* `LineSystem.IsometricInclusion S T`, with `G.root r hr ∈ T.Φ` the image of a root.
* `LineSystem.IsometricInclusion.IsProper`: some root of `T` is not an image.
* `LineSystem.IsometricInclusion.ofLinearMap`: an ambient linear map that preserves the inner
  products of roots and maps roots to roots.
* `LineSystem.IsometricInclusion.targetHyp24`: the target marked by the images of a star.
* `LineSystem.IsometricInclusion.orthGraphEmbedding`: the induced embedding of orthogonality graphs
  (Lemma "marked inclusions").

## Main statements

* `LineSystem.IsometricInclusion.isProper_of_ncard_lt`: more roots in the target.
* `LineSystem.not_isMaximal_of_proper_isometric_inclusion`: Lemma "an equal-rank proper
  inclusion".
* `LineSystem.Hyp24.orthGraph_embedding_of_subset`: Lemma "marked inclusions".
-/

open scoped RealInnerProductSpace
open Submodule Module

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- An isometric inclusion of `S` in `T`: a linear isometry of the spans of the root sets that
carries the roots of `S` into the roots of `T`. -/
structure IsometricInclusion (S : LineSystem V) (T : LineSystem W) where
  /-- The linear isometry of spans. -/
  toLinearIsometry : span ℝ S.Φ →ₗᵢ[ℝ] span ℝ T.Φ
  /-- Roots go to roots. -/
  map_mem : ∀ r (hr : r ∈ S.Φ), ((toLinearIsometry ⟨r, subset_span hr⟩ : span ℝ T.Φ) : W) ∈ T.Φ

namespace IsometricInclusion

variable {S : LineSystem V} {T : LineSystem W} (G : IsometricInclusion S T)

/-- The image of a root. -/
def root (r : V) (hr : r ∈ S.Φ) : W := (G.toLinearIsometry ⟨r, subset_span hr⟩ : W)

theorem root_mem (r : V) (hr : r ∈ S.Φ) : G.root r hr ∈ T.Φ := G.map_mem r hr

theorem inner_toLinearIsometry (x y : span ℝ S.Φ) :
    ⟪(G.toLinearIsometry x : W), (G.toLinearIsometry y : W)⟫ = ⟪(x : V), (y : V)⟫ := by
  rw [← Submodule.coe_inner, LinearIsometry.inner_map_map, Submodule.coe_inner]

theorem inner_root (r : V) (hr : r ∈ S.Φ) (s : V) (hs : s ∈ S.Φ) :
    ⟪G.root r hr, G.root s hs⟫ = ⟪r, s⟫ :=
  G.inner_toLinearIsometry _ _

theorem root_injective {r s : V} (hr : r ∈ S.Φ) (hs : s ∈ S.Φ) (h : G.root r hr = G.root s hs) :
    r = s := by
  have h2 : ⟪r, s⟫ = 2 := by
    rw [← G.inner_root r hr s hs, h]
    exact T.inner_self _ (G.root_mem s hs)
  exact (S.inner_eq_two_iff hr hs).mp h2

/-- The inclusion is proper: some root of `T` is not the image of a root of `S`. -/
def IsProper : Prop := ∃ t ∈ T.Φ, ∀ r (hr : r ∈ S.Φ), G.root r hr ≠ t

/-- An inclusion into a system with more roots is proper. -/
theorem isProper_of_ncard_lt (h : S.Φ.ncard < T.Φ.ncard) : G.IsProper := by
  classical
  by_contra hne
  simp only [IsProper, not_exists, not_and, not_forall, not_not] at hne
  let φ : V → W := fun r => if hr : r ∈ S.Φ then G.root r hr else 0
  have hsub : T.Φ ⊆ φ '' S.Φ := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := hne t ht
    exact ⟨r, hr, by simp only [φ, hr, dite_true, hrt]⟩
  have h1 := Set.ncard_le_ncard hsub (S.finite.image φ)
  have h2 := Set.ncard_image_le (f := φ) S.finite
  omega

/-- An ambient linear map that preserves the inner products of roots and maps roots to roots
restricts to an isometric inclusion. -/
noncomputable def ofLinearMap (f : V →ₗ[ℝ] W) (hinner : ∀ r ∈ S.Φ, ∀ s ∈ S.Φ, ⟪f r, f s⟫ = ⟪r, s⟫)
    (hmem : ∀ r ∈ S.Φ, f r ∈ T.Φ) : IsometricInclusion S T where
  toLinearIsometry :=
    LinearMap.isometryOfInner
      (LinearMap.codRestrict (span ℝ T.Φ) (f.domRestrict (span ℝ S.Φ)) (by
        rintro ⟨x, hx⟩
        change f x ∈ span ℝ T.Φ
        induction hx using Submodule.span_induction with
        | mem r hr => exact subset_span (hmem r hr)
        | zero => simp
        | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
        | smul c a _ ha => rw [map_smul]; exact smul_mem _ c ha))
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        rw [Submodule.coe_inner, Submodule.coe_inner]
        change ⟪f x, f y⟫ = ⟪x, y⟫
        induction hx using Submodule.span_induction generalizing y with
        | mem r hr =>
          induction hy using Submodule.span_induction with
          | mem s hs => exact hinner r hr s hs
          | zero => simp
          | add a b _ _ ha hb => rw [map_add, inner_add_right, inner_add_right, ha, hb]
          | smul c a _ ha => rw [map_smul, real_inner_smul_right, real_inner_smul_right, ha]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, inner_add_left, inner_add_left, ha y hy, hb y hy]
        | smul c a _ ha => rw [map_smul, real_inner_smul_left, real_inner_smul_left, ha y hy])
  map_mem r hr := hmem r hr

theorem ofLinearMap_root (f : V →ₗ[ℝ] W) (hinner hmem) (r : V) (hr : r ∈ S.Φ) :
    (ofLinearMap f hinner hmem : IsometricInclusion S T).root r hr = f r := rfl

/-- A literal inclusion of root sets in the same space. -/
noncomputable def ofSubset {S T : LineSystem V} (h : S.Φ ⊆ T.Φ) : IsometricInclusion S T :=
  ofLinearMap LinearMap.id (fun _ _ _ _ => rfl) (fun _ hr => h hr)

theorem ofSubset_root {S T : LineSystem V} (h : S.Φ ⊆ T.Φ) (r : V) (hr : r ∈ S.Φ) :
    (ofSubset h).root r hr = r := rfl

/-- The composition of isometric inclusions. -/
noncomputable def trans {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    {R : LineSystem U} (G' : IsometricInclusion T R) : IsometricInclusion S R where
  toLinearIsometry := G'.toLinearIsometry.comp G.toLinearIsometry
  map_mem r hr := by
    have h := G'.map_mem _ (G.root_mem r hr)
    exact h

theorem trans_root {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    {R : LineSystem U} (G' : IsometricInclusion T R) (r : V) (hr : r ∈ S.Φ) :
    (G.trans G').root r hr = G'.root (G.root r hr) (G.root_mem r hr) := rfl

/-- The target marked by the images of the star of `H`. -/
def targetHyp24 (H : Hyp24 V) (G : IsometricInclusion H.S T) (hi : T.IsIndecomposable)
    (hs : T.IsStarClosed) : Hyp24 W where
  S := T
  isIndecomposable := hi
  isStarClosed := hs
  a := G.root H.a H.a_mem
  b := G.root H.b H.b_mem
  a_mem := G.root_mem _ _
  b_mem := G.root_mem _ _
  inner_a_b := by rw [G.inner_root, H.inner_a_b]

/-- An isometric inclusion maps `Γa` into the `Γa` of any target star formed by the images. -/
theorem root_mem_Γa (H : Hyp24 V) (H' : Hyp24 W) (G : IsometricInclusion H.S H'.S)
    (ha : G.root H.a H.a_mem = H'.a) (hb : G.root H.b H.b_mem = H'.b) {x : V} (hx : x ∈ H.Γa) :
    G.root x (H.Γa_subset_Φ hx) ∈ H'.Γa := by
  refine H'.mem_Γa_of (G.root_mem _ _) ?_ ?_
  · rw [← ha, G.inner_root, H.inner_a_of_mem_Γa hx]
  · rw [← hb, G.inner_root, H.inner_b_of_mem_Γa hx]

-- Lemma "marked inclusions"
/-- Lemma "marked inclusions" (`lem:sec3-marked-inclusion`): an isometric inclusion induces an
injection of `Γa` into the target `Γa` for the image star, preserving adjacency and nonadjacency
in the orthogonality graphs. -/
noncomputable def orthGraphEmbedding (H : Hyp24 V) (H' : Hyp24 W)
    (G : IsometricInclusion H.S H'.S) (ha : G.root H.a H.a_mem = H'.a)
    (hb : G.root H.b H.b_mem = H'.b) : H.orthGraph ↪g H'.orthGraph where
  toFun x := ⟨G.root x (H.Γa_subset_Φ x.property), G.root_mem_Γa H H' ha hb x.property⟩
  inj' x y h := by
    apply Subtype.ext
    have h' : G.root (x : V) (H.Γa_subset_Φ x.2) = G.root (y : V) (H.Γa_subset_Φ y.2) :=
      congrArg (fun z : H'.Γa => (z : W)) h
    exact G.root_injective _ _ h'
  map_rel_iff' {x y} := by
    rw [Hyp24.orthGraph_adj, Hyp24.orthGraph_adj]
    change ⟪G.root (x : V) (H.Γa_subset_Φ x.2), G.root (y : V) (H.Γa_subset_Φ y.2)⟫ = 0 ↔ _
    rw [G.inner_root]

end IsometricInclusion

namespace Hyp24

-- Lemma "marked inclusions"
/-- Lemma "marked inclusions" (`lem:sec3-marked-inclusion`): marking the target by the images of
the star, the orthogonality graph of the source is an induced subgraph of that of the target. -/
theorem orthGraph_embedding_of_subset (H : Hyp24 V) {T : LineSystem W}
    (G : IsometricInclusion H.S T) (hi : T.IsIndecomposable) (hs : T.IsStarClosed) :
    Nonempty (H.orthGraph ↪g (G.targetHyp24 H hi hs).orthGraph) :=
  ⟨G.orthGraphEmbedding H (G.targetHyp24 H hi hs) rfl rfl⟩

end Hyp24

-- Lemma "an equal-rank proper inclusion"
/-- Lemma "an equal-rank proper inclusion" (`lem:sec3-proper-inclusion`): a proper isometric
inclusion between systems whose spans have the same dimension shows that the source is not
maximal within its span. -/
theorem not_isMaximal_of_proper_isometric_inclusion {S : LineSystem V} {T : LineSystem W}
    (G : IsometricInclusion S T) (hrank : finrank ℝ (span ℝ S.Φ) = finrank ℝ (span ℝ T.Φ))
    (hG : G.IsProper) : ¬ S.IsMaximal := by
  intro hmax
  have := FiniteDimensional.span_of_finite ℝ S.finite
  have := FiniteDimensional.span_of_finite ℝ T.finite
  have hsurj : Function.Surjective G.toLinearIsometry.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp
      G.toLinearIsometry.injective
  obtain ⟨t, ht, hnot⟩ := hG
  obtain ⟨x, hx⟩ := hsurj ⟨t, subset_span ht⟩
  have hxt : (G.toLinearIsometry x : W) = t := congrArg Subtype.val hx
  have hnorm : ⟪(x : V), (x : V)⟫ = 2 := by
    rw [← G.inner_toLinearIsometry, hxt, T.inner_self t ht]
  have hprod : ∀ r ∈ S.Φ, ⟪(x : V), r⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
    intro r hr
    have h := G.inner_toLinearIsometry x ⟨r, subset_span hr⟩
    change ⟪(G.toLinearIsometry x : W), G.root r hr⟫ = ⟪(x : V), r⟫ at h
    rw [← h, hxt]
    exact T.inner_mem t ht _ (G.root_mem r hr)
  have hxS := hmax x x.property hnorm hprod
  exact hnot x hxS (by rw [← hxt]; rfl)

end LineSystem
