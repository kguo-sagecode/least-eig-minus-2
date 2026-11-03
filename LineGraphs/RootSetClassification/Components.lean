/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ConnectedBase
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Orthogonal components of a root set

`lem:rem-components` of the blueprint for Remark 3.11 of [CGSS]. The components
are those of the graph on all roots, with edges joining nonorthogonal roots.
Each is a root set in its own span, and the spans form an orthogonal internal sum.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- The graph on all roots in `lem:rem-components` of Remark 3.11. -/
def rootGraph (Φ : Set V) : SimpleGraph Φ := nonorthogonalityGraph Subtype.val

/-- The ambient roots of a graph component in `lem:rem-components` of Remark 3.11. -/
def componentRoots (C : (rootGraph Φ).ConnectedComponent) : Set V :=
  {r | ∃ hr : r ∈ Φ, (rootGraph Φ).connectedComponentMk ⟨r, hr⟩ = C}

/-- The component spans in `lem:rem-components` of Remark 3.11. -/
noncomputable def componentSpan (C : (rootGraph Φ).ConnectedComponent) : Submodule ℝ V :=
  span ℝ (componentRoots C)

/-- Step `roorth` of Remark 3.11: roots in different components are orthogonal. -/
theorem inner_eq_zero_of_component_ne (r s : Φ)
    (h : (rootGraph Φ).connectedComponentMk r ≠ (rootGraph Φ).connectedComponentMk s) :
    ⟪(r : V), (s : V)⟫ = 0 := by
  by_contra hn
  apply h
  by_cases hrs : r = s
  · exact congrArg _ hrs
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨hrs, hn⟩

/-- Step `roorth` in terms of the ambient component root sets. -/
theorem componentRoots_orthogonal (C D : (rootGraph Φ).ConnectedComponent) (hCD : C ≠ D)
    {r s : V} (hr : r ∈ componentRoots C) (hs : s ∈ componentRoots D) : ⟪r, s⟫ = 0 := by
  obtain ⟨hr, hCr⟩ := hr
  obtain ⟨hs, hDs⟩ := hs
  exact inner_eq_zero_of_component_ne ⟨r, hr⟩ ⟨s, hs⟩ (by rwa [hCr, hDs])

/-- Steps `rorootset` and `rangfixedbasic` of Remark 3.11: a reflection-closed
subset of a root set is a root set in its own span. -/
theorem restrictSpan_isRootSet (hΦ : IsRootSet Φ) {Ψ : Set V} (hsub : Ψ ⊆ Φ)
    (href : ∀ r ∈ Ψ, ∀ s ∈ Ψ, s - (2 * ⟪r, s⟫ / ⟪r, r⟫) • r ∈ Ψ) :
    IsRootSet ((Subtype.val : span ℝ Ψ → V) ⁻¹' Ψ) where
  finite := (hΦ.finite.subset hsub).preimage Subtype.val_injective.injOn
  zero_notMem h := hΦ.zero_notMem (hsub h)
  span_eq_top := span_span_coe_preimage
  crystallographic r hr s hs := hΦ.crystallographic r (hsub hr) s (hsub hs)
  reduced r hr t ht := hΦ.reduced r (hsub hr) t (hsub ht)
  reflection_mem r hr s hs := href r hr s hs

/-- Steps `rozero`--`rononzero`: reflection in a root preserves its component. -/
theorem reflection_mem_componentRoots (hΦ : IsRootSet Φ)
    (C : (rootGraph Φ).ConnectedComponent) {r s : V}
    (hr : r ∈ componentRoots C) (hs : s ∈ componentRoots C) :
    s - (2 * ⟪r, s⟫ / ⟪r, r⟫) • r ∈ componentRoots C := by
  obtain ⟨hrΦ, hCr⟩ := hr
  obtain ⟨hsΦ, hCs⟩ := hs
  by_cases hz : ⟪r, s⟫ = 0
  · simpa only [hz, mul_zero, zero_div, zero_smul, sub_zero] using ⟨hsΦ, hCs⟩
  let t := reflection r (hΦ.ne_zero hrΦ) s
  have ht : t ∈ Φ := by
    dsimp [t]
    rw [reflection_apply]
    exact hΦ.reflection_mem r hrΦ s hsΦ
  have hrt : ⟪r, t⟫ ≠ 0 := by
    have he := (reflection r (hΦ.ne_zero hrΦ)).inner_map_map r s
    rw [reflection_self, inner_neg_left] at he
    intro h
    exact hz (by change ⟪r, t⟫ = 0 at h; linarith)
  have he : (rootGraph Φ).connectedComponentMk ⟨r, hrΦ⟩ =
      (rootGraph Φ).connectedComponentMk ⟨t, ht⟩ := by
    by_contra hn
    exact hrt (inner_eq_zero_of_component_ne _ _ hn)
  rw [← reflection_apply r (hΦ.ne_zero hrΦ)]
  exact ⟨ht, he.symm.trans hCr⟩

/-- Step `rorootset`: the root-set structure on each component span. -/
theorem component_isRootSet (hΦ : IsRootSet Φ) (C : (rootGraph Φ).ConnectedComponent) :
    IsRootSet ((Subtype.val : componentSpan C → V) ⁻¹' componentRoots C) :=
  hΦ.restrictSpan_isRootSet (fun _ h ↦ h.choose)
    (fun _ hr _ hs ↦ hΦ.reflection_mem_componentRoots C hr hs)

/-- Step `roconnected`, the connected-to-indecomposable direction of Remark 3.11. -/
theorem isIndecomposable_of_connected (hΦ : IsRootSet Φ) (hc : (rootGraph Φ).Connected) :
    hΦ.IsIndecomposable := by
  obtain ⟨r₀⟩ := hc.nonempty
  refine ⟨⟨r₀, r₀.property⟩, fun A B hab ho ↦ ?_⟩
  have hstep : ∀ ⦃r s⦄, (rootGraph Φ).Adj r s → ((r : V) ∈ A) = ((s : V) ∈ A) := by
    intro r s hrs
    apply propext
    constructor <;> intro hr <;> by_contra hs
    · have hsu : (s : V) ∈ A ∪ B := hab ▸ s.property
      exact hrs.2 (ho _ hr _ (hsu.resolve_left hs))
    · exact hrs.2 (by
        rw [real_inner_comm]
        have hru : (r : V) ∈ A ∪ B := hab ▸ r.property
        exact ho _ hr _ (hru.resolve_left hs))
  have hconst := hc.constant_of_edge_eq hstep
  by_cases hr₀ : (r₀ : V) ∈ A
  · right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hsΦ : s ∈ Φ := hab ▸ Or.inr hs
    have hsA : s ∈ A := (hconst r₀ ⟨s, hsΦ⟩) ▸ hr₀
    exact hΦ.ne_zero hsΦ (inner_self_eq_zero.mp (ho s hsA s hs))
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrΦ : r ∈ Φ := hab ▸ Or.inl hr
    exact hr₀ ((hconst ⟨r, hrΦ⟩ r₀) ▸ hr)

/-- Step `roconnected`: indecomposability is equivalent to connectedness of the
graph on all roots. Both sides exclude the empty root set. -/
theorem isIndecomposable_iff_connected (hΦ : IsRootSet Φ) :
    hΦ.IsIndecomposable ↔ (rootGraph Φ).Connected := by
  refine ⟨fun hI ↦ ?_, hΦ.isIndecomposable_of_connected⟩
  obtain ⟨r, hr⟩ := hI.1
  let C := (rootGraph Φ).connectedComponentMk ⟨r, hr⟩
  let A := componentRoots C
  have hab : A ∪ (Φ \ A) = Φ := Set.union_sdiff_cancel (fun _ h ↦ h.choose)
  have ho : ∀ a ∈ A, ∀ b ∈ Φ \ A, ⟪a, b⟫ = 0 := by
    rintro a ⟨ha, hCa⟩ b ⟨hb, hbA⟩
    apply inner_eq_zero_of_component_ne ⟨a, ha⟩ ⟨b, hb⟩
    intro he
    exact hbA ⟨hb, he.symm.trans hCa⟩
  have hB : Φ \ A = ∅ := (hI.2 A (Φ \ A) hab ho).resolve_left (by
    intro hA
    have : r ∈ A := ⟨hr, rfl⟩
    simp only [hA, Set.mem_empty_iff_false] at this)
  let : Nonempty Φ := ⟨⟨r, hr⟩⟩
  have hreach (s : Φ) : (rootGraph Φ).Reachable ⟨r, hr⟩ s := by
    have hs : (s : V) ∈ A := by
      by_contra hn
      have : (s : V) ∈ Φ \ A := ⟨s.property, hn⟩
      simp only [hB, Set.mem_empty_iff_false] at this
    obtain ⟨_, hs⟩ := hs
    exact SimpleGraph.ConnectedComponent.exact hs.symm
  exact ⟨fun s t ↦ (hreach s).symm.trans (hreach t)⟩

/-- Step `roindecomp`: the induced graph of a component is connected, so its
root set in its span is indecomposable. -/
theorem component_isIndecomposable (hΦ : IsRootSet Φ)
    (C : (rootGraph Φ).ConnectedComponent) : (hΦ.component_isRootSet C).IsIndecomposable := by
  apply isIndecomposable_of_connected
  let f : C → ((Subtype.val : componentSpan C → V) ⁻¹' componentRoots C) := fun r ↦
    ⟨⟨r.val.val, subset_span ⟨r.val.property, r.property⟩⟩, ⟨r.val.property, r.property⟩⟩
  let g : C.toSimpleGraph →g rootGraph
      ((Subtype.val : componentSpan C → V) ⁻¹' componentRoots C) :=
    { toFun := f
      map_rel' := by
        intro r s hrs
        refine ⟨?_, hrs.2⟩
        intro he
        apply hrs.1
        exact Subtype.ext (congrArg (fun t ↦ t.val.val) he) }
  apply C.connected_toSimpleGraph.map g
  intro r
  obtain ⟨hr, hCr⟩ := r.property
  refine ⟨⟨⟨r.val.val, hr⟩, hCr⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Step `rospans`: distinct component spans are orthogonal. -/
theorem orthogonalFamily_componentSpan :
    OrthogonalFamily ℝ (fun C : (rootGraph Φ).ConnectedComponent ↦ componentSpan C)
      (fun C ↦ (componentSpan C).subtypeₗᵢ) := by
  intro C D hCD r s
  have hl : componentSpan C ≤ LinearMap.ker (innerₗ V (s : V)) := by
    apply span_le.mpr
    intro a ha
    have hr : componentSpan D ≤ LinearMap.ker (innerₗ V a) := by
      apply span_le.mpr
      exact fun b hb ↦ componentRoots_orthogonal C D hCD ha hb
    change ⟪(s : V), a⟫ = 0
    rw [real_inner_comm]
    exact hr s.property
  change ⟪(r : V), (s : V)⟫ = 0
  rw [real_inner_comm]
  exact hl r.property

/-- Step `roallspan`: every root is in its component span, and the roots span. -/
theorem iSup_componentSpan_eq_top (hΦ : IsRootSet Φ) :
    (⨆ C : (rootGraph Φ).ConnectedComponent, componentSpan C) = ⊤ := by
  apply top_unique
  rw [← hΦ.span_eq_top]
  apply span_le.mpr
  intro r hr
  exact le_iSup componentSpan ((rootGraph Φ).connectedComponentMk ⟨r, hr⟩)
    (subset_span ⟨hr, rfl⟩)

open scoped Classical in
-- Remark 3.11, lem:rem-components
/-- `lem:rem-components` of Remark 3.11: the graph components give indecomposable
root sets and an orthogonal internal direct sum of the ambient space. -/
theorem orthogonal_components (hΦ : IsRootSet Φ) :
    (∀ C : (rootGraph Φ).ConnectedComponent, (hΦ.component_isRootSet C).IsIndecomposable) ∧
    OrthogonalFamily ℝ (fun C : (rootGraph Φ).ConnectedComponent ↦ componentSpan C)
      (fun C ↦ (componentSpan C).subtypeₗᵢ) ∧
    DirectSum.IsInternal (fun C : (rootGraph Φ).ConnectedComponent ↦ componentSpan C) := by
  refine ⟨hΦ.component_isIndecomposable, orthogonalFamily_componentSpan, ?_⟩
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨orthogonalFamily_componentSpan.independent, hΦ.iSup_componentSpan_eq_top⟩

/-- Step `roempty`: the empty root set spans only the zero space. -/
theorem subsingleton_of_eq_empty (hΦ : IsRootSet Φ) (he : Φ = ∅) : Subsingleton V := by
  have ht : (⊥ : Submodule ℝ V) = ⊤ := by simpa only [he, span_empty] using hΦ.span_eq_top
  exact ⟨fun x y ↦ by
    have hx : x = 0 := (show x ∈ (⊥ : Submodule ℝ V) from ht ▸ mem_top)
    have hy : y = 0 := (show y ∈ (⊥ : Submodule ℝ V) from ht ▸ mem_top)
    exact hx.trans hy.symm⟩

/-- Step `roempty` and its converse in Remark 3.11: the root set is empty exactly when
the space is zero. -/
theorem eq_empty_iff_subsingleton (hΦ : IsRootSet Φ) : Φ = ∅ ↔ Subsingleton V := by
  refine ⟨hΦ.subsingleton_of_eq_empty, fun _ ↦ ?_⟩
  exact Set.eq_empty_iff_forall_notMem.mpr fun r hr ↦ hΦ.ne_zero hr (Subsingleton.elim _ _)

/-- Step `roempty` of Remark 3.11: the empty root set has no components. -/
theorem isEmpty_connectedComponent_of_eq_empty (he : Φ = ∅) :
    IsEmpty (rootGraph Φ).ConnectedComponent :=
  ⟨fun C ↦ SimpleGraph.ConnectedComponent.ind (β := fun _ ↦ False)
    (fun v ↦ Set.eq_empty_iff_forall_notMem.mp he v.1 v.2) C⟩

end IsRootSet
