/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.SpanTransport
import Mathlib.Data.Set.Finite.Powerset

/-!
# A maximal extension within the root span

The lemma `lem:sec3-extension` of the Section 3 blueprint, used in Theorem 3.6 of [CGSS].
The candidate roots have finitely many signatures against the original roots. Maximizing the
cardinality of an eligible root set gives maximality; equality of spans gives indecomposability.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `lem:sec3-extension`: candidate roots in the original span, with the products allowed
by Definition 2.2 of [CGSS]. -/
def spanCandidates (S : LineSystem V) : Set V :=
  {x | x ∈ span ℝ S.Φ ∧ ⟪x, x⟫ = 2 ∧
    ∀ r ∈ S.Φ, ⟪x, r⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ)}

/-- `lem:sec3-extension`, steps `s3extsignature`--`s3extfinite`: the finitely many
signatures determine candidate vectors because the original roots span. -/
theorem finite_spanCandidates (S : LineSystem V) : S.spanCandidates.Finite := by
  classical
  have := S.finite.to_subtype
  let f : V → S.Φ → ℝ := fun x r ↦ ⟪x, (r : V)⟫
  have hfinite : {a : S.Φ → ℝ | ∀ r, a r ∈ ({-2, -1, 0, 1, 2} : Set ℝ)}.Finite :=
    Set.Finite.pi' (fun _ ↦ Set.toFinite _)
  refine Set.Finite.of_injOn (f := f) (t := {a : S.Φ → ℝ |
    ∀ r, a r ∈ ({-2, -1, 0, 1, 2} : Set ℝ)}) ?_ ?_ hfinite
  · exact fun x hx r ↦ hx.2.2 r r.property
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply S.eq_zero_of_mem_span_of_forall_inner (sub_mem hx.1 hy.1)
  intro r hr
  rw [inner_sub_left, sub_eq_zero]
  exact congrFun hxy ⟨r, hr⟩

/-- `lem:sec3-extension`, step `s3extinK`: the allowed product set is closed under negation. -/
private theorem neg_mem_allowed {t : ℝ} (h : t ∈ ({-2, -1, 0, 1, 2} : Set ℝ)) :
    -t ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- `lem:sec3-extension`, step `s3extadjoin`: adjoining both signs of an allowed vector
gives another line system. -/
def adjoinRoot (S : LineSystem V) (x : V) (hnorm : ⟪x, x⟫ = 2)
    (hprod : ∀ r ∈ S.Φ, ⟪x, r⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ)) : LineSystem V where
  Φ := S.Φ ∪ {x, -x}
  finite := S.finite.union (Set.toFinite _)
  inner_self r hr := by
    rcases hr with hr | hr
    · exact S.inner_self r hr
    · rcases hr with rfl | hr
      · exact hnorm
      · rw [Set.mem_singleton_iff] at hr
        rw [hr, inner_neg_neg, hnorm]
  neg_mem r hr := by
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hr ⊢
    rcases hr with hr | rfl | rfl
    · exact Or.inl (S.neg_mem r hr)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (neg_neg x))
  inner_mem r hr s hs := by
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
    rcases hr with hr | rfl | rfl <;> rcases hs with hs | rfl | rfl
    · exact S.inner_mem r hr s hs
    · rw [real_inner_comm]
      exact hprod r hr
    · rw [inner_neg_right, real_inner_comm]
      exact neg_mem_allowed (hprod r hr)
    · exact hprod s hs
    · rw [hnorm]
      norm_num
    · rw [inner_neg_right, hnorm]
      norm_num
    · rw [inner_neg_left]
      exact neg_mem_allowed (hprod s hs)
    · rw [inner_neg_left, hnorm]
      norm_num
    · rw [inner_neg_neg, hnorm]
      norm_num

/-- `lem:sec3-extension`, steps `s3extoldpart`--`s3extindec`: an extension of an
indecomposable system with the same span is indecomposable. -/
theorem IsIndecomposable.of_span_eq {S T : LineSystem V} (hS : S.IsIndecomposable)
    (hST : S.Φ ⊆ T.Φ) (hspan : span ℝ T.Φ = span ℝ S.Φ) : T.IsIndecomposable := by
  intro P Q hPQ horth
  have hcover : (P ∩ S.Φ) ∪ (Q ∩ S.Φ) = S.Φ := by
    rw [← Set.union_inter_distrib_right, hPQ]
    exact Set.inter_eq_right.mpr hST
  have hparts := hS (P ∩ S.Φ) (Q ∩ S.Φ) hcover
    (fun p hp q hq ↦ horth p hp.1 q hq.1)
  have hzero (x : V) (hx : x ∈ T.Φ) (h : ∀ r ∈ S.Φ, ⟪x, r⟫ = 0) : False := by
    have hxspan : x ∈ span ℝ S.Φ := hspan ▸ subset_span hx
    have hxzero := S.eq_zero_of_mem_span_of_forall_inner hxspan h
    have hn := T.inner_self x hx
    rw [hxzero, inner_zero_left] at hn
    norm_num at hn
  rcases hparts with hP | hQ
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    apply hzero p (hPQ ▸ Or.inl hp)
    intro r hr
    have hrT : r ∈ P ∪ Q := by rw [hPQ]; exact hST hr
    rcases hrT with hrP | hrQ
    · have : r ∈ P ∩ S.Φ := ⟨hrP, hr⟩
      simp only [hP, Set.mem_empty_iff_false] at this
    · exact horth p hp r hrQ
  · right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    apply hzero q (hPQ ▸ Or.inr hq)
    intro r hr
    have hrT : r ∈ P ∪ Q := by rw [hPQ]; exact hST hr
    rcases hrT with hrP | hrQ
    · rw [real_inner_comm]
      exact horth r hrP q hq
    · have : r ∈ Q ∩ S.Φ := ⟨hrQ, hr⟩
      simp only [hQ, Set.mem_empty_iff_false] at this

/-- `lem:sec3-extension`, used in Theorem 3.6 of [CGSS]: a nonmaximal indecomposable
line system has a proper maximal, indecomposable, star-closed extension in its own span.
The ambient space need not be finite-dimensional, since the root set is finite. -/
theorem exists_maximal_extension_span (S : LineSystem V) (_hne : S.Φ.Nonempty)
    (hi : S.IsIndecomposable) (hmax : ¬ S.IsMaximal) :
    ∃ T : LineSystem V, S.Φ ⊂ T.Φ ∧ T.Φ ⊆ span ℝ S.Φ ∧
      span ℝ T.Φ = span ℝ S.Φ ∧ T.IsMaximal ∧ T.IsIndecomposable ∧ T.IsStarClosed := by
  classical
  let E : Set (Set V) := {R | ∃ T : LineSystem V,
    T.Φ = R ∧ S.Φ ⊆ T.Φ ∧ T.Φ ⊆ S.spanCandidates}
  have hS : S.Φ ∈ E := ⟨S, rfl, Set.Subset.rfl, fun r hr ↦
    ⟨subset_span hr, S.inner_self r hr, S.inner_mem r hr⟩⟩
  have hE : E.Finite := S.finite_spanCandidates.powerset.subset (by
    rintro R ⟨T, rfl, _, hT⟩
    exact hT)
  obtain ⟨R, hR, hcard⟩ := hE.toFinset.exists_max_image Set.ncard
    ⟨S.Φ, hE.mem_toFinset.mpr hS⟩
  obtain ⟨T, rfl, hST, hTK⟩ := hE.mem_toFinset.mp hR
  have hTW : T.Φ ⊆ span ℝ S.Φ := fun r hr ↦ (hTK hr).1
  have hspan : span ℝ T.Φ = span ℝ S.Φ :=
    le_antisymm (span_le.mpr hTW) (span_mono hST)
  have hTmax : T.IsMaximal := by
    intro x hx hn hp
    let U := T.adjoinRoot x hn hp
    have hTU : T.Φ ⊆ U.Φ := Set.subset_union_left
    have hxK : x ∈ S.spanCandidates := ⟨hspan ▸ hx, hn, fun r hr ↦ hp r (hST hr)⟩
    have hnegK : -x ∈ S.spanCandidates :=
      ⟨Submodule.neg_mem _ hxK.1, by simpa only [inner_neg_neg] using hn,
        fun r hr ↦ by rw [inner_neg_left]; exact neg_mem_allowed (hxK.2.2 r hr)⟩
    have hU : U.Φ ∈ E := by
      refine ⟨U, rfl, hST.trans hTU, ?_⟩
      intro r hr
      rcases hr with hr | hr
      · exact hTK hr
      · rcases hr with rfl | hr
        · exact hxK
        · exact Set.mem_singleton_iff.mp hr ▸ hnegK
    have hle := hcard U.Φ (hE.mem_toFinset.mpr hU)
    by_contra hxT
    have hproper : T.Φ ⊂ U.Φ := Set.ssubset_iff_subset_ne.mpr
      ⟨hTU, fun he ↦ hxT (he.symm ▸ (show x ∈ U.Φ from Or.inr (Or.inl rfl)))⟩
    exact (not_lt_of_ge hle) (Set.ncard_lt_ncard hproper U.finite)
  have hproper : S.Φ ⊂ T.Φ := Set.ssubset_iff_subset_ne.mpr ⟨hST, fun he ↦ hmax (by
    intro x hx hn hp
    rw [he] at hx hp ⊢
    exact hTmax x hx hn hp)⟩
  exact ⟨T, hproper, hTW, hspan, hTmax, hi.of_span_eq hST hspan, hTmax.isStarClosed⟩

end LineSystem
