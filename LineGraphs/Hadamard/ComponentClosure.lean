/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Components
import LineGraphs.Hadamard.StarClosure
import LineGraphs.LineSystem.RootType

/-!
# The star closure of a component

Parts 4 and 5 of blueprint Lemma `lem:6-components`, Section 6 of [CGSS]. The component is
indecomposable before taking its star closure. Classification is an explicit hypothesis in
the forward, unique-type form of Theorem 3.5; the extension to spans uses `Iso.spanIsometry`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
  (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)

/-- The original roots `Φ(K)` of a component in blueprint `lem:6-components`. -/
def componentLineSystem (K : H.hadamardGraph.ConnectedComponent) :
    LineSystem (EuclideanSpace ℝ (Fin n)) where
  Φ := Set.range (LineSystem.signedVec fun p : K.supp ↦ H.hadamardRoot p)
  finite := Set.finite_range _
  inner_self := by
    rintro _ ⟨⟨p, b⟩, rfl⟩
    exact (hH.lineSystem hn hn16 ha).inner_self _ ⟨(p, b), rfl⟩
  neg_mem := by
    rintro _ ⟨⟨p, b⟩, rfl⟩
    refine ⟨(p, !b), ?_⟩
    cases b <;> simp [LineSystem.signedVec]
  inner_mem := by
    rintro _ ⟨⟨p, b⟩, rfl⟩ _ ⟨⟨q, c⟩, rfl⟩
    exact (hH.lineSystem hn hn16 ha).inner_mem _ ⟨(p, b), rfl⟩ _ ⟨(q, c), rfl⟩

/-- A component's roots belong to the original Hadamard line system (`s6cfsigma`). -/
theorem componentLineSystem_subset (K : H.hadamardGraph.ConnectedComponent) :
    (hH.componentLineSystem hn hn16 ha K).Φ ⊆ (hH.lineSystem hn hn16 ha).Φ := by
  rintro _ ⟨⟨p, b⟩, rfl⟩
  exact ⟨(p, b), rfl⟩

/-- The selected positive root of each pair belongs to its component (`s6cfsigma`). -/
theorem hadamardRoot_mem_componentLineSystem (K : H.hadamardGraph.ConnectedComponent)
    {p : HadamardPair n} (hp : p ∈ K.supp) :
    H.hadamardRoot p ∈ (hH.componentLineSystem hn hn16 ha K).Φ :=
  ⟨(⟨p, hp⟩, false), rfl⟩

/-- Step `s6cfsigma` of `lem:6-components`: components are nonempty. -/
theorem componentLineSystem_nonempty (K : H.hadamardGraph.ConnectedComponent) :
    (hH.componentLineSystem hn hn16 ha K).Φ.Nonempty := by
  obtain ⟨p, hp⟩ := K.nonempty_supp
  exact ⟨_, hH.hadamardRoot_mem_componentLineSystem hn hn16 ha K hp⟩

/-- Step `s6cfcard` of `lem:6-components`: the signed roots have cardinality `2 |K|`. -/
theorem ncard_componentLineSystem (K : H.hadamardGraph.ConnectedComponent) :
    (hH.componentLineSystem hn hn16 ha K).Φ.ncard = 2 * K.supp.ncard := by
  have hi : Function.Injective (LineSystem.signedVec fun p : K.supp ↦ H.hadamardRoot p) := by
    rintro ⟨p, b⟩ ⟨q, c⟩ he
    have he' : LineSystem.signedVec H.hadamardRoot (p.val, b) =
        LineSystem.signedVec H.hadamardRoot (q.val, c) := he
    have hp := hH.signed_hadamardRoot_injective hn hn16 ha he'
    have heq : (p : HadamardPair n) = q := congrArg Prod.fst hp
    have heq' : b = c := congrArg Prod.snd hp
    exact Prod.ext (Subtype.ext heq) heq'
  change (Set.range _).ncard = _
  rw [Set.ncard_range_of_injective hi, Nat.card_prod]
  simp [mul_comm]

/-- Part 4 of `lem:6-components`: taking both signs preserves the component span. -/
theorem span_componentLineSystem (K : H.hadamardGraph.ConnectedComponent) :
    span ℝ (hH.componentLineSystem hn hn16 ha K).Φ = componentSpan K := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨⟨p, b⟩, rfl⟩
    have hp : H.hadamardRoot p ∈ componentSpan K := subset_span ⟨p, p.property, rfl⟩
    cases b
    · exact hp
    · exact neg_mem hp
  · apply span_mono
    rintro _ ⟨p, hp, rfl⟩
    exact hH.hadamardRoot_mem_componentLineSystem hn hn16 ha K hp

/-- Step `s6cfsigma` of `lem:6-components`: paths between pairs propagate membership
in either part of an orthogonal partition, including both signs of each root. -/
theorem isIndecomposable_componentLineSystem (K : H.hadamardGraph.ConnectedComponent) :
    (hH.componentLineSystem hn hn16 ha K).IsIndecomposable := by
  intro P Q hPQ horth
  have hcover (p : HadamardPair n) (hp : p ∈ K.supp) :
      H.hadamardRoot p ∈ P ∨ H.hadamardRoot p ∈ Q := by
    change H.hadamardRoot p ∈ P ∪ Q
    rw [hPQ]
    exact hH.hadamardRoot_mem_componentLineSystem hn hn16 ha K hp
  have hprop {u v : HadamardPair n} (h : H.hadamardGraph.Reachable u v)
      (huK : u ∈ K.supp) (hu : H.hadamardRoot u ∈ P) : H.hadamardRoot v ∈ P := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => exact hu
    | @cons u w v huw p ih =>
      have hwK := K.mem_supp_of_adj_mem_supp huK huw
      apply ih hwK
      rcases hcover w hwK with hw | hw
      · exact hw
      · exact (huw.2 (horth _ hu _ hw)).elim
  by_cases hP : ∃ p ∈ K.supp, H.hadamardRoot p ∈ P
  · obtain ⟨p, hpK, hp⟩ := hP
    right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqΦ : q ∈ (hH.componentLineSystem hn hn16 ha K).Φ := hPQ ▸ Or.inr hq
    obtain ⟨⟨v, b⟩, rfl⟩ := hqΦ
    have hv := hprop (K.reachable_of_mem_supp hpK v.property) hpK hp
    have hz := horth _ hv _ hq
    cases b <;> simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
      inner_neg_right, hH.inner_hadamardRoot_self (by omega)] at hz <;> norm_num at hz
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpΦ : p ∈ (hH.componentLineSystem hn hn16 ha K).Φ := hPQ ▸ Or.inl hp
    obtain ⟨⟨v, b⟩, rfl⟩ := hpΦ
    have hv := (hcover v v.property).resolve_left (fun h ↦ hP ⟨v, v.property, h⟩)
    have hz := horth _ hp _ hv
    cases b <;> simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
      inner_neg_left, hH.inner_hadamardRoot_self (by omega)] at hz <;> norm_num at hz

/-- The system `R_K` of blueprint `lem:6-components`, the smallest star-closed extension. -/
noncomputable def componentStarClosure (K : H.hadamardGraph.ConnectedComponent) :
    LineSystem (EuclideanSpace ℝ (Fin n)) :=
  (hH.componentLineSystem hn hn16 ha K).starClosure

/-- Part 4 (`s6cfour`) of `lem:6-components`, Section 6 of [CGSS], from LN3. -/
theorem componentStarClosure_properties (K : H.hadamardGraph.ConnectedComponent) :
    (hH.componentStarClosure hn hn16 ha K).Φ.Nonempty ∧
      (hH.componentStarClosure hn hn16 ha K).IsIndecomposable ∧
      (hH.componentStarClosure hn hn16 ha K).IsStarClosed ∧
      (hH.componentLineSystem hn hn16 ha K).Φ ⊆ (hH.componentStarClosure hn hn16 ha K).Φ ∧
      span ℝ (hH.componentStarClosure hn hn16 ha K).Φ = componentSpan K := by
  let S := hH.componentLineSystem hn hn16 ha K
  exact ⟨(hH.componentLineSystem_nonempty hn hn16 ha K).mono S.subset_starClosure,
    (hH.isIndecomposable_componentLineSystem hn hn16 ha K).starClosure,
    S.isStarClosed_starClosure, S.subset_starClosure,
    S.span_starClosure.trans (hH.span_componentLineSystem hn hn16 ha K)⟩

-- Lemma (the components), Section 6
/-- Part 5 (`s6ctype`, `s6crank`, `s6clines`) of blueprint `lem:6-components`, Section 6
of [CGSS]. The explicit hypothesis is the forward, unique-type form of Theorem 3.5.
The root isomorphism extends to the surjective span isometry `Iso.spanIsometry`. -/
theorem component_rootType_of_classification
    (hclass : ∀ S : LineSystem (EuclideanSpace ℝ (Fin n)), S.Φ.Nonempty →
      S.IsIndecomposable → S.IsStarClosed →
        ∃! t : LineSystem.RootType, Nonempty (S.Iso t.model))
    (K : H.hadamardGraph.ConnectedComponent) :
    ∃! t : LineSystem.RootType,
      Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso t.model) ∧
      t.rank = componentRank K ∧
      (hH.componentStarClosure hn hn16 ha K).numLines = t.numLines ∧
      n * componentRank K ≤ 2 * t.numLines := by
  obtain ⟨hne, hi, hs, hsub, hspan⟩ := hH.componentStarClosure_properties hn hn16 ha K
  obtain ⟨t, ht, huniq⟩ := hclass _ hne hi hs
  have hrank : t.rank = componentRank K := by
    obtain ⟨e⟩ := ht
    rw [← t.finrank_span_model, ← e.finrank_span_eq, hspan]
    rfl
  have hlines : (hH.componentStarClosure hn hn16 ha K).numLines = t.numLines := by
    obtain ⟨e⟩ := ht
    exact e.numLines_eq.trans t.numLines_model
  have hcard := Set.ncard_le_ncard hsub (hH.componentStarClosure hn hn16 ha K).finite
  rw [hH.ncard_componentLineSystem hn hn16 ha K] at hcard
  have hle : K.supp.ncard ≤ t.numLines := by
    rw [← hlines, LineSystem.numLines]
    omega
  refine ⟨t, ⟨ht, hrank, hlines, ?_⟩, fun u hu ↦ huniq u hu.1⟩
  rw [← hH.two_mul_card_component K]
  omega

end Matrix.IsHadamard
