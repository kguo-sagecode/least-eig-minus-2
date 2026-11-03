/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import Mathlib.Data.Set.Card

/-!
# The lines of a representation

Lemma `lem:4-lines` in the Section 4 blueprint for [CGSS]: both signs of the representing
vectors form a line system, with one line per vertex, indecomposable for connected graphs.
-/

open scoped RealInnerProductSpace
open Submodule

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Lemma `lem:4-lines`, step `s4linessys`, Section 4 of [CGSS]: both signs of every vector. -/
def IsRepresentation.lineSystem (hx : X.IsRepresentation x) : LineSystem E where
  Φ := Set.range x ∪ Set.range (fun u ↦ -x u)
  finite := (Set.finite_range x).union (Set.finite_range _)
  inner_self := by
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact hx.inner_self u
    · rw [inner_neg_neg, hx.inner_self]
  neg_mem := by
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact Or.inr ⟨u, rfl⟩
    · exact Or.inl ⟨u, (neg_neg _).symm⟩
  inner_mem := by
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩) _ (⟨v, rfl⟩ | ⟨v, rfl⟩)
    all_goals
      simp only [inner_neg_left, inner_neg_right, neg_neg, isRepresentation_iff.mp hx u v]
      split_ifs <;> norm_num

/-- Lemma `lem:4-lines`, step `s4linessys`, Section 4 of [CGSS]: exactly one line per vertex. -/
theorem IsRepresentation.numLines_lineSystem (hx : X.IsRepresentation x) :
    hx.lineSystem.numLines = Fintype.card V := by
  have hd : Disjoint (Set.range x) (Set.range (fun u ↦ -x u)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
    exact hx.ne_neg u v hv.symm
  change (Set.range x ∪ Set.range (fun u ↦ -x u)).ncard / 2 = _
  have hn : Function.Injective (fun u ↦ -x u) := neg_injective.comp hx.injective
  rw [Set.ncard_union_eq hd (Set.finite_range _) (Set.finite_range _),
    Set.ncard_range_of_injective hx.injective,
    Set.ncard_range_of_injective hn, Nat.card_eq_fintype_card]
  omega

/-- Lemma `lem:4-lines`, Section 4 of [CGSS]: taking both signs does not change the span. -/
theorem IsRepresentation.span_lineSystem (hx : X.IsRepresentation x) :
    span ℝ hx.lineSystem.Φ = span ℝ (Set.range x) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact subset_span (Set.mem_range_self u)
    · exact neg_mem (subset_span (Set.mem_range_self u))
  · exact span_mono Set.subset_union_left

/-- Lemma `lem:4-lines`, Section 4 of [CGSS]: the family is represented in its own line system. -/
theorem IsRepresentation.isRepresentedIn_lineSystem (hx : X.IsRepresentation x) :
    X.IsRepresentedIn hx.lineSystem :=
  ⟨x, hx, fun u ↦ Or.inl (Set.mem_range_self u)⟩

/-- Lemma `lem:4-lines`, final step, Section 4 of [CGSS]: connectivity forbids an orthogonal
partition. Membership in either part propagates along a path in the represented graph. -/
theorem IsRepresentation.isIndecomposable_of_connected (hx : X.IsRepresentation x)
    (hX : X.Connected) : hx.lineSystem.IsIndecomposable := by
  classical
  intro P Q hPQ horth
  have hcover (u : V) : x u ∈ P ∨ x u ∈ Q := by
    change x u ∈ P ∪ Q
    rw [hPQ]
    exact Or.inl (Set.mem_range_self u)
  have hprop {u v : V} (h : X.Reachable u v) (hu : x u ∈ P) : x v ∈ P := by
    obtain ⟨p⟩ := h
    induction p with
    | nil => exact hu
    | @cons u w v huw p ih =>
      apply ih
      rcases hcover w with hw | hw
      · exact hw
      · have hz := horth _ hu _ hw
        rw [hx.inner_of_adj huw] at hz
        norm_num at hz
  by_cases hP : ∃ u, x u ∈ P
  · obtain ⟨u, hu⟩ := hP
    right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqΦ : q ∈ hx.lineSystem.Φ := hPQ ▸ Or.inr hq
    rcases hqΦ with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · have hz := horth _ (hprop (hX u v) hu) _ hq
      rw [hx.inner_self] at hz
      norm_num at hz
    · have hz := horth _ (hprop (hX u v) hu) _ hq
      rw [inner_neg_right, hx.inner_self] at hz
      norm_num at hz
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpΦ : p ∈ hx.lineSystem.Φ := hPQ ▸ Or.inl hp
    rcases hpΦ with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact hP ⟨u, hp⟩
    · have hu := (hcover u).resolve_left (fun h ↦ hP ⟨u, h⟩)
      have hz := horth _ hp _ hu
      rw [inner_neg_left, hx.inner_self] at hz
      norm_num at hz

end SimpleGraph
