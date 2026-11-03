/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# A connected spanning set

Lemma (a connected spanning set), `lem:sec3-connected-span` of
`blueprint/sec3-rootsystems.tex`, the spanning criterion for indecomposability used for the
models of Section 3 of [CGSS] and in Theorem 3.6.
-/

open Submodule
open scoped RealInnerProductSpace

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Steps `s3connedge` to `s3connother` of `lem:sec3-connected-span` (Section 3 of [CGSS]):
if the part `P` contains a vertex of the connected graph on `B`, it contains `B`, and the
other part is empty. -/
theorem eq_empty_of_connected_spanning_of_mem (S : LineSystem V) {B : Set V}
    (hB : B ⊆ S.Φ) (hspan : span ℝ S.Φ ≤ span ℝ B)
    (hconn : (SimpleGraph.fromRel fun r s : B ↦ ⟪(r : V), s⟫ ≠ 0).Connected)
    {P Q : Set V} (hPQ : P ∪ Q = S.Φ) (horth : ∀ p ∈ P, ∀ q ∈ Q, ⟪p, q⟫ = 0)
    {b₀ : B} (hb₀ : (b₀ : V) ∈ P) : Q = ∅ := by
  set G := SimpleGraph.fromRel fun r s : B ↦ ⟪(r : V), s⟫ ≠ 0
  -- s3connedge: an edge does not cross the partition.
  have hstep : ∀ {a b : B}, G.Adj a b → (a : V) ∈ P → (b : V) ∈ P := by
    intro a b hab ha
    have hb : (b : V) ∈ P ∪ Q := hPQ ▸ hB b.property
    rcases hb with hb | hb
    · exact hb
    · exfalso
      have h0 := horth a ha b hb
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
      · exact h h0
      · exact h (by rw [real_inner_comm]; exact h0)
  -- s3connpath: all of `B` lies in `P`.
  have hwalk : ∀ {a b : B} (_ : G.Walk a b), (a : V) ∈ P → (b : V) ∈ P := by
    intro a b w
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun ha ↦ ih (hstep h ha)
  have hBP : ∀ b : B, (b : V) ∈ P := fun b ↦ hwalk (hconn.preconnected b₀ b).some hb₀
  -- s3connother: a vector of `Q` is orthogonal to the span, hence has norm zero.
  rw [Set.eq_empty_iff_forall_notMem]
  intro q hq
  have hqΦ : q ∈ S.Φ := hPQ ▸ Or.inr hq
  have hle : span ℝ B ≤ (ℝ ∙ q)ᗮ := by
    rw [span_le]
    intro b hb
    rw [SetLike.mem_coe, mem_orthogonal_singleton_iff_inner_right]
    rw [real_inner_comm]
    exact horth b (hBP ⟨b, hb⟩) q hq
  have hq0 := hle (hspan (subset_span hqΦ))
  rw [mem_orthogonal_singleton_iff_inner_right, S.inner_self q hqΦ] at hq0
  norm_num at hq0

-- Lemma "a connected spanning set"
/-- Lemma (a connected spanning set), `lem:sec3-connected-span` (Section 3 of [CGSS]): if
`B ⊆ Φ(S)` spans the span of `Φ(S)` and its graph, joining distinct roots of nonzero inner
product, is connected (hence `B` is nonempty), then `S` is indecomposable. -/
theorem isIndecomposable_of_connected_spanning (S : LineSystem V) {B : Set V}
    (hB : B ⊆ S.Φ) (hspan : span ℝ S.Φ ≤ span ℝ B)
    (hconn : (SimpleGraph.fromRel fun r s : B ↦ ⟪(r : V), s⟫ ≠ 0).Connected) :
    S.IsIndecomposable := by
  intro P Q hPQ horth
  obtain ⟨b₀⟩ := hconn.nonempty
  have hb : (b₀ : V) ∈ P ∪ Q := hPQ ▸ hB b₀.property
  rcases hb with hb | hb
  · exact Or.inr (S.eq_empty_of_connected_spanning_of_mem hB hspan hconn hPQ horth hb)
  · refine Or.inl (S.eq_empty_of_connected_spanning_of_mem hB hspan hconn
      ((Set.union_comm Q P).trans hPQ) (fun q hq p hp ↦ ?_) hb)
    rw [real_inner_comm]
    exact horth p hp q hq

end LineSystem
