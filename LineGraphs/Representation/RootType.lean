/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Lines
import LineGraphs.LineSystem.SpanExtension
import LineGraphs.LineSystem.RootType

/-!
# The classification interface needed by Section 4

Theorem 3.6 of [CGSS] classifies nonempty maximal indecomposable line systems
by `RootType.model`. This module keeps that classification as an explicit hypothesis
and proves the remaining steps, including preservation of the dimension of the span.
`RootTypeClassified.lean` discharges it in the unconditional theorem
`IsRepresentation.exists_isRepresentedIn_rootType`.
-/

open Submodule Module

namespace SimpleGraph

variable {V E : Type*} [Finite V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Section 4 tools, using Theorem 3.6 of [CGSS]: the exact classification
consequence needed to put a connected representation in a model of the same
rank. All steps apart from classification follow from `lem:4-lines`,
`lem:sec3-extension`, and span transport. -/
theorem IsRepresentation.exists_isRepresentedIn_rootType_of_classification
    (hx : X.IsRepresentation x) (hX : X.Connected)
    (hclass : ∀ S : LineSystem E, S.Φ.Nonempty → S.IsMaximal → S.IsIndecomposable →
      ∃ t : LineSystem.RootType, Nonempty (S.Iso t.model)) :
    ∃ t : LineSystem.RootType, X.IsRepresentedIn t.model ∧
      t.rank = finrank ℝ (span ℝ (Set.range x)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hne : hx.lineSystem.Φ.Nonempty := by
    obtain ⟨u⟩ := hX.nonempty
    exact ⟨x u, Or.inl (Set.mem_range_self u)⟩
  have hi := hx.isIndecomposable_of_connected hX
  have hext : ∃ S : LineSystem E, hx.lineSystem.Φ ⊆ S.Φ ∧
      span ℝ S.Φ = span ℝ hx.lineSystem.Φ ∧ S.IsMaximal ∧ S.IsIndecomposable := by
    by_cases hm : hx.lineSystem.IsMaximal
    · exact ⟨hx.lineSystem, Set.Subset.rfl, rfl, hm, hi⟩
    · obtain ⟨S, hS, _, hspan, hmax, hind, _⟩ :=
        hx.lineSystem.exists_maximal_extension_span hne hi hm
      exact ⟨S, hS.subset, hspan, hmax, hind⟩
  obtain ⟨S, hS, hspan, hmax, hind⟩ := hext
  obtain ⟨t, ⟨e⟩⟩ := hclass S (hne.mono hS) hmax hind
  refine ⟨t, (hx.isRepresentedIn_lineSystem.mono hS).of_iso e, ?_⟩
  rw [← t.finrank_span_model, ← e.finrank_span_eq, hspan, hx.span_lineSystem]

end SimpleGraph
