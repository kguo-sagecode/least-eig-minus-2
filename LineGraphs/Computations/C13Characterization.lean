/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C13Design
import LineGraphs.LineGraphSpectra.DesignGraphs
import LineGraphs.Representation.ClawsCriteria

/-! # Non-characterization as a flag graph in [CGSS], Corollary 5.10 -/

namespace Computations.C13

attribute [-instance] lineGraphDecidable in
-- Corollary 5.10
/-- Corollary 5.10 of [CGSS]: the `(4,3,4,3,2)` design is an exception to
characterization in the sense of Implicit hypothesis 6.
Its cospectral mate has an induced claw, whereas every flag graph is claw-free. -/
theorem not_flagGraphCharacterized : ¬ design.FlagGraphCharacterized := by
  classical
  intro h
  let e₁ : graph1 ≃g design.flagGraph := nonempty_iso_flagGraph.some
  have hs : design.flagGraph.Cospectral graph2 := e₁.symm.cospectral.trans cospectral
  obtain ⟨P, B, _, _, _, _, D, ⟨e⟩⟩ := h _ graph2 hs
  have hc : graph2.ClawFree := e.clawFree_iff.mpr D.incidenceGraph.lineGraph_clawFree
  apply (graph2.clawFree_iff_forall_not_isClaw.mp hc) 4 {0, 1, 10}
  obtain ⟨h0, h1, h10, h01, h010, h110⟩ := graph2_claw
  refine ⟨by decide, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · intro v hv w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      simp_all only [SimpleGraph.irrefl, not_false_eq_true, SimpleGraph.adj_comm]

end Computations.C13
