/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C7Data
import LineGraphs.Computations.C3A

/-!
# The sharp example for Theorem 4.3

C7 of the Section 4 blueprint: 36 roots of `E₈`, with a vertex of valency 28.
-/

namespace Computations.C7

set_option maxRecDepth 4000

/-- C7, Theorem 4.3 of [CGSS]: the graph defined by the integer vectors. -/
def graph : SimpleGraph (Fin 36) := SimpleGraph.integerGraph vectors 9

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.integerGraph vectors 9).Adj)

/-- C7, step `s4c7ip`, of [CGSS]: every vector has squared norm 18 before scaling. -/
theorem norms_checked : ∀ i, LineSystem.integerInner (vectors i) (vectors i) = 18 := by
  decide +kernel

/-- C7, step `s4c7ip`, of [CGSS]: distinct vectors have product zero or nine. -/
theorem products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (vectors i) (vectors j) = 0 ∨
      LineSystem.integerInner (vectors i) (vectors j) = 9 := by
  decide +kernel

/-- C7, step `s4c7mem`, of [CGSS]: each integer row decodes as a root of model (i). -/
theorem roots_checked : ∀ i, LineSystem.isE₈viaA₈Root (vectors i) = true := by
  decide +kernel

/-- C7 of [CGSS]: the displayed vectors represent the graph in model (i). -/
theorem isRepresentedIn_E₈viaA₈ : graph.IsRepresentedIn LineSystem.E₈viaA₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 3) (vectors i), ?_, ?_⟩
  · exact SimpleGraph.integerGraph_isRepresentation vectors 9 (1 / 3) (by norm_num)
      norms_checked products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈viaA₈_iff _).mpr (roots_checked i)

/-- C7 and Theorem 4.3, step `s43three`, of [CGSS]: transport the certified
representation to the default model of `E₈` using C3. -/
theorem isRepresentedIn_E₈ : graph.IsRepresentedIn LineSystem.E₈ :=
  isRepresentedIn_E₈viaA₈.of_iso LineSystem.E₈viaA₈.isoE₈

/-- C7 of [CGSS]: `y₁` has exactly 28 neighbours. -/
theorem degree_zero : graph.degree 0 = 28 := by decide +kernel

end Computations.C7

namespace SimpleGraph

/-- Theorem 4.3, assertion 3, of [CGSS]: C7 attains both the order bound
and the valency bound. The vertex type `Fin 36` records the order. -/
theorem exists_isRepresentedIn_E₈_card_36 :
    ∃ (X : SimpleGraph (Fin 36)) (_ : DecidableRel X.Adj),
      X.IsRepresentedIn LineSystem.E₈ ∧ ∃ u, X.degree u = 28 :=
  ⟨Computations.C7.graph, inferInstance, Computations.C7.isRepresentedIn_E₈,
    0, Computations.C7.degree_zero⟩

end SimpleGraph
