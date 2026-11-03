/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Switching
import LineGraphs.Seidel.EightVertexModels
import LineGraphs.Graphs.Basic

/-!
# The finite switching models in C22

The source graphs in `comp:C22` and the regular-switching lemmas of Remark 4.14.
-/

namespace SimpleGraph

/-- Switch the triangular graph by the edge set of `Z`, as in `comp:C22` of Remark 4.14. -/
def switchTriangular {n : ℕ} (Z : SimpleGraph (Fin n)) :
    SimpleGraph (⊤ : SimpleGraph (Fin n)).edgeSet :=
  (⊤ : SimpleGraph (Fin n)).lineGraph.switch {e | e.val ∈ Z.edgeSet}

/-- The triangular graph with one isolated vertex, the E₇ source in `comp:C22`. -/
def triangularAddOne (n : ℕ) :
    SimpleGraph ((⊤ : SimpleGraph (Fin n)).edgeSet ⊕ Fin 1) :=
  (⊤ : SimpleGraph (Fin n)).lineGraph ⊕g (⊥ : SimpleGraph (Fin 1))

/-- Switch the E₇ source by edges of `Z`, leaving its extra vertex outside the cut (C22). -/
def switchTriangularAddOne {n : ℕ} (Z : SimpleGraph (Fin n)) :
    SimpleGraph ((⊤ : SimpleGraph (Fin n)).edgeSet ⊕ Fin 1) :=
  (triangularAddOne n).switch {e | Sum.elim (fun a ↦ a.val ∈ Z.edgeSet) (fun _ ↦ False) e}

/-- The two triangles on `0,1,2` and `3,4,5`, the E₇ switching set in `comp:C22`. -/
def twoC3 : SimpleGraph (Fin 6) := fromRel fun i j ↦ i.val / 3 = j.val / 3

instance : DecidableRel twoC3.Adj := by unfold twoC3; infer_instance

/-- The cycle-sum labels of the two triangles used in `comp:C22`. -/
def twoC3.sumIso : (cycleGraph 3) ⊕g (cycleGraph 3) ≃g twoC3 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

/-- The explicit pair adjacency used to interpret the switching certificates of C22. -/
theorem switchTriangular_adj {n : ℕ} (Z : SimpleGraph (Fin n))
    (p q : {p : Fin n × Fin n // p.1 < p.2}) :
    (switchTriangular Z).Adj (completeGraphEdgeEquiv (Fin n) p)
        (completeGraphEdgeEquiv (Fin n) q) ↔
      p ≠ q ∧ ((p ≠ q ∧
        (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2)) ↔
        (Z.Adj p.1.1 p.1.2 ↔ Z.Adj q.1.1 q.1.2)) := by
  simp only [switchTriangular, switch_adj, Ne, (completeGraphEdgeEquiv (Fin n)).injective.eq_iff,
    lineGraph_completeGraph_adj, Set.mem_ofPred_eq, coe_completeGraphEdgeEquiv, mem_edgeSet]

/-- The empty switch in assertion 3 of `comp:C22` is the triangular graph itself. -/
theorem switchTriangular_bot (n : ℕ) :
    switchTriangular (⊥ : SimpleGraph (Fin n)) = (⊤ : SimpleGraph (Fin n)).lineGraph := by
  ext u v
  simp only [switchTriangular, switch_adj, edgeSet_bot, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_self, iff_true]
  exact and_iff_right_of_imp Adj.ne

end SimpleGraph
