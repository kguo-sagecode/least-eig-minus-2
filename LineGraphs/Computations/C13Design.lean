import LineGraphs.Computations.C13
import LineGraphs.Cited.HallConnor.Basic
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Computation C13: the flag graph in [CGSS], Corollary 5.10

The four triples form a `(4,3,4,3,2)` design. Its flag graph is the line graph of its incidence
graph. The supplied permutation identifies this graph with the first exceptional graph.
-/

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: the incidence graph, also used for the design in C15. -/
def incidenceGraph {P B : Type*} [DecidableEq P] (block : B → Finset P) :
    SimpleGraph (P ⊕ B) where
  Adj
    | .inl p, .inr b => p ∈ block b
    | .inr b, .inl p => p ∈ block b
    | _, _ => False
  symm.symm := by rintro (p | b) (q | c) <;> simp
  loopless.irrefl := by rintro (p | b) <;> simp

/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: decide incidence adjacency. -/
instance incidenceGraphDecidable {P B : Type*} [DecidableEq P] (block : B → Finset P) :
    DecidableRel (incidenceGraph block).Adj := fun u v ↦ by
  cases u <;> cases v <;> dsimp [incidenceGraph] <;> infer_instance

/-- C13 and C15, [CGSS] remarks after Corollary 5.10 and Example 5.13:
compute line adjacency by testing a common endpoint. -/
instance lineGraphDecidable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : DecidableRel G.lineGraph.Adj := fun e f ↦
  decidable_of_iff (e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V))
    SimpleGraph.lineGraph_adj_iff_exists.symm

/-- C13, [CGSS] Corollary 5.10: the four triples on four points. -/
def blocks : Fin 4 → Finset (Fin 4) := ![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}]

/-- C13, [CGSS] Corollary 5.10: the exceptional symmetric design. -/
def design : Design (Fin 4) (Fin 4) 4 3 4 3 2 where
  card_points := rfl
  card_blocks := rfl
  block := blocks
  card_block := by decide +kernel
  card_blocksThrough := by decide +kernel
  card_blocksThroughPair := by decide +kernel
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

/-- C13, [CGSS] Corollary 5.10: the flag labels from the certificate. -/
def flagLabels : Fin 12 → Fin 4 × Fin 4 :=
  ![(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (3, 1),
    (0, 2), (2, 2), (3, 2), (1, 3), (2, 3), (3, 3)]

/-- C13, [CGSS] Corollary 5.10: each flag is an edge of the incidence graph. -/
def flagEdge (i : Fin 12) : (incidenceGraph design.block).edgeSet :=
  ⟨s(Sum.inl (flagLabels i).1, Sum.inr (flagLabels i).2),
    (show ∀ i : Fin 12, (incidenceGraph design.block).Adj
      (.inl (flagLabels i).1) (.inr (flagLabels i).2) by decide +kernel) i⟩

/-- C13, [CGSS] Corollary 5.10: the flags enumerate all incidence edges exactly once. -/
theorem flag_edge_bijective : Function.Bijective flagEdge := by decide +kernel

/-- C13, [CGSS] Corollary 5.10: the flag table is an adjacency table. -/
theorem flag_adjacency_checked : checkAdjacency 12 flagAdjacency = true := by decide +kernel

/-- C13, [CGSS] Corollary 5.10: identify the table with the mathematical flag graph. -/
noncomputable def flagGraphIso : graphOfMatrix flag_adjacency_checked ≃g
    (incidenceGraph design.block).lineGraph :=
  graphOfMatrixIso flag_adjacency_checked _ (Equiv.ofBijective flagEdge flag_edge_bijective)
    (show ∀ i j : Fin 12, (incidenceGraph design.block).lineGraph.Adj (flagEdge i) (flagEdge j) ↔
      entry flagAdjacency i j = 1 by decide +kernel)

/-- C13, [CGSS] Corollary 5.10: the first graph is the flag graph of the `(4,3,2)` design. -/
theorem nonempty_iso_flagGraph : Nonempty (graph1 ≃g (incidenceGraph design.block).lineGraph) := by
  obtain ⟨e⟩ := nonempty_graphOfMatrix_iso adjacency1_checked flag_adjacency_checked
    (p := flagPermutation) (by decide +kernel)
  exact ⟨e.trans flagGraphIso⟩

end Computations.C13
