import LineGraphs.Computations.C13Design
import LineGraphs.Computations.C15

/-!
# C15: the design flag graph in [CGSS], Example 5.13

The ten labelled triples give a `(6,3,10,5,2)` design. Its flag graph is the line graph of
its incidence graph; the certificate labels enumerate the thirty flags.
-/

namespace Computations.C15

/-- C15, [CGSS] Example 5.13: the ten blocks. -/
def blocks : Fin 10 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 1, 4}, {0, 2, 3}, {0, 3, 5}, {0, 4, 5},
    {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4}, {2, 4, 5}]

/-- C15, [CGSS] Example 5.13: the labelled two-design. -/
def design : Design (Fin 6) (Fin 10) 6 3 10 5 2 where
  card_points := rfl
  card_blocks := rfl
  block := blocks
  card_block := by decide +kernel
  card_blocksThrough := by decide +kernel
  card_blocksThroughPair := by decide +kernel
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

/-- C15, [CGSS] Example 5.13: the thirty flags. -/
def flagLabels : Fin 30 → Fin 6 × Fin 10 :=
  ![(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (4, 1), (0, 2), (2, 2), (3, 2), (0, 3), (3, 3),
  (5, 3), (0, 4), (4, 4), (5, 4), (1, 5), (2, 5), (5, 5), (1, 6), (3, 6), (4, 6), (1, 7), (3,
  7), (5, 7), (2, 8), (3, 8), (4, 8), (2, 9), (4, 9), (5, 9)]

/-- C15, [CGSS] Example 5.13: flags as incidence edges. -/
def flagEdge (i : Fin 30) : (C13.incidenceGraph design.block).edgeSet :=
  ⟨s(Sum.inl (flagLabels i).1, Sum.inr (flagLabels i).2),
    (show ∀ i : Fin 30, (C13.incidenceGraph design.block).Adj
      (.inl (flagLabels i).1) (.inr (flagLabels i).2) by decide +kernel) i⟩

/-- C15, [CGSS] Example 5.13: all flags occur exactly once. -/
theorem flag_edge_bijective : Function.Bijective flagEdge := by decide +kernel

/-- C15, [CGSS] Example 5.13: the first certificate graph is the design flag graph. -/
noncomputable def flagGraphIso : graph1 ≃g (C13.incidenceGraph design.block).lineGraph :=
  graphOfMatrixIso adjacency1_checked _ (Equiv.ofBijective flagEdge flag_edge_bijective)
    (show ∀ i j : Fin 30,
      (C13.incidenceGraph design.block).lineGraph.Adj (flagEdge i) (flagEdge j) ↔
        entry adjacency1 i j = 1 by decide +kernel)

end Computations.C15
