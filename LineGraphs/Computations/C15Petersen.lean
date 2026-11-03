import LineGraphs.Computations.C13Design
import LineGraphs.Computations.C15

/-!
# C15: the iterated Petersen line graph in [CGSS], Example 5.13

Petersen has the outer pentagon `0,…,4`, inner pentagram `5,…,9`, and spokes `i—(i+5)`.
The omitted edge labels were regenerated with SageMath 10.9 from the existing certificate's
construction; all maps and adjacencies below are independently checked by Lean.
-/

namespace Computations.C15

/-- C15, [CGSS] Example 5.13: the standard pentagon/pentagram Petersen graph. -/
def petersen : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun i j ↦
  (i.val < 5 ∧ j.val = (i.val + 1) % 5) ∨
  (5 ≤ i.val ∧ j.val = 5 + (i.val - 5 + 2) % 5) ∨
  (i.val < 5 ∧ j.val = i.val + 5)

/-- C15, [CGSS] Example 5.13, final blueprint remark: decide pentagon/pentagram adjacency. -/
instance petersenDecidable : DecidableRel petersen.Adj := inferInstanceAs (DecidableRel
  (SimpleGraph.fromRel _).Adj)

/-- C15, [CGSS] Example 5.13: Petersen's fifteen edges in the Sage order. -/
def lineLabels : Fin 15 → Fin 10 × Fin 10 :=
  ![(0, 1), (0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (3, 8), (4, 9), (5, 7),
  (5, 8), (6, 8), (6, 9), (7, 9)]

/-- C15, [CGSS] Example 5.13: the explicit vertices of the first line graph. -/
def lineEdge (i : Fin 15) : petersen.edgeSet :=
  ⟨s((lineLabels i).1, (lineLabels i).2),
    (show ∀ i : Fin 15, petersen.Adj (lineLabels i).1 (lineLabels i).2 by decide +kernel) i⟩

/-- C15, [CGSS] Example 5.13: all Petersen edges occur exactly once. -/
theorem line_edge_bijective : Function.Bijective lineEdge := by decide +kernel

/-- C15, [CGSS] Example 5.13: the thirty edges of the first line graph. -/
def doubleLineLabels : Fin 30 → Fin 15 × Fin 15 :=
  ![(0, 2), (1, 0), (1, 2), (3, 0), (3, 4), (4, 0), (4, 12), (5, 3), (5, 6), (5, 7), (6, 3),
  (7, 1), (8, 5), (8, 7), (8, 12), (9, 1), (9, 7), (9, 13), (10, 2), (10, 6), (11, 2), (11,
  8), (11, 10), (11, 12), (13, 4), (13, 12), (14, 6), (14, 9), (14, 10), (14, 13)]

/-- C15, [CGSS] Example 5.13: explicit vertices of `L(L(Petersen))`. -/
def doubleLineEdge (i : Fin 30) : petersen.lineGraph.edgeSet :=
  ⟨s(lineEdge (doubleLineLabels i).1, lineEdge (doubleLineLabels i).2),
    (show ∀ i : Fin 30, petersen.lineGraph.Adj
      (lineEdge (doubleLineLabels i).1) (lineEdge (doubleLineLabels i).2) by decide +kernel) i⟩

/-- C15, [CGSS] Example 5.13: all vertices of the second line graph occur once. -/
theorem double_line_edge_bijective : Function.Bijective doubleLineEdge := by decide +kernel

/-- C15, [CGSS] Example 5.13: the second certificate graph is `L(L(Petersen))`. -/
noncomputable def doubleLineGraphIso : graph2 ≃g petersen.lineGraph.lineGraph :=
  graphOfMatrixIso adjacency2_checked _
    (Equiv.ofBijective doubleLineEdge double_line_edge_bijective)
    (show ∀ i j : Fin 30, petersen.lineGraph.lineGraph.Adj (doubleLineEdge i) (doubleLineEdge j) ↔
      entry adjacency2 i j = 1 by decide +kernel)

end Computations.C15
