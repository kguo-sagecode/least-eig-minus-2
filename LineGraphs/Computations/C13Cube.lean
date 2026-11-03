import LineGraphs.Computations.C13Design

/-!
# C13: the line graph of the cube in [CGSS], the remark after Corollary 5.10

The cube has the eight binary triples as vertices, adjacent when exactly one coordinate
differs. Sage finds the displayed map from graph 1 to its twelve edges. Lean checks that these
are all the edges, without repetition, and checks every line-graph adjacency by kernel reduction.
-/

namespace Computations.C13

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: the binary three-cube `Q₃`. -/
def cube : SimpleGraph (Fin 2 × Fin 2 × Fin 2) := SimpleGraph.fromRel fun u v ↦
  (u.1 ≠ v.1 ∧ u.2 = v.2) ∨
  (u.1 = v.1 ∧ u.2.1 ≠ v.2.1 ∧ u.2.2 = v.2.2) ∨
  (u.1 = v.1 ∧ u.2.1 = v.2.1 ∧ u.2.2 ≠ v.2.2)

/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: decide cube adjacency. -/
instance cubeDecidable : DecidableRel cube.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: Sage's cube-edge labels. -/
def cubeEdgeLabels : Fin 12 → (Fin 2 × Fin 2 × Fin 2) × (Fin 2 × Fin 2 × Fin 2) :=
  ![((0, 0, 1), (0, 0, 0)), ((0, 1, 1), (0, 1, 0)), ((1, 1, 0), (1, 1, 1)),
    ((1, 0, 1), (1, 0, 0)), ((0, 0, 0), (0, 1, 0)), ((0, 1, 1), (1, 1, 1)),
    ((1, 1, 0), (1, 0, 0)), ((0, 0, 1), (1, 0, 1)), ((0, 1, 1), (0, 0, 1)),
    ((1, 1, 0), (0, 1, 0)), ((1, 0, 1), (1, 1, 1)), ((0, 0, 0), (1, 0, 0))]

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: each label is a cube edge. -/
def cubeEdge (i : Fin 12) : cube.edgeSet :=
  ⟨s((cubeEdgeLabels i).1, (cubeEdgeLabels i).2),
    (show ∀ i : Fin 12, cube.Adj (cubeEdgeLabels i).1 (cubeEdgeLabels i).2 by decide +kernel) i⟩

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: the labels enumerate the edges. -/
theorem cube_edge_bijective : Function.Bijective cubeEdge := by decide +kernel

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: check line-graph adjacency. -/
theorem cube_line_adjacency_checked : ∀ i j : Fin 12,
    cube.lineGraph.Adj (cubeEdge i) (cubeEdge j) ↔ entry adjacency1 i j = 1 := by
  decide +kernel

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: graph 1 is `L(Q₃)`. -/
noncomputable def cubeLineGraphIso : graph1 ≃g cube.lineGraph :=
  graphOfMatrixIso adjacency1_checked _ (Equiv.ofBijective cubeEdge cube_edge_bijective)
    cube_line_adjacency_checked

-- Corollary 5.10 (the following remark, C13)
/-- C13, [CGSS] Corollary 5.10, the following blueprint remark: identify graph 1 with `L(Q₃)`. -/
theorem nonempty_iso_cube_lineGraph : Nonempty (graph1 ≃g cube.lineGraph) :=
  ⟨cubeLineGraphIso⟩

end Computations.C13
