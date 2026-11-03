import LineGraphs.Computations.C13
import LineGraphs.Computations.ModelTables
import LineGraphs.Representation.Basic

/-!
# Computation C13: the vectors of [CGSS], Corollary 5.10

The printed Steiner coordinates are carried into the project's fixed E₇ by the supplied
integer map. Both Gram matrices and root membership are checked in the kernel.
-/

open scoped BigOperators RealInnerProductSpace

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: an integer row vector after the supplied coordinate map. -/
def mappedRoot (rows : IntMatrix) (i : Fin 12) (j : Fin 8) : ℤ :=
  ∑ k : Fin 8, entry rows i k * entry rootMap k j

/-- C13, [CGSS] Corollary 5.10: the normalized vectors in the fixed E₇ coordinates. -/
noncomputable def vectors (rows : IntMatrix) (i : Fin 12) : EuclideanSpace ℝ (Fin 8) :=
  LineSystem.integerVector (1 / 2) (mappedRoot rows i)

/-- C13, [CGSS] Corollary 5.10: both printed families lie in the stated Steiner section. -/
theorem printed_roots_checked : ∀ rows ∈ [roots1, roots2], ∀ i : Fin 12,
    LineSystem.isE₈viaSteinerRoot (fun j ↦ entry rows i j) = true ∧
      (∑ j : Fin 4, entry rows i (j.val + 4)) = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the coordinate map multiplies squared norms by two. -/
theorem root_map_gram : ∀ i j : Fin 8,
    (∑ k : Fin 8, entry rootMap i k * entry rootMap j k) = if i = j then 2 else 0 := by
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: both mapped families are E₇ roots. -/
theorem roots_mem_E₇ : ∀ rows ∈ [roots1, roots2], ∀ i : Fin 12,
    vectors rows i ∈ LineSystem.E₇.Φ := by
  intro rows h i
  apply (LineSystem.integerVector_mem_E₇_iff _).mpr
  have hc : ∀ rows ∈ [roots1, roots2], ∀ i : Fin 12,
      LineSystem.isE₇Root (mappedRoot rows i) = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide +kernel
  exact hc rows h i

/-- C13, [CGSS] Corollary 5.10: the Gram matrices in doubled E₇ coordinates. -/
theorem gram_checked : ∀ p ∈ [(roots1, adjacency1), (roots2, adjacency2)],
    ∀ i j : Fin 12, LineSystem.integerInner (mappedRoot p.1 i) (mappedRoot p.1 j) =
      4 * (2 * (if i = j then 1 else 0) + entry p.2 i j) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the first vector family represents the first graph. -/
theorem representation_graph1 : graph1.IsRepresentation (vectors roots1) := by
  apply SimpleGraph.isRepresentation_iff.mpr
  intro i j
  rw [vectors, vectors, LineSystem.inner_integerVector,
    gram_checked (roots1, adjacency1) (by simp) i j]
  change (1 / 2 : ℝ) * (1 / 2) *
    (4 * (2 * (if i = j then 1 else 0) + entry adjacency1 i j) : ℤ) =
    if i = j then 2 else if entry adjacency1 i j = 1 then 1 else 0
  rcases checkAdjacency_entries adjacency1_checked i j with h | h <;>
    by_cases hij : i = j <;> norm_num [hij, h, checkAdjacency_diagonal adjacency1_checked]

/-- C13, [CGSS] Corollary 5.10: graph 1 is represented in the fixed E₇. -/
theorem isRepresentedIn_E₇_graph1 : graph1.IsRepresentedIn LineSystem.E₇ :=
  ⟨vectors roots1, representation_graph1, roots_mem_E₇ _ (by simp)⟩

/-- C13, [CGSS] Corollary 5.10: the second vector family represents the second graph. -/
theorem representation_graph2 : graph2.IsRepresentation (vectors roots2) := by
  apply SimpleGraph.isRepresentation_iff.mpr
  intro i j
  rw [vectors, vectors, LineSystem.inner_integerVector,
    gram_checked (roots2, adjacency2) (by simp) i j]
  change (1 / 2 : ℝ) * (1 / 2) *
    (4 * (2 * (if i = j then 1 else 0) + entry adjacency2 i j) : ℤ) =
    if i = j then 2 else if entry adjacency2 i j = 1 then 1 else 0
  rcases checkAdjacency_entries adjacency2_checked i j with h | h <;>
    by_cases hij : i = j <;> norm_num [hij, h, checkAdjacency_diagonal adjacency2_checked]

/-- C13, [CGSS] Corollary 5.10: graph 2 is represented in the fixed E₇. -/
theorem isRepresentedIn_E₇_graph2 : graph2.IsRepresentedIn LineSystem.E₇ :=
  ⟨vectors roots2, representation_graph2, roots_mem_E₇ _ (by simp)⟩

end Computations.C13
