/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E6Stars
import LineGraphs.Computations.C4E7Stars
import LineGraphs.Graphs.Basic

/-!
# The graphs of C4 for E₆ and E₇

For the ordered star `a' = e₁ + e₂`, `b' = -e₁ + e₃` of the blueprint (`E₆.hyp24` and
`E₇.hyp24`, at `Fin 8` indices 0, 1, 2), the orthogonality graph on Γa is the lattice graph
`L₂(3) = L(K_{3,3})` for E₆ and the complement of the triangular graph `T(6) = L(K₆)`, that is
the disjointness graph on the 2-subsets of a 6-set, for E₇. The graphs are written as in
`cgss/notation.md` §5. By `C4E6Stars.lean` and `C4E7Stars.lean`, the same holds for every
ordered star.

The labellings are tables found by search and checked by `decide +kernel`. In the 1-based
coordinates of the blueprint, and with the E₆ lattice rows indexed by the first coordinate, the
lattice labels are

* row 0: `-e₁+e₂`, `e₃+e₄`, `e₃-e₄`;
* row 1: `e₃+e₅`, `½(-e₁+e₂+e₃-e₄-e₅-e₆-e₇-e₈)`, `½(-e₁+e₂+e₃+e₄-e₅+e₆+e₇+e₈)`;
* row 2: `e₃-e₅`, `½(-e₁+e₂+e₃-e₄+e₅+e₆+e₇+e₈)`, `½(-e₁+e₂+e₃+e₄+e₅-e₆-e₇-e₈)`.

For E₇, the pair `{0, 1}` of `Fin 6` labels `-e₁+e₂`, and the pairs `{0, j}` with `j ≥ 2`
label half-vectors.
-/

open Computations C4 SimpleGraph

namespace LineSystem

/-- The position in `E₆.gammaLabel` of the vertex `(i, j)` of the lattice graph. -/
def E₆.latticeLabel (p : Fin 3 × Fin 3) : Fin 9 :=
  listFin 9 [0, 1, 2, 3, 8, 6, 4, 7, 5] ⟨3 * p.1.val + p.2.val, by omega⟩

/-- The lattice labels are a bijection. -/
noncomputable def E₆.latticeEquiv : Fin 3 × Fin 3 ≃ Fin 9 :=
  Equiv.ofBijective E₆.latticeLabel (by decide +kernel)

-- Computation C4
/-- C4: for the star `(e₁+e₂, -e₁+e₃)`, the orthogonality graph of E₆ is the lattice graph
`L₂(3) = L(K_{3,3})`. -/
noncomputable def E₆.latticeGraphIso :
    (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g E₆.hyp24.orthGraph :=
  RelIso.trans
    (show (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g
        graphOfMatrix (by decide +kernel : checkAdjacency 9 e6Adjacency = true) from
      { toEquiv := (completeBipartiteEdgeEquiv (Fin 3) (Fin 3)).symm.trans E₆.latticeEquiv
        map_rel_iff' := by
          intro e f
          obtain ⟨p, rfl⟩ := (completeBipartiteEdgeEquiv (Fin 3) (Fin 3)).surjective e
          obtain ⟨q, rfl⟩ := (completeBipartiteEdgeEquiv (Fin 3) (Fin 3)).surjective f
          rw [lineGraph_completeBipartiteGraph_adj]
          change entry e6Adjacency ((completeBipartiteEdgeEquiv (Fin 3) (Fin 3)).symm.trans
              E₆.latticeEquiv (completeBipartiteEdgeEquiv (Fin 3) (Fin 3) p))
            ((completeBipartiteEdgeEquiv (Fin 3) (Fin 3)).symm.trans
              E₆.latticeEquiv (completeBipartiteEdgeEquiv (Fin 3) (Fin 3) q)) = 1 ↔ _
          simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
          exact (by decide +kernel : ∀ p q : Fin 3 × Fin 3,
            entry e6Adjacency (E₆.latticeLabel p) (E₆.latticeLabel q) = 1 ↔
              p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)) p q })
    E₆.orthGraphIso

/-- The position in `E₇.gammaLabel` of the pair `{i, j}`, `i < j`, of `Fin 6`. -/
def E₇.pairLabel (p : {p : Fin 6 × Fin 6 // p.1 < p.2}) : Fin 15 :=
  ⟨[0, 0, 7, 9, 11, 13, 0, 0, 8, 10, 12, 14, 0, 0, 0, 1, 3, 6,
    0, 0, 0, 0, 5, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0][6 * p.1.1.val + p.1.2.val]?.getD 0 % 15,
    Nat.mod_lt _ (by decide)⟩

/-- The pair labels are a bijection. -/
noncomputable def E₇.pairEquiv : {p : Fin 6 × Fin 6 // p.1 < p.2} ≃ Fin 15 :=
  Equiv.ofBijective E₇.pairLabel (by decide +kernel)

-- Computation C4
/-- C4: for the star `(e₁+e₂, -e₁+e₃)`, the orthogonality graph of E₇ is the complement of the
triangular graph `T(6) = L(K₆)`: two 2-subsets of a 6-set are adjacent when they are disjoint. -/
noncomputable def E₇.triangularGraphComplIso :
    (completeGraph (Fin 6)).lineGraphᶜ ≃g E₇.hyp24.orthGraph :=
  RelIso.trans
    (show (completeGraph (Fin 6)).lineGraphᶜ ≃g
        graphOfMatrix (by decide +kernel : checkAdjacency 15 e7Adjacency = true) from
      { toEquiv := (completeGraphEdgeEquiv (Fin 6)).symm.trans E₇.pairEquiv
        map_rel_iff' := by
          intro e f
          obtain ⟨p, rfl⟩ := (completeGraphEdgeEquiv (Fin 6)).surjective e
          obtain ⟨q, rfl⟩ := (completeGraphEdgeEquiv (Fin 6)).surjective f
          rw [compl_lineGraph_completeGraph_adj]
          change entry e7Adjacency ((completeGraphEdgeEquiv (Fin 6)).symm.trans
              E₇.pairEquiv (completeGraphEdgeEquiv (Fin 6) p))
            ((completeGraphEdgeEquiv (Fin 6)).symm.trans
              E₇.pairEquiv (completeGraphEdgeEquiv (Fin 6) q)) = 1 ↔ _
          simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
          exact (by decide +kernel : ∀ p q : {p : Fin 6 × Fin 6 // p.1 < p.2},
            entry e7Adjacency (E₇.pairLabel p) (E₇.pairLabel q) = 1 ↔
              p ≠ q ∧ ¬(p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2)) p q })
    E₇.orthGraphIso

namespace Hyp24

variable (H : Hyp24 (EuclideanSpace ℝ (Fin 8)))

-- Computation C4
/-- C4 for every ordered star of E₆: the orthogonality graph is `L₂(3)`. -/
theorem nonempty_latticeGraph_iso_of_S_eq_E₆ (hS : H.S = E₆) :
    Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g H.orthGraph) := by
  obtain ⟨e⟩ := H.nonempty_orthGraph_iso_of_S_eq_E₆ hS
  exact ⟨E₆.latticeGraphIso.trans e⟩

-- Computation C4
/-- C4 for every ordered star of E₇: the orthogonality graph is the complement of `T(6)`. -/
theorem nonempty_triangularGraph_compl_iso_of_S_eq_E₇ (hS : H.S = E₇) :
    Nonempty ((completeGraph (Fin 6)).lineGraphᶜ ≃g H.orthGraph) := by
  obtain ⟨e⟩ := H.nonempty_orthGraph_iso_of_S_eq_E₇ hS
  exact ⟨E₇.triangularGraphComplIso.trans e⟩

end Hyp24

end LineSystem
