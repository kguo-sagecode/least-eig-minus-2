/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.EightVertexModels
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Separating invariants for SE4

Section 4 of `cgss/proofs/reg8/reg8.tex`, the prerequisite `res:414-SE4` for
Remark 4.14 of [CGSS]. Triangles and four-cycles distinguish the models.
-/

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

-- SE4 (Remark 4.14), four-cycle invariant
/-- The number of four-cycles in SE4, computed by choosing two common neighbours
of each ordered pair of distinct vertices. Each cycle has two diagonals, each
counted in both orders, giving the divisor four. Chords are allowed. -/
def numFourCycles (X : SimpleGraph V) [DecidableRel X.Adj] : ℕ :=
  (∑ u, ∑ v, if u = v then 0 else (Fintype.card (X.commonNeighbors u v)).choose 2) / 4

/-- The four-cycle invariant of `res:414-SE4` is preserved by graph isomorphisms. -/
theorem Iso.numFourCycles_eq {X : SimpleGraph V} {Y : SimpleGraph W}
    [DecidableRel X.Adj] [DecidableRel Y.Adj] (e : X ≃g Y) :
    X.numFourCycles = Y.numFourCycles := by
  have hc (u v : V) : Fintype.card (X.commonNeighbors u v) =
      Fintype.card (Y.commonNeighbors (e u) (e v)) := by
    apply Fintype.card_congr
    exact e.toEquiv.subtypeEquiv (fun w ↦ by simp [mem_commonNeighbors, e.map_adj_iff])
  unfold numFourCycles
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro v _
  change (if u = v then 0 else _) = (if e u = e v then 0 else _)
  simp only [e.injective.eq_iff]
  split_ifs
  · rfl
  · congr 1
    exact hc u v

/-- Triangle counts in the invariant argument of `res:414-SE4` are isomorphism invariants. -/
theorem Iso.card_cliqueFinset_eq {X : SimpleGraph V} {Y : SimpleGraph W}
    [DecidableRel X.Adj] [DecidableRel Y.Adj] (e : X ≃g Y) (n : ℕ) :
    (X.cliqueFinset n).card = (Y.cliqueFinset n).card := by
  classical
  apply Finset.card_bij (fun s _ ↦ s.map e.toEquiv.toEmbedding)
  · intro s hs
    rw [mem_cliqueFinset_iff] at hs ⊢
    refine ⟨?_, by simpa using hs.card_eq⟩
    rw [Finset.coe_map]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    exact e.map_adj_iff.mpr (hs.isClique hu hv (fun h ↦ huv (congrArg e h)))
  · intro s _ t _ h
    exact Finset.map_injective _ h
  · intro t ht
    refine ⟨t.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · rw [mem_cliqueFinset_iff] at ht ⊢
      refine ⟨?_, by simpa using ht.card_eq⟩
      rw [Finset.coe_map]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
      exact e.symm.map_adj_iff.mpr (ht.isClique hu hv (fun h ↦ huv (congrArg e.symm h)))
    · simp [Finset.map_map]

set_option maxRecDepth 100000 in
/-- The triangle and four-cycle counts for the three two-regular models in SE4. -/
theorem two_regular_eight_invariants :
    ((cycleGraph 8).cliqueFinset 3).card = 0 ∧ (cycleGraph 8).numFourCycles = 0 ∧
    (cycleThreeFive.cliqueFinset 3).card = 1 ∧ cycleThreeFive.numFourCycles = 0 ∧
    (twoC4.cliqueFinset 3).card = 0 ∧ twoC4.numFourCycles = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The triangle and four-cycle counts for the six cubic models in SE4. -/
theorem cubic_eight_invariants :
    (twoK4.cliqueFinset 3).card = 8 ∧ twoK4.numFourCycles = 6 ∧
    (cubeGraph.cliqueFinset 3).card = 0 ∧ cubeGraph.numFourCycles = 6 ∧
    (wagnerGraph.cliqueFinset 3).card = 0 ∧ wagnerGraph.numFourCycles = 4 ∧
    (truncatedK33Graph.cliqueFinset 3).card = 1 ∧ truncatedK33Graph.numFourCycles = 3 ∧
    (twiceTruncatedK4Graph.cliqueFinset 3).card = 2 ∧ twiceTruncatedK4Graph.numFourCycles = 2 ∧
    (twoDiamondsGraph.cliqueFinset 3).card = 4 ∧ twoDiamondsGraph.numFourCycles = 2 := by
  decide +kernel

-- SE4 (Remark 4.14), uniqueness
/-- The six cubic models of `res:414-SE4` are pairwise nonisomorphic,
in the order `2K₄`, cube, Wagner, `Y₁`, `Y₂`, `Y₄` of reg8. -/
theorem cubic_eight_pairwise_not_iso :
    Pairwise (fun i j : Fin 6 ↦ ¬ Nonempty
      (![twoK4, cubeGraph, wagnerGraph, truncatedK33Graph, twiceTruncatedK4Graph,
        twoDiamondsGraph] i ≃g
        ![twoK4, cubeGraph, wagnerGraph, truncatedK33Graph, twiceTruncatedK4Graph,
          twoDiamondsGraph] j)) := by
  intro i j hij ⟨e⟩
  fin_cases i <;> fin_cases j <;> dsimp at e <;> first | exact hij rfl |
    (have ht := e.card_cliqueFinset_eq 3
     have hq := e.numFourCycles_eq
     obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
       cubic_eight_invariants
     omega)

/-- The three two-regular models in `res:414-SE4` are pairwise nonisomorphic. -/
theorem two_regular_eight_pairwise_not_iso :
    Pairwise (fun i j : Fin 3 ↦ ¬ Nonempty
      (![cycleGraph 8, cycleThreeFive, twoC4] i ≃g
        ![cycleGraph 8, cycleThreeFive, twoC4] j)) := by
  intro i j hij ⟨e⟩
  fin_cases i <;> fin_cases j <;> dsimp at e <;> first | exact hij rfl |
    (have ht := e.card_cliqueFinset_eq 3
     have hq := e.numFourCycles_eq
     obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := two_regular_eight_invariants
     omega)

end SimpleGraph
