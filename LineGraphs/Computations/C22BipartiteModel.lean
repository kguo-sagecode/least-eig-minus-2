/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Graphs.Basic

/-! # The lattice target and its clique count in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

noncomputable local instance : Fintype
    (completeBipartiteGraph (Fin 4) (Fin 4)).edgeSet := Fintype.ofFinite _

/-- The lattice adjacency table for `comp:C22` passes the graph checker. -/
theorem lattice44_adjacency : checkAdjacency 16 lattice44Adj = true := by decide +kernel

/-- Identify the product-labelled table with the actual line graph of `K₄,₄` (C22). -/
noncomputable def lattice44TableIso : graphOfMatrix lattice44_adjacency ≃g
    (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph := by
  apply graphOfMatrixIso _ _
    (finProdFinEquiv.symm.trans (completeBipartiteEdgeEquiv (Fin 4) (Fin 4)))
  intro i j
  simp only [Equiv.trans_apply, lineGraph_completeBipartiteGraph_adj]
  exact (by decide +kernel : ∀ i j : Fin 16,
    ((finProdFinEquiv.symm i : Fin 4 × Fin 4) ≠ finProdFinEquiv.symm j ∧
      ((finProdFinEquiv.symm i : Fin 4 × Fin 4).1 = (finProdFinEquiv.symm j : Fin 4 × Fin 4).1 ∨
       (finProdFinEquiv.symm i : Fin 4 × Fin 4).2 = (finProdFinEquiv.symm j : Fin 4 × Fin 4).2)) ↔
      entry lattice44Adj i j = 1) i j

-- Computation C22, assertion 5
/-- The line graph of `K₄,₄` has eight four-cliques, assertion 5 of `comp:C22` (Remark 4.14). -/
theorem cliqueCount_lineGraph_completeBipartite :
    ((completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph.cliqueMultiset 4).card = 8 := by
  rw [lattice44TableIso.cliqueMultiset_map, Multiset.card_map,
    ← cliqueCount_sound lattice44_adjacency]
  exact (by decide +kernel : cliqueCount 16 4 lattice44Adj = 8)

end Computations.C22
