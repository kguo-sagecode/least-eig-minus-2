/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.CliqueBenchmarkT8

/-! # The triangular target and its clique profile in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

/-- The lexicographic pairs decode the triangular table used by the C22 benchmark. -/
theorem triangular8_adj : ∀ i j,
    pairAdj (edgePairs8 i) (edgePairs8 j) ↔ entry CliqueBenchmarkData.t8 i j = 1 := by
  decide +kernel

/-- Identify the C22 triangular adjacency table with the actual line graph of `K₈`. -/
noncomputable def triangular8TableIso :
    graphOfMatrix Examples.t8_adjacency ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph :=
  graphOfMatrixIso _ _ edgeLabel8 (fun i j ↦ (edgeLabel8_adj i j).trans (triangular8_adj i j))

-- Computation C22, assertion 4
/-- The triangular graph's four-clique profile, assertion 4 of `comp:C22` (Remark 4.14). -/
theorem cliqueProfile_t8 : (⊤ : SimpleGraph (Fin 8)).lineGraph.cliqueProfile 4 =
    Multiset.replicate 28 40 := by
  rw [← triangular8TableIso.cliqueProfile_eq,
    ← cliqueProfile_sound Examples.t8_adjacency, Examples.t8_clique_profile]
  decide +kernel

end Computations.C22
