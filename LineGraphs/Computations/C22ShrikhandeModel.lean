/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Shrikhande
import LineGraphs.Computations.CliqueCertificates

/-! # The Shrikhande target in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

set_option maxRecDepth 10000

/-- The C22 target table is the actual Shrikhande graph of C9. -/
theorem shrikhande_adj :
    ∀ i j, SimpleGraph.shrikhande.Adj i j ↔ entry C9.shrikhandeAdj i j = 1 := by
  decide +kernel

/-- The Shrikhande adjacency table used by `comp:C22` passes the graph checker. -/
theorem shrikhande_adjacency : checkAdjacency 16 C9.shrikhandeAdj = true := by
  decide +kernel

/-- Identify the checked C22 table with the Shrikhande graph of C9. -/
noncomputable def shrikhandeTableIso :
    graphOfMatrix shrikhande_adjacency ≃g SimpleGraph.shrikhande :=
  graphOfMatrixIso _ _ (Equiv.refl _) shrikhande_adj

-- Computation C22, assertion 5
/-- The Shrikhande graph has no four-clique, assertion 5 of `comp:C22` (Remark 4.14). -/
theorem cliqueCount_shrikhande : (SimpleGraph.shrikhande.cliqueMultiset 4).card = 0 := by
  rw [shrikhandeTableIso.cliqueMultiset_map, Multiset.card_map,
    ← cliqueCount_sound shrikhande_adjacency]
  exact (by decide +kernel : cliqueCount 16 4 C9.shrikhandeAdj = 0)

end Computations.C22

