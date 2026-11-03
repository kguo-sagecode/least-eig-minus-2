/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Petersen
import LineGraphs.Computations.CliqueCertificates

/-! # The Petersen target in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

set_option maxRecDepth 10000

/-- The C22 target table is the actual Petersen graph of C9. -/
theorem petersen_adj :
    ∀ i j, SimpleGraph.petersen.Adj i j ↔ entry C9.petersenAdj i j = 1 := by
  decide +kernel

/-- The Petersen adjacency table used by `comp:C22` passes the graph checker. -/
theorem petersen_adjacency : checkAdjacency 10 C9.petersenAdj = true := by
  decide +kernel

/-- Identify the checked C22 table with the Petersen graph of C9. -/
noncomputable def petersenTableIso :
    graphOfMatrix petersen_adjacency ≃g SimpleGraph.petersen :=
  graphOfMatrixIso _ _ (Equiv.refl _) petersen_adj

end Computations.C22

