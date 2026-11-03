/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9ChangI
import LineGraphs.Computations.CliqueBenchmarkChangI

/-! # The ChangI target in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

set_option maxRecDepth 10000

/-- The C22 target table is the actual ChangI graph of C9. -/
theorem changI_adj :
    ∀ i j, SimpleGraph.changI.Adj i j ↔ entry CliqueBenchmarkData.changI i j = 1 := by
  decide +kernel

/-- Identify the checked C22 table with the ChangI graph of C9. -/
noncomputable def changITableIso :
    graphOfMatrix Examples.changI_adjacency ≃g SimpleGraph.changI :=
  graphOfMatrixIso _ _ (Equiv.refl _) changI_adj

-- Computation C22, assertion 4
/-- The ChangI four-clique profile, assertion 4 of `comp:C22` (Remark 4.14). -/
theorem cliqueProfile_changI : SimpleGraph.changI.cliqueProfile 4 =
    Multiset.replicate 4 32 + Multiset.replicate 24 36 := by
  rw [← changITableIso.cliqueProfile_eq,
    ← cliqueProfile_sound Examples.changI_adjacency, Examples.changI_clique_profile]
  decide +kernel

end Computations.C22

