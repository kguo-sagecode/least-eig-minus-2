/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9ChangII
import LineGraphs.Computations.CliqueBenchmarkChangII

/-! # The ChangII target in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

set_option maxRecDepth 10000

/-- The C22 target table is the actual ChangII graph of C9. -/
theorem changII_adj :
    ∀ i j, SimpleGraph.changII.Adj i j ↔ entry CliqueBenchmarkData.changII i j = 1 := by
  decide +kernel

/-- Identify the checked C22 table with the ChangII graph of C9. -/
noncomputable def changIITableIso :
    graphOfMatrix Examples.changII_adjacency ≃g SimpleGraph.changII :=
  graphOfMatrixIso _ _ (Equiv.refl _) changII_adj

-- Computation C22, assertion 4
/-- The ChangII four-clique profile, assertion 4 of `comp:C22` (Remark 4.14). -/
theorem cliqueProfile_changII : SimpleGraph.changII.cliqueProfile 4 =
    Multiset.replicate 24 34 + Multiset.replicate 4 36 := by
  rw [← changIITableIso.cliqueProfile_eq,
    ← cliqueProfile_sound Examples.changII_adjacency, Examples.changII_clique_profile]
  decide +kernel

end Computations.C22

