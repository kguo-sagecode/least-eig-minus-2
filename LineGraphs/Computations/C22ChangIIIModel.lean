/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9ChangIII
import LineGraphs.Computations.CliqueBenchmarkChangIII

/-! # The ChangIII target in `comp:C22` (Remark 4.14) -/

namespace Computations.C22

set_option maxRecDepth 10000

/-- The C22 target table is the actual ChangIII graph of C9. -/
theorem changIII_adj :
    ∀ i j, SimpleGraph.changIII.Adj i j ↔ entry CliqueBenchmarkData.changIII i j = 1 := by
  decide +kernel

/-- Identify the checked C22 table with the ChangIII graph of C9. -/
noncomputable def changIIITableIso :
    graphOfMatrix Examples.changIII_adjacency ≃g SimpleGraph.changIII :=
  graphOfMatrixIso _ _ (Equiv.refl _) changIII_adj

-- Computation C22, assertion 4
/-- The ChangIII four-clique profile, assertion 4 of `comp:C22` (Remark 4.14). -/
theorem cliqueProfile_changIII : SimpleGraph.changIII.cliqueProfile 4 =
    Multiset.replicate 10 33 + Multiset.replicate 18 35 := by
  rw [← changIIITableIso.cliqueProfile_eq,
    ← cliqueProfile_sound Examples.changIII_adjacency, Examples.changIII_clique_profile]
  decide +kernel

end Computations.C22

