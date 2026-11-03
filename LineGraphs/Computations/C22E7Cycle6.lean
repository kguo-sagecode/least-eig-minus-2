/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22ShrikhandeModel

/-! # C22: switching by `cycleGraph 6` in the E7 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 2
/-- The `cycleGraph 6` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e7_switch_cycle6 :
    Nonempty (switchTriangularAddOne (cycleGraph 6) ≃g SimpleGraph.shrikhande) := by
  exact nonempty_iso_switchTriangularAddOne_of_check (cycleGraph 6) (SimpleGraph.shrikhande)
      e7Cycle6Adj (C9.shrikhandeAdj) e7Cycle6Permutation
      (by decide +kernel) shrikhande_adj (by decide +kernel)

end Computations.C22

