/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22ChangIIModel

/-! # C22: switching by `cycleGraph 8` in the E8 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 3
/-- The `cycleGraph 8` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e8_switch_cycle8 :
    Nonempty (switchTriangular (cycleGraph 8) ≃g SimpleGraph.changII) := by
  exact nonempty_iso_switchTriangular_of_check (cycleGraph 8) (SimpleGraph.changII)
      edgePairs8 edgePairs8_bijective
      e8Cycle8Adj (CliqueBenchmarkData.changII) e8Cycle8Permutation
      (by decide +kernel) changII_adj (by decide +kernel)

end Computations.C22

