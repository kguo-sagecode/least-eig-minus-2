/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22PetersenModel

/-! # C22: switching by `cycleGraph 5` in the E6 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 1
/-- The `cycleGraph 5` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e6_switch_cycle5 :
    Nonempty (switchTriangular (cycleGraph 5) ≃g SimpleGraph.petersen) := by
  exact nonempty_iso_switchTriangular_of_check (cycleGraph 5) (SimpleGraph.petersen)
      edgePairs5 edgePairs5_bijective
      e6Cycle5Adj (C9.petersenAdj) e6Cycle5Permutation
      (by decide +kernel) petersen_adj (by decide +kernel)

end Computations.C22

