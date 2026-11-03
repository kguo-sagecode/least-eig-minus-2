/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22ChangIIIModel

/-! # C22: switching by `truncatedK33Graph` in the E8 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 3
/-- The `truncatedK33Graph` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e8_switch_truncatedK33 :
    Nonempty (switchTriangular (truncatedK33Graph) ≃g SimpleGraph.changIII) := by
  exact nonempty_iso_switchTriangular_of_check (truncatedK33Graph) (SimpleGraph.changIII)
      edgePairs8 edgePairs8_bijective
      e8TruncatedK33Adj (CliqueBenchmarkData.changIII) e8TruncatedK33Permutation
      (by decide +kernel) changIII_adj (by decide +kernel)

end Computations.C22

