/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22ChangIIModel

/-! # C22: switching by `twiceTruncatedK4Graph` in the E8 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 3
/-- The `twiceTruncatedK4Graph` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e8_switch_twiceTruncatedK4 :
    Nonempty (switchTriangular (twiceTruncatedK4Graph) ≃g SimpleGraph.changII) := by
  exact nonempty_iso_switchTriangular_of_check (twiceTruncatedK4Graph) (SimpleGraph.changII)
      edgePairs8 edgePairs8_bijective
      e8TwiceTruncatedK4Adj (CliqueBenchmarkData.changII) e8TwiceTruncatedK4Permutation
      (by decide +kernel) changII_adj (by decide +kernel)

end Computations.C22

