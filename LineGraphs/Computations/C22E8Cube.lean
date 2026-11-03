/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22ChangIModel

/-! # C22: switching by `cubeGraph` in the E8 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 3
/-- The `cubeGraph` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e8_switch_cube :
    Nonempty (switchTriangular (cubeGraph) ≃g SimpleGraph.changI) := by
  exact nonempty_iso_switchTriangular_of_check (cubeGraph) (SimpleGraph.changI)
      edgePairs8 edgePairs8_bijective
      e8CubeAdj (CliqueBenchmarkData.changI) e8CubePermutation
      (by decide +kernel) changI_adj (by decide +kernel)

end Computations.C22

