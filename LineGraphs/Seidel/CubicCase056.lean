/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.CubicVerifier

/-! # SE4: the local branch with neighbourhood `{0, 5, 6}` at vertex 1 -/

namespace SimpleGraph.CubicEight

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks every degree-compatible completion in this branch.
/-- The `{0, 5, 6}` branch of the local case split for `res:414-SE4` (Remark 4.14). -/
theorem check_completions_056 :
    checkCompletions checkCertificate [2, 3, 4, 5, 6, 7]
      (Function.update initialRows 1 {0, 5, 6}) = true := by
  decide +kernel

end SimpleGraph.CubicEight
