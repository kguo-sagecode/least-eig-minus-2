/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Checker

/-!
# C16: order-16 agreement checks, chunk 3

Four first-row indices per file bound kernel verification time and memory.
-/

namespace Computations.C16

/-- C16, Hypothesis 6.1: first row indices 12 through 15. -/
theorem h16_agreement_chunk3 :
    ((List.range' 12 4).all (checkAgreementRow 16 16 h16Rows)) = true := by
  decide +kernel

end Computations.C16
