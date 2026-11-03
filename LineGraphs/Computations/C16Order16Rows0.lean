/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Data
import LineGraphs.Computations.C16Checker

/-!
# C16: order-16 agreement checks, chunk 0

Four first-row indices per file bound kernel verification time and memory.
-/

namespace Computations.C16

/-- C16, Hypothesis 6.1: first row indices zero and one. -/
theorem h16_agreement_chunk0_left :
    ((List.range' 0 2).all (checkAgreementRow 16 16 h16Rows)) = true := by
  decide +kernel

/-- C16, Hypothesis 6.1: first row indices two and three. -/
theorem h16_agreement_chunk0_right :
    ((List.range' 2 2).all (checkAgreementRow 16 16 h16Rows)) = true := by
  decide +kernel

/-- C16, Hypothesis 6.1: first row indices zero through three. -/
theorem h16_agreement_chunk0 :
    ((List.range' 0 4).all (checkAgreementRow 16 16 h16Rows)) = true := by
  rw [show List.range' 0 4 = List.range' 0 2 ++ List.range' 2 2 by decide, List.all_append,
    h16_agreement_chunk0_left, h16_agreement_chunk0_right]
  rfl

end Computations.C16
