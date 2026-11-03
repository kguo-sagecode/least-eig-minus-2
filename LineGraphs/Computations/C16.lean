/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Order2
import LineGraphs.Computations.C16Order4
import LineGraphs.Computations.C16Order8
import LineGraphs.Computations.C16Order16
import LineGraphs.Computations.C16Geometry

/-!
# Computation C16: Hadamard matrices

The five certificate matrices satisfy Mathlib's `Matrix.IsHadamard`. The sound Boolean
checker proves Hypothesis 6.1 with `x = 4` for Paley-12 and `x = n` for the four Sylvester
examples. `C16Geometry` proves the count, dimension, and angles of the 66 Paley lines.
-/

open Matrix

namespace Computations.C16

/-- C16: the general blueprint identity `PᵀP = n²I/2 - nJ/2`, specialized to Paley-12. -/
theorem h12_transpose_hadamardPairs_mul :
    h12.hadamardPairsᵀ * h12.hadamardPairs =
      (72 : ℝ) • 1 - (6 : ℝ) • Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  convert h12_isHadamard.transpose_hadamardPairs_mul using 1
  norm_num

/-- C16: all five instances of Hypothesis 6.1, with their stated parameters. -/
theorem fourRow_agreements :
    h12_isHadamard.FourRowAgreement 4 ∧ h2_isHadamard.FourRowAgreement 2 ∧
      h4_isHadamard.FourRowAgreement 4 ∧ h8_isHadamard.FourRowAgreement 8 ∧
      h16_isHadamard.FourRowAgreement 16 :=
  ⟨h12_fourRowAgreement, h2_fourRowAgreement, h4_fourRowAgreement,
    h8_fourRowAgreement, h16_fourRowAgreement⟩

end Computations.C16
