/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Frame
import LineGraphs.LineSystem.ModelSpans

/-!
# Computation C6 for E₇ and E₆

The coordinate frame matrices over the doubled integer roots of `E₇ = E₈ ∩ (e₇ - e₈)^⊥` and
`E₆ = E₇ ∩ (e₆ - e₇)^⊥` (steps `s3c6seven`, `s3c6six` of `blueprint/sec3-rootsystems.tex`):
`diag(144 I₆, 72 J₂)` and `diag(96 I₅, 32 J₃)`. Neither is scalar on `ℝ⁸`; on the spans, where
the last two (three) coordinates agree, the frame operators are `36 = 4 · 63 / 7` and
`24 = 4 · 36 / 6` times the identity (steps `s3frameSeven`, `s3frameSix`).
-/

open scoped RealInnerProductSpace
open Finset Submodule

namespace Computations.C6

open LineSystem

-- Computation C6
/-- C6, step `s3c6seven`: for `E₇`, `K = diag(144 I₆, 72 J₂)`. -/
theorem e₇_frame_matrix : ∀ k l : Fin 8,
    ∑ a : E₇.Index, E₇.root a k * E₇.root a l =
      if k.val < 6 then (if k = l then 144 else 0) else (if l.val < 6 then 0 else 72) := by
  decide +kernel

-- Computation C6
/-- C6, step `s3c6six`: for `E₆`, `K = diag(96 I₅, 32 J₃)`. -/
theorem e₆_frame_matrix : ∀ k l : Fin 8,
    ∑ a : E₆.Index, E₆.root a k * E₆.root a l =
      if k.val < 5 then (if k = l then 96 else 0) else (if l.val < 5 then 0 else 32) := by
  decide +kernel

end Computations.C6

namespace LineSystem

open Computations.C6

-- Lemma "the frame identity within the span", step s3frameSeven
/-- C6 for `E₇`: on its span (`x₆ = x₇` in `Fin 8`) the frame operator is `36` times the
identity. -/
theorem isFrame_E₇ : E₇.IsFrame 36 := by
  intro x hx
  have h67 : x 6 = x 7 := span_E₇_le_equalCoordinates hx
  ext k
  rw [E₇.integerModel.frameSum_apply]
  change 1 / 2 * (1 / 2) *
    ∑ j, ((∑ a : E₇.Index, E₇.root a k * E₇.root a j : ℤ) : ℝ) * x j = _
  simp only [e₇_frame_matrix, PiLp.smul_apply, smul_eq_mul]
  fin_cases k <;> simp [Fin.sum_univ_eight, h67] <;> ring

-- Lemma "the frame identity within the span", step s3frameSix
/-- C6 for `E₆`: on its span (`x₅ = x₆ = x₇` in `Fin 8`) the frame operator is `24` times the
identity. -/
theorem isFrame_E₆ : E₆.IsFrame 24 := by
  intro x hx
  have h := span_E₆_le_equalCoordinates hx
  have h67 : x 6 = x 7 := h.1
  have h56 : x 5 = x 6 := h.2
  ext k
  rw [E₆.integerModel.frameSum_apply]
  change 1 / 2 * (1 / 2) *
    ∑ j, ((∑ a : E₆.Index, E₆.root a k * E₆.root a j : ℤ) : ℝ) * x j = _
  simp only [e₆_frame_matrix, PiLp.smul_apply, smul_eq_mul]
  fin_cases k <;> simp [Fin.sum_univ_eight, h56, h67] <;> ring

end LineSystem
