/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Coordinates

/-!
# Exceptional coordinate sets for Remark 3.11

The coordinate spaces and root sets in `def:rem-exceptional` of
`blueprint/sec3-remark311.tex`. The E₇ and E₆ spaces here use the signs in that
definition; they are not the equal-coordinate embeddings of `LineSystem.E₇` and
`LineSystem.E₆`.
-/

open scoped RealInnerProductSpace

namespace RootSetModel

-- Remark 3.11, def:rem-exceptional
/-- The E₈ coordinate set of `def:rem-exceptional`, Remark 3.11, with even half-root sign parity. -/
noncomputable def E₈ : Set (EuclideanSpace ℝ (Fin 8)) := LineSystem.E₈.Φ

/-- The E₇ space in `def:rem-exceptional`: coordinates 7 and 8 have sum zero. -/
noncomputable def e₇Space : Submodule ℝ (EuclideanSpace ℝ (Fin 8)) :=
  (innerₗ (EuclideanSpace ℝ (Fin 8)) (unit 6 + unit 7)).ker

/-- The E₆ space in `def:rem-exceptional`: coordinates 6 and 7 agree and are
opposite to coordinate 8. -/
noncomputable def e₆Space : Submodule ℝ (EuclideanSpace ℝ (Fin 8)) :=
  e₇Space ⊓ (innerₗ (EuclideanSpace ℝ (Fin 8)) (unit 5 - unit 6)).ker

/-- The E₇ coordinate root set of `def:rem-exceptional` in Remark 3.11. -/
noncomputable def E₇ : Set e₇Space := Subtype.val ⁻¹' E₈

/-- The E₆ coordinate root set of `def:rem-exceptional` in Remark 3.11. -/
noncomputable def E₆ : Set e₆Space := Subtype.val ⁻¹' E₈

/-- The F₄ coordinate root set of `def:rem-exceptional` in Remark 3.11. -/
noncomputable def F₄ : Set (EuclideanSpace ℝ (Fin 4)) :=
  Dn 4 ∪ axisRoots 4 1 ∪ halfRoots 4

/-- The zero-sum plane for G₂ in `def:rem-exceptional` of Remark 3.11. -/
noncomputable def g₂Space : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (LineSystem.coordinateSum 3).ker

/-- A positive long G₂ root in `eq:G-roots`: one coordinate is doubled, and the
other two are minus one. -/
noncomputable def g₂LongRoot (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  (3 : ℝ) • unit i - ∑ j : Fin 3, unit j

/-- The G₂ coordinate root set of `def:rem-exceptional` in Remark 3.11. -/
noncomputable def G₂ : Set g₂Space :=
  Subtype.val ⁻¹' ((LineSystem.An 2).Φ ∪
    {x | ∃ i, x = g₂LongRoot i ∨ x = -g₂LongRoot i})

/-- The explicit E₇ equation of `def:rem-exceptional`. -/
theorem mem_e₇Space (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₇Space ↔ x 6 + x 7 = 0 := by
  change ⟪unit 6 + unit 7, x⟫ = 0 ↔ _
  simp [inner_add_left, unit, EuclideanSpace.inner_single_left]

/-- The explicit E₆ equations of `def:rem-exceptional`. -/
theorem mem_e₆Space (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₆Space ↔ x 5 = x 6 ∧ x 6 = -x 7 := by
  change (x ∈ e₇Space ∧ ⟪unit 5 - unit 6, x⟫ = 0) ↔ _
  rw [mem_e₇Space]
  simp only [inner_sub_left, unit, EuclideanSpace.inner_single_left, map_one, one_mul]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end RootSetModel
