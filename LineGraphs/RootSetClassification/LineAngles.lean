/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Angles
import LineGraphs.RootSetClassification.LineRepresentatives

/-!
# The angles occurring between root lines

The angle-set formulation of steps `rCallowed` and `rCoccurrence` in
Theorem C of the blueprint for Remark 3.11 of [CGSS]. Angles depend only on the actual lines.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ Ψ : Set V}

/-- The angles occurring between distinct root lines in Theorem C of the blueprint for Remark 3.11
of [CGSS]. -/
def lineAngles (Φ : Set V) : Set ℝ :=
  {θ | ∃ r ∈ Φ, ∃ s ∈ Φ, s ∉ ℝ ∙ r ∧ lineAngle r s = θ}

/-- Nonzero rescaling leaves line angles unchanged (`facts:rem-angles`). -/
theorem lineAngle_smul {r s : V} (hr : r ≠ 0) (hs : s ≠ 0)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    lineAngle (a • r) (b • s) = lineAngle r s := by
  unfold lineAngle
  congr 1
  simp only [real_inner_smul_left, real_inner_smul_right, abs_mul, norm_smul,
    Real.norm_eq_abs]
  field_simp

/-- Any nonzero representatives of the same two lines have the same angle (`rCclassicalsame`). -/
theorem lineAngle_eq_of_same_lines {r s r' s' : V}
    (hr : r ≠ 0) (hs : s ≠ 0) (hr' : r' ≠ 0) (hs' : s' ≠ 0)
    (hlr : ℝ ∙ r' = ℝ ∙ r) (hls : ℝ ∙ s' = ℝ ∙ s) :
    lineAngle r' s' = lineAngle r s := by
  have hmr : r' ∈ ℝ ∙ r := hlr ▸ mem_span_singleton_self r'
  have hms : s' ∈ ℝ ∙ s := hls ▸ mem_span_singleton_self s'
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hmr
  obtain ⟨b, rfl⟩ := mem_span_singleton.mp hms
  apply lineAngle_smul hr hs
  · intro he; exact hr' (by simp [he])
  · intro he; exact hs' (by simp [he])

/-- The occurrence set is determined by the actual line set (`rCclassicalsame`). -/
theorem lineAngles_eq_of_rootLines_eq (hΦ : IsRootSet Φ) (hΨ : IsRootSet Ψ)
    (he : rootLines Φ = rootLines Ψ) : lineAngles Φ = lineAngles Ψ := by
  have aux (Φ Ψ : Set V) (hΦ : IsRootSet Φ) (hΨ : IsRootSet Ψ)
      (he : rootLines Φ = rootLines Ψ) : lineAngles Φ ⊆ lineAngles Ψ := by
    rintro θ ⟨r, hr, s, hs, hl, ha⟩
    have hrl : (ℝ ∙ r) ∈ rootLines Ψ := he ▸ ⟨r, hr, rfl⟩
    have hsl : (ℝ ∙ s) ∈ rootLines Ψ := he ▸ ⟨s, hs, rfl⟩
    obtain ⟨r', hr', hlr⟩ := hrl
    obtain ⟨s', hs', hls⟩ := hsl
    change ℝ ∙ r' = ℝ ∙ r at hlr
    change ℝ ∙ s' = ℝ ∙ s at hls
    refine ⟨r', hr', s', hs', ?_, ?_⟩
    · intro hm
      have hle : ℝ ∙ s' ≤ ℝ ∙ r' := (span_singleton_le_iff_mem _ _).mpr hm
      rw [hlr, hls] at hle
      exact hl (hle (mem_span_singleton_self s))
    · exact (lineAngle_eq_of_same_lines (hΦ.ne_zero hr) (hΦ.ne_zero hs)
        (hΨ.ne_zero hr') (hΨ.ne_zero hs') hlr hls).trans ha
  exact Set.Subset.antisymm (aux Φ Ψ hΦ hΨ he) (aux Ψ Φ hΨ hΦ he.symm)

/-- Step `rCallowedBF`: two squared lengths in ratio two allow only 90, 60, and 45 degrees. -/
theorem lineAngles_subset_of_lengths_two (hΦ : IsRootSet Φ) {b : ℝ} (hb : 0 < b)
    (hL : ∀ r ∈ Φ, ⟪r, r⟫ = b ∨ ⟪r, r⟫ = 2 * b) :
    lineAngles Φ ⊆ {Real.pi / 2, Real.pi / 3, Real.pi / 4} := by
  rintro θ ⟨r, hr, s, hs, hl, rfl⟩
  by_cases ho : ⟪r, s⟫ = 0
  · exact Or.inl (lineAngle_eq_pi_div_two ho)
  rcases hΦ.squared_angle_length_cases hr hs ho hl with ⟨_, ha⟩ | ⟨_, ha⟩ | ⟨h, _⟩
  · exact Or.inr (Or.inl (lineAngle_eq_pi_div_three (hΦ.ne_zero hr) (hΦ.ne_zero hs) ha))
  · exact Or.inr (Or.inr (lineAngle_eq_pi_div_four (hΦ.ne_zero hr) (hΦ.ne_zero hs) ha))
  · rcases hL r hr with hr | hr <;> rcases hL s hs with hs | hs <;>
      rcases h with h | h <;> linarith

/-- Step `rCallowedG`: two squared lengths in ratio three allow only 90, 60, and 30 degrees. -/
theorem lineAngles_subset_of_lengths_three (hΦ : IsRootSet Φ) {b : ℝ} (hb : 0 < b)
    (hL : ∀ r ∈ Φ, ⟪r, r⟫ = b ∨ ⟪r, r⟫ = 3 * b) :
    lineAngles Φ ⊆ {Real.pi / 2, Real.pi / 3, Real.pi / 6} := by
  rintro θ ⟨r, hr, s, hs, hl, rfl⟩
  by_cases ho : ⟪r, s⟫ = 0
  · exact Or.inl (lineAngle_eq_pi_div_two ho)
  rcases hΦ.squared_angle_length_cases hr hs ho hl with ⟨_, ha⟩ | ⟨h, _⟩ | ⟨_, ha⟩
  · exact Or.inr (Or.inl (lineAngle_eq_pi_div_three (hΦ.ne_zero hr) (hΦ.ne_zero hs) ha))
  · rcases hL r hr with hr | hr <;> rcases hL s hs with hs | hs <;>
      rcases h with h | h <;> linarith
  · exact Or.inr (Or.inr (lineAngle_eq_pi_div_six (hΦ.ne_zero hr) (hΦ.ne_zero hs) ha))

end IsRootSet
