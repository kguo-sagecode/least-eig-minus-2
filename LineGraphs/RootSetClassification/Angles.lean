/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.AnglePairings
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Acute line angles and length ratios

The angle convention `facts:rem-angles` and steps `rangoneangle`--`rangthreeangle`
of `lem:angles` in Remark 3.11 of [CGSS]. Angles are in radians, with the
absolute inner product making the convention independent of signs.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- The acute line-angle convention `facts:rem-angles` of Remark 3.11. -/
noncomputable def lineAngle (r s : V) : ℝ := Real.arccos (|⟪r, s⟫| / (‖r‖ * ‖s‖))

/-- The cosine identification in `facts:rem-angles`, using a squared inner-product equation. -/
theorem lineAngle_eq_of_inner_sq {r s : V} (hr : r ≠ 0) (hs : s ≠ 0) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (hc : 0 ≤ Real.cos θ)
    (he : ⟪r, s⟫ ^ 2 = (Real.cos θ) ^ 2 * ⟪r, r⟫ * ⟪s, s⟫) :
    lineAngle r s = θ := by
  apply Real.arccos_eq_of_eq_cos hθ₀ hθπ
  apply (div_eq_iff (mul_ne_zero (norm_ne_zero_iff.mpr hr) (norm_ne_zero_iff.mpr hs))).mpr
  apply (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg hc (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mp
  calc
    |⟪r, s⟫| ^ 2 = ⟪r, s⟫ ^ 2 := sq_abs _
    _ = (Real.cos θ) ^ 2 * ⟪r, r⟫ * ⟪s, s⟫ := he
    _ = (Real.cos θ * (‖r‖ * ‖s‖)) ^ 2 := by
      rw [mul_pow, mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      ring

/-- Step `rangoneangle`: squared cosine one quarter means sixty degrees. -/
theorem lineAngle_eq_pi_div_three {r s : V} (hr : r ≠ 0) (hs : s ≠ 0)
    (he : 4 * ⟪r, s⟫ ^ 2 = ⟪r, r⟫ * ⟪s, s⟫) : lineAngle r s = Real.pi / 3 := by
  apply lineAngle_eq_of_inner_sq hr hs (by positivity) (by linarith [Real.pi_pos])
  · rw [Real.cos_pi_div_three]
    norm_num
  · rw [Real.cos_pi_div_three]
    nlinarith

/-- Step `rangtwoangle`: squared cosine one half means forty-five degrees. -/
theorem lineAngle_eq_pi_div_four {r s : V} (hr : r ≠ 0) (hs : s ≠ 0)
    (he : 4 * ⟪r, s⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪s, s⟫) : lineAngle r s = Real.pi / 4 := by
  apply lineAngle_eq_of_inner_sq hr hs (by positivity) (by linarith [Real.pi_pos])
  · rw [Real.cos_pi_div_four]
    positivity
  · rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith

/-- Step `rangthreeangle`: squared cosine three quarters means thirty degrees. -/
theorem lineAngle_eq_pi_div_six {r s : V} (hr : r ≠ 0) (hs : s ≠ 0)
    (he : 4 * ⟪r, s⟫ ^ 2 = 3 * ⟪r, r⟫ * ⟪s, s⟫) : lineAngle r s = Real.pi / 6 := by
  apply lineAngle_eq_of_inner_sq hr hs (by positivity) (by linarith [Real.pi_pos])
  · rw [Real.cos_pi_div_six]
    positivity
  · rw [Real.cos_pi_div_six, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith

/-- The perpendicular case adjoined in step `rCallowed` of Remark 3.11. -/
theorem lineAngle_eq_pi_div_two {r s : V} (he : ⟪r, s⟫ = 0) :
    lineAngle r s = Real.pi / 2 := by
  simp [lineAngle, he, Real.arccos_zero]

/-- The positive square-root step concluding `rangcases` of Remark 3.11. -/
theorem norm_ratio_eq_sqrt {r s : V} (hr : r ≠ 0) (hs : s ≠ 0) {k : ℝ} (hk : 1 ≤ k)
    (he : ⟪r, r⟫ = k * ⟪s, s⟫ ∨ ⟪s, s⟫ = k * ⟪r, r⟫) :
    max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = Real.sqrt k := by
  have hk₀ : 0 ≤ k := le_trans (by norm_num) hk
  have hk₁ : 1 ≤ Real.sqrt k := by
    nlinarith [Real.sq_sqrt hk₀, Real.sqrt_nonneg k]
  have aux (x y : V) (hy : y ≠ 0) (hxy : ⟪x, x⟫ = k * ⟪y, y⟫) :
      max ‖x‖ ‖y‖ / min ‖x‖ ‖y‖ = Real.sqrt k := by
    have hn : ‖x‖ = Real.sqrt k * ‖y‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg k) (norm_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt hk₀, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, hxy]
    have hle : ‖y‖ ≤ ‖x‖ := by rw [hn]; nlinarith [norm_nonneg y]
    rw [max_eq_left hle, min_eq_right hle, hn]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hy)
  rcases he with he | he
  · exact aux r s hs he
  · simpa only [max_comm, min_comm] using aux s r hr he

-- Remark 3.11, lem:angles
/-- The length-ratio/angle assertion of `lem:angles` in Remark 3.11: a
nonorthogonal pair of distinct root lines has precisely one of the three
possibilities `(1, π/3)`, `(√2, π/4)`, or `(√3, π/6)`. -/
theorem angle_length_cases (hΦ : IsRootSet Φ) {r s : V} (hr : r ∈ Φ) (hs : s ∈ Φ)
    (ho : ⟪r, s⟫ ≠ 0) (hl : s ∉ ℝ ∙ r) :
    (max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = 1 ∧ lineAngle r s = Real.pi / 3) ∨
    (max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = Real.sqrt 2 ∧ lineAngle r s = Real.pi / 4) ∨
    (max ‖r‖ ‖s‖ / min ‖r‖ ‖s‖ = Real.sqrt 3 ∧ lineAngle r s = Real.pi / 6) := by
  have hr₀ := hΦ.ne_zero hr
  have hs₀ := hΦ.ne_zero hs
  rcases hΦ.squared_angle_length_cases hr hs ho hl with ⟨hl, ha⟩ | ⟨hl, ha⟩ | ⟨hl, ha⟩
  · left
    refine ⟨?_, lineAngle_eq_pi_div_three hr₀ hs₀ ha⟩
    simpa using norm_ratio_eq_sqrt hr₀ hs₀ (le_refl (1 : ℝ)) (Or.inl (by simpa using hl))
  · exact Or.inr (Or.inl ⟨norm_ratio_eq_sqrt hr₀ hs₀ (by norm_num) hl,
      lineAngle_eq_pi_div_four hr₀ hs₀ ha⟩)
  · exact Or.inr (Or.inr ⟨norm_ratio_eq_sqrt hr₀ hs₀ (by norm_num) hl,
      lineAngle_eq_pi_div_six hr₀ hs₀ ha⟩)

end IsRootSet
