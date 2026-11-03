/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Angles
import LineGraphs.RootSetClassification.Coordinates

/-!
# Three lines at forty-five degrees

`lem:rem-three-lines` of the blueprint for Remark 3.11 of [CGSS]. The
displayed three unit vectors have constant off-diagonal inner product
`1 / √2`. Their three squared-cosine equations contradict crystallography.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- The strict squared-cosine test for distinct lines in `facts:rem-angles`. -/
theorem not_mem_line_of_inner_sq_lt {r s : V}
    (he : ⟪r, s⟫ ^ 2 < ⟪r, r⟫ * ⟪s, s⟫) : s ∉ ℝ ∙ r := by
  rintro hs
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hs
  simp only [real_inner_smul_left, real_inner_smul_right] at he
  nlinarith

/-- Step `rtlpairs`: the forty-five-degree equation forces squared-length ratio two. -/
theorem squared_length_ratio_two (hΦ : IsRootSet Φ) {r s : V} (hr : r ∈ Φ) (hs : s ∈ Φ)
    (he : 4 * ⟪r, s⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪s, s⟫) :
    ⟪r, r⟫ = 2 * ⟪s, s⟫ ∨ ⟪s, s⟫ = 2 * ⟪r, r⟫ := by
  have hp := mul_pos (real_inner_self_pos.mpr (hΦ.ne_zero hr))
    (real_inner_self_pos.mpr (hΦ.ne_zero hs))
  have ho : ⟪r, s⟫ ≠ 0 := by intro hz; rw [hz] at he; nlinarith
  have hl : s ∉ ℝ ∙ r := not_mem_line_of_inner_sq_lt (by nlinarith)
  rcases hΦ.squared_angle_length_cases hr hs ho hl with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · nlinarith
  · exact h
  · nlinarith

-- Remark 3.11, lem:rem-three-lines
/-- Steps `rtlimpossible`--`rtlgamma`: no root system in any ambient dimension
contains three roots satisfying the pairwise forty-five-degree equations. -/
theorem not_contains_three_equiangular_lines (hΦ : IsRootSet Φ) {r s t : V}
    (hr : r ∈ Φ) (hs : s ∈ Φ) (ht : t ∈ Φ)
    (hrs : 4 * ⟪r, s⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪s, s⟫)
    (hrt : 4 * ⟪r, t⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪t, t⟫)
    (hst : 4 * ⟪s, t⟫ ^ 2 = 2 * ⟪s, s⟫ * ⟪t, t⟫) : False := by
  have hp := real_inner_self_pos.mpr (hΦ.ne_zero hr)
  rcases hΦ.squared_length_ratio_two hr hs hrs with h₁ | h₁ <;>
    rcases hΦ.squared_length_ratio_two hr ht hrt with h₂ | h₂ <;>
    rcases hΦ.squared_length_ratio_two hs ht hst with h₃ | h₃ <;> linarith

/-- The constant `c` in the explicit example of `lem:rem-three-lines`. -/
noncomputable def fortyFiveCos : ℝ := 1 / Real.sqrt 2

/-- Step `rtlradicand`: the three-vector construction has a positive radicand. -/
theorem fortyFiveCos_properties :
    fortyFiveCos ^ 2 = 1 / 2 ∧ 1 / 2 < fortyFiveCos ∧ fortyFiveCos < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have h₁ : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have h₂ : Real.sqrt 2 < (2 : ℝ) := by nlinarith
  unfold fortyFiveCos
  constructor
  · rw [div_pow, hs]
    norm_num
  constructor
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)).mpr
    linarith

/-- The three vectors displayed in `lem:rem-three-lines` of Remark 3.11. -/
noncomputable def fortyFiveTriple : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![WithLp.toLp 2 ![1, 0, 0],
    WithLp.toLp 2 ![fortyFiveCos, fortyFiveCos, 0],
    WithLp.toLp 2 ![fortyFiveCos, 1 - fortyFiveCos, Real.sqrt (2 * fortyFiveCos - 1)]]

/-- Steps `rtlnorm1`--`rtlip23`: the exact Gram matrix of the example. -/
theorem fortyFiveTriple_inner (i j : Fin 3) :
    ⟪fortyFiveTriple i, fortyFiveTriple j⟫ = if i = j then 1 else fortyFiveCos := by
  obtain ⟨hc, hc₀, _⟩ := fortyFiveCos_properties
  have hs := Real.sq_sqrt (show 0 ≤ 2 * fortyFiveCos - 1 by linarith)
  fin_cases i <;> fin_cases j <;>
    simp only [PiLp.inner_apply] <;>
    norm_num [fortyFiveTriple, Fin.sum_univ_succ] <;>
    nlinarith

/-- Step `rtlangle`: the example consists of three distinct unit lines pairwise at `π/4`. -/
theorem fortyFiveTriple_properties :
    (∀ i, ‖fortyFiveTriple i‖ = 1) ∧
      ∀ i j, i ≠ j → fortyFiveTriple j ∉ ℝ ∙ fortyFiveTriple i ∧
        lineAngle (fortyFiveTriple i) (fortyFiveTriple j) = Real.pi / 4 := by
  have hn (i : Fin 3) : ⟪fortyFiveTriple i, fortyFiveTriple i⟫ = 1 := by
    simp only [fortyFiveTriple_inner, ite_true]
  have hz (i : Fin 3) : fortyFiveTriple i ≠ 0 :=
    real_inner_self_pos.mp (by rw [hn]; norm_num)
  constructor
  · intro i
    have h := hn i
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (fortyFiveTriple i)]
  · intro i j hij
    have he : 4 * ⟪fortyFiveTriple i, fortyFiveTriple j⟫ ^ 2 =
        2 * ⟪fortyFiveTriple i, fortyFiveTriple i⟫ *
          ⟪fortyFiveTriple j, fortyFiveTriple j⟫ := by
      rw [fortyFiveTriple_inner, ite_eq_right_iff.mpr (fun h ↦ (hij h).elim), hn, hn,
        fortyFiveCos_properties.1]
      norm_num
    refine ⟨not_mem_line_of_inner_sq_lt ?_, lineAngle_eq_pi_div_four (hz i) (hz j) he⟩
    rw [hn, hn] at he ⊢
    nlinarith

end IsRootSet
