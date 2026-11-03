/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Frame
import LineGraphs.LineSystem.ModelSpans

/-!
# Computation C6 for the three models of E₈

The coordinate frame matrices `K = ∑ v vᵀ` over the raw integer roots, both signs (step
`s3c6exceptional` of `blueprint/sec3-rootsystems.tex`), checked by `decide +kernel` over the
structured root indices: `540I - 60J` for model (i) (tripled coordinates, `q = 9`), `240I` for
model (ii) (doubled coordinates, `q = 4`) and `120I` for model (iii) (`q = 2`). On the span,
each gives the frame operator `60 = 4N/ℓ = 4 · 120 / 8` times the identity.
-/

open scoped RealInnerProductSpace
open Finset Submodule

namespace Computations.C6

open LineSystem

-- Computation C6
/-- C6, step `s3c6one`: model (i), `K = 540I₉ - 60J₉`. -/
theorem e₈viaA₈_frame_matrix : ∀ k l : Fin 9,
    ∑ a : E₈viaA₈.Index, E₈viaA₈.root a k * E₈viaA₈.root a l =
      540 * (if k = l then 1 else 0) - 60 := by
  decide +kernel

-- Computation C6
/-- C6, step `s3c6two`: model (ii), `K = 240I₈`. -/
theorem e₈_frame_matrix : ∀ k l : Fin 8,
    ∑ a : E₈viaD₈.Index, E₈viaD₈.root a k * E₈viaD₈.root a l = 240 * (if k = l then 1 else 0) := by
  decide +kernel

-- Computation C6
/-- C6, step `s3c6three`: model (iii), `K = 120I₈`. -/
theorem e₈viaSteiner_frame_matrix : ∀ k l : Fin 8,
    ∑ a : E₈viaSteiner.Index, E₈viaSteiner.root a k * E₈viaSteiner.root a l =
      120 * (if k = l then 1 else 0) := by
  decide +kernel

end Computations.C6

namespace LineSystem

open Computations.C6

-- Lemma "the frame identity within the span", step s3frameEii
/-- C6 for model (ii): the frame operator is `60` times the identity. -/
theorem frameSum_E₈ (x : EuclideanSpace ℝ (Fin 8)) : E₈.frameSum x = (60 : ℝ) • x := by
  ext k
  rw [E₈viaD₈.integerModel.frameSum_apply]
  change 1 / 2 * (1 / 2) *
    ∑ j, ((∑ a : E₈viaD₈.Index, E₈viaD₈.root a k * E₈viaD₈.root a j : ℤ) : ℝ) * x j = _
  simp only [e₈_frame_matrix]
  push_cast
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, PiLp.smul_apply, smul_eq_mul]
  ring

-- Lemma "the frame identity within the span", step s3frameEii
/-- C6 for the default model of E₈ (model (ii)): `4N/ℓ = 60`. -/
theorem isFrame_E₈ : E₈.IsFrame 60 := fun x _ => frameSum_E₈ x

-- Lemma "the frame identity within the span", step s3frameEi
/-- C6 for model (i): on the span (coordinate sum zero) the frame operator is `60`. -/
theorem isFrame_E₈viaA₈ : E₈viaA₈.IsFrame 60 := by
  intro x hx
  have hs : ∑ j, x j = 0 := span_E₈viaA₈_le_ker_coordinateSum hx
  ext k
  rw [E₈viaA₈.integerModel.frameSum_apply]
  change 1 / 3 * (1 / 3) *
    ∑ j, ((∑ a : E₈viaA₈.Index, E₈viaA₈.root a k * E₈viaA₈.root a j : ℤ) : ℝ) * x j = _
  simp only [e₈viaA₈_frame_matrix]
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum, hs, PiLp.smul_apply,
    smul_eq_mul]
  ring

-- Lemma "the frame identity within the span", step s3frameEiii
/-- C6 for model (iii): the frame operator is `60` times the identity. -/
theorem isFrame_E₈viaSteiner : E₈viaSteiner.IsFrame 60 := by
  intro x _
  ext k
  rw [E₈viaSteiner.integerModel.frameSum_apply]
  change (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ *
    ∑ j, ((∑ a : E₈viaSteiner.Index, E₈viaSteiner.root a k * E₈viaSteiner.root a j : ℤ) : ℝ) *
      x j = _
  simp only [e₈viaSteiner_frame_matrix]
  push_cast
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, PiLp.smul_apply, smul_eq_mul]
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]
  rw [h]
  ring

end LineSystem
