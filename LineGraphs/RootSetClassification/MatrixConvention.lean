/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LineFrame
import Mathlib.Data.Matrix.Mul

/-!
# The normalized matrix convention

`lem:C-convention` of the blueprint for Remark 3.11 of [CGSS]. The
coordinate-free frame operator is `UUᵀ` in any orthonormal basis, while
`lineGram` is `UᵀU`. Spanning permits cancellation by testing inner products.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {I : Type*} [Fintype I] [DecidableEq I]

/-- The Gram matrix of chosen unit columns in `eq:C-convention`. -/
noncomputable def lineGram (u : I → V) : Matrix I I ℝ := fun i j ↦ ⟪u i, u j⟫

/-- The normalized line matrix `C = 2G - 2I` of `eq:C-convention`, Remark 3.11. -/
noncomputable def signedAdj (u : I → V) : Matrix I I ℝ :=
  (2 : ℝ) • lineGram u - (2 : ℝ) • 1

omit [DecidableEq I] in
/-- Step `rCfactor`, evaluated as a bilinear form. -/
theorem lineGram_sq_apply (u : I → V) (i j : I) :
    (lineGram u * lineGram u) i j = ⟪u i, lineFrame u (u j)⟫ := by
  simp only [Matrix.mul_apply, lineGram, lineFrame, LinearMap.sum_apply, inner_sum,
    lineProjector_apply, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq I] in
/-- Steps `rCforward`, `rCreverse`: spanning cancels the two column maps. -/
theorem lineGram_sq_eq_iff_frame (u : I → V) (hs : span ℝ (Set.range u) = ⊤) (t : ℝ) :
    lineGram u * lineGram u = t • lineGram u ↔ lineFrame u = t • LinearMap.id := by
  constructor
  · intro he
    have hcol (j : I) : lineFrame u (u j) = t • u j := by
      apply ext_inner_left ℝ
      intro x
      have hx : x ∈ span ℝ (Set.range u) := hs ▸ mem_top
      induction hx using span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have hij := congrFun (congrFun he i) j
        rw [lineGram_sq_apply] at hij
        simpa only [Matrix.smul_apply, smul_eq_mul, lineGram, real_inner_smul_right] using hij
      | zero => simp
      | add x y _ _ hx hy => simp only [inner_add_left, hx, hy]
      | smul a x _ hx => simp only [real_inner_smul_left, hx]
    ext x
    change lineFrame u x = t • x
    have hx : x ∈ span ℝ (Set.range u) := hs ▸ mem_top
    induction hx using span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hcol i
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
    | smul a x _ hx => simp only [map_smul, hx, smul_smul, mul_comm]
  · intro he
    ext i j
    rw [lineGram_sq_apply, he]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right,
      Matrix.smul_apply, smul_eq_mul, lineGram]

/-- Step `rCexpand`: expansion of the normalized quadratic polynomial. -/
theorem signedAdj_polynomial (u : I → V) (θ : ℝ) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - θ • 1) =
      (4 : ℝ) • (lineGram u * lineGram u - ((θ + 2) / 2) • lineGram u) := by
  simp only [signedAdj, sub_add_cancel, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one,
    smul_sub, smul_smul]
  module

/-- The polynomial vanishes exactly when the Gram square is scalar (`rCexpand`). -/
theorem signedAdj_quadratic_iff_gram (u : I → V) (θ : ℝ) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - θ • 1) = 0 ↔
      lineGram u * lineGram u = ((θ + 2) / 2) • lineGram u := by
  rw [signedAdj_polynomial, smul_eq_zero]
  norm_num only [OfNat.ofNat_ne_zero, false_or, sub_eq_zero]

omit [DecidableEq I] in
/-- Step `rCunittrace`: a unit column contributes one to the trace. -/
theorem trace_lineFrame [FiniteDimensional ℝ V] (u : I → V) (hu : ∀ i, ‖u i‖ = 1) :
    LinearMap.trace ℝ V (lineFrame u) = Fintype.card I := by
  simp only [lineFrame, map_sum, trace_lineProjector, real_inner_self_eq_norm_sq, hu,
    one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

-- Remark 3.11, lem:C-convention
/-- The normalized matrix convention of Remark 3.11: the quadratic identity
is equivalent to the tight frame and its uniquely determined second constant. -/
theorem signedAdj_quadratic_iff_frame [FiniteDimensional ℝ V] (u : I → V)
    (hu : ∀ i, ‖u i‖ = 1) (hs : span ℝ (Set.range u) = ⊤)
    (hn : 0 < Module.finrank ℝ V) (θ : ℝ) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - θ • 1) = 0 ↔
      lineFrame u = ((Fintype.card I : ℝ) / Module.finrank ℝ V) • LinearMap.id ∧
        θ = 2 * (Fintype.card I : ℝ) / Module.finrank ℝ V - 2 := by
  rw [signedAdj_quadratic_iff_gram, lineGram_sq_eq_iff_frame u hs]
  have hn₀ : (Module.finrank ℝ V : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  constructor
  · intro he
    have ht := congrArg (LinearMap.trace ℝ V) he
    rw [trace_lineFrame u hu, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
    have hv : (θ + 2) / 2 = (Fintype.card I : ℝ) / Module.finrank ℝ V :=
      (eq_div_iff hn₀).mpr ht.symm
    refine ⟨by simpa only [hv] using he, ?_⟩
    rw [mul_div_assoc]
    linarith
  · rintro ⟨hf, rfl⟩
    convert hf using 1
    congr 1
    ring

omit [DecidableEq I] in
/-- Step `rCsignframe`: changing any column signs preserves the frame. -/
theorem lineFrame_signs (u : I → V) (ε : I → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    lineFrame (fun i ↦ ε i • u i) = lineFrame u := by
  apply Finset.sum_congr rfl
  intro i _
  ext x
  simp only [lineProjector_apply, real_inner_smul_left, smul_smul]
  congr 1
  calc
    ε i * ⟪u i, x⟫ * ε i = ε i ^ 2 * ⟪u i, x⟫ := by ring
    _ = ⟪u i, x⟫ := by rw [hε, one_mul]

/-- Step `rCsignGram`: changing signs conjugates the Gram matrix diagonally. -/
theorem lineGram_signs (u : I → V) (ε : I → ℝ) :
    lineGram (fun i ↦ ε i • u i) = Matrix.diagonal ε * lineGram u * Matrix.diagonal ε := by
  ext i j
  simp only [lineGram, real_inner_smul_left, real_inner_smul_right, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  ring

/-- Steps `rCsignsquare`, `rCsigns`: sign changes diagonally conjugate `C`. -/
theorem signedAdj_signs (u : I → V) (ε : I → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    signedAdj (fun i ↦ ε i • u i) =
      Matrix.diagonal ε * signedAdj u * Matrix.diagonal ε := by
  ext i j
  simp only [signedAdj, lineGram, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul, Matrix.mul_diagonal, real_inner_smul_left, real_inner_smul_right,
    Matrix.one_apply]
  split_ifs with hij
  · subst j
    nlinarith [hε i]
  · ring

end IsRootSet
