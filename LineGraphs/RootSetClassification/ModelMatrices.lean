/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.MatrixConvention
import LineGraphs.RootSetClassification.ClassicalLines
import LineGraphs.RootSetClassification.LengthSpectrum

/-!
# The quadratic equations for model line matrices

Steps `rCframes`--`rCeqG` of blueprint Theorem C and `cor:rem-constants` of
Remark 3.11 of [CGSS]. Every matrix uses arbitrary unit representatives
and the convention `C = 2G - 2I`. The E₈ constant is 28.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Φ : Set V} {I : Type*} [Fintype I] [DecidableEq I]

/-- Steps `rCframes`, `reqframe`: every indecomposable root set gives the normalized
quadratic equation, with the number of oriented roots supplying twice the line count. -/
theorem signedAdj_quadratic (hΦ : IsRootSet Φ) (hI : hΦ.IsIndecomposable)
    {r u : I → V} (hr : RootRepresentatives Φ r) (hu : ∀ i, ‖u i‖ = 1)
    (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) *
      (signedAdj u - ((Φ.ncard : ℝ) / Module.finrank ℝ V - 2) • 1) = 0 := by
  let := hΦ.finiteDimensional
  let := hΦ.finite_root_index
  let := Fintype.ofFinite Φ
  obtain ⟨hn, hf⟩ := hΦ.frame_identity hI hr hu hl
  apply (signedAdj_quadratic_iff_frame u hu (hr.span_unit hΦ hl) hn _).mpr
  refine ⟨hf, ?_⟩
  rw [← Set.fintypeCard_eq_ncard, hr.card hΦ, Nat.cast_mul, Nat.cast_ofNat]

end IsRootSet

namespace RootSetModel

open IsRootSet CartanMatrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The second quadratic constant in blueprint Theorem C and `cor:rem-constants` of Remark 3.11. -/
def matrixConstant {n : ℕ} : FiniteType n → ℝ
  | .a n _ => n - 1
  | .b n _ | .c n _ => 2 * (n - 1)
  | .d n _ => 2 * (n - 2)
  | .e₆ => 10
  | .e₇ => 16
  | .e₈ => 28
  | .f₄ => 10
  | .g₂ => 4

/-- Steps `rCeqBC`--`rCeqG`, `reqA`--`reqE8`: substitute the exact root counts. -/
theorem matrixConstant_eq {n : ℕ} (t : FiniteType n) :
    matrixConstant t = (rootCount t : ℝ) / n - 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt t.rank_pos)
  cases t with
  | a n ha =>
    simp only [matrixConstant, rootCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  | b n ha | c n ha =>
    simp only [matrixConstant, rootCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    field_simp
  | d n ha =>
    simp only [matrixConstant, rootCount, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring
  | e₆ | e₇ | e₈ | f₄ | g₂ => norm_num [matrixConstant, rootCount]

/-- Steps `rCframes`, `rCeqBC`--`rCeqG` and `reqframe`--`reqE8` of Remark 3.11: the model
matrix equation, valid for every canonical model and all representative signs. -/
theorem signedAdj_quadratic_model {n : ℕ} (t : FiniteType n)
    {r u : I → Space t} (hr : RootRepresentatives (roots t) r) (hu : ∀ i, ‖u i‖ = 1)
    (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - matrixConstant t • 1) = 0 := by
  rw [matrixConstant_eq]
  simpa only [root_counts, finrank_space] using
    (isRootSet t).signedAdj_quadratic (isIndecomposable t) hr hu hl

-- Remark 3.11, thm:C
/-- Step `rCeqBC`: the Bₙ line matrix has second constant `2(n - 1)`. -/
theorem signedAdj_quadratic_Bn {n : ℕ} (hn : 2 ≤ n)
    {r u : I → EuclideanSpace ℝ (Fin n)} (hr : RootRepresentatives (Bn n) r)
    (hu : ∀ i, ‖u i‖ = 1) (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (2 * ((n : ℝ) - 1)) • 1) = 0 :=
  signedAdj_quadratic_model (.b n hn) hr hu hl

-- Remark 3.11, thm:C
/-- Step `rCeqBC`: the Cₙ line equation, including the rank-two construction case. -/
theorem signedAdj_quadratic_Cn {n : ℕ} (hn : 2 ≤ n)
    {r u : I → EuclideanSpace ℝ (Fin n)} (hr : RootRepresentatives (Cn n) r)
    (hu : ∀ i, ‖u i‖ = 1) (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (2 * ((n : ℝ) - 1)) • 1) = 0 := by
  have h := (Cn_isRootSet n).signedAdj_quadratic (Cn_isIndecomposable hn) hr hu hl
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : ((Cn n).ncard : ℝ) / Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 2 =
      2 * ((n : ℝ) - 1) := by
    simp only [Cn_ncard, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
    field_simp
  rwa [he] at h

-- Remark 3.11, thm:C
/-- Step `rCeqF`: the F₄ line matrix has second constant 10. -/
theorem signedAdj_quadratic_F₄ {r u : I → EuclideanSpace ℝ (Fin 4)}
    (hr : RootRepresentatives F₄ r) (hu : ∀ i, ‖u i‖ = 1)
    (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (10 : ℝ) • 1) = 0 :=
  signedAdj_quadratic_model .f₄ hr hu hl

-- Remark 3.11, thm:C
/-- Step `rCeqG`: the G₂ line matrix has second constant 4. -/
theorem signedAdj_quadratic_G₂ {r u : I → g₂Space}
    (hr : RootRepresentatives G₂ r) (hu : ∀ i, ‖u i‖ = 1)
    (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - (4 : ℝ) • 1) = 0 :=
  signedAdj_quadratic_model .g₂ hr hu hl

-- Remark 3.11, cor:rem-constants
/-- The equal-length equations of Remark 3.11, with constants `n - 1`, `2(n - 2)`,
10, 16, and 28 for A, D, E₆, E₇, and E₈ respectively. The hypothesis `IsSimplyLaced t`
selects the equal-length cases of blueprint `cor:rem-constants`; the proof uses the
more general `signedAdj_quadratic_model`, valid for every model. -/
theorem signedAdj_quadratic_simplyLaced {n : ℕ} (t : FiniteType n)
    (_ht : IsSimplyLaced t) {r u : I → Space t} (hr : RootRepresentatives (roots t) r)
    (hu : ∀ i, ‖u i‖ = 1) (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    (signedAdj u + (2 : ℝ) • 1) * (signedAdj u - matrixConstant t • 1) = 0 :=
  signedAdj_quadratic_model t hr hu hl

end RootSetModel
