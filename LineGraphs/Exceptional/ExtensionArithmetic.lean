/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.ExtensionGeometry

/-! # The integer formulas in the extension test

Clearing the positive denominator in `lem:extension` (Lemma 3.4) of [Exc].
-/

open Matrix
open scoped RealInnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Lemma 3.4 [Exc]
/-- The inverse bilinear form as an exact adjugate quotient, used in
`lem:extension` (Lemma 3.4) of [Exc]. This identity also holds for singular matrices,
using the zero-valued inverse conventions. -/
theorem intCast_inv_bilinear (G : Matrix ι ι ℤ) (s t : ι → ℤ) :
    (fun i => (s i : ℝ)) ⬝ᵥ ((G.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ fun i => (t i : ℝ)) =
      (s ⬝ᵥ (G.adjugate *ᵥ t) : ℤ) / (G.det : ℝ) := by
  have hadj : (G.map (Int.cast : ℤ → ℝ)).adjugate =
      G.adjugate.map (Int.cast : ℤ → ℝ) := ((Int.castRingHom ℝ).map_adjugate G).symm
  rw [inv_def, Ring.inverse_eq_inv, hadj, ← Int.cast_det, smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  simp [dotProduct, mulVec, map_apply, Int.cast_sum, Int.cast_mul]

variable {V E : Type*} [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Matrix V V ℤ} {B : Finset V} {x : V → E}

-- Lemma 3.4 [Exc]
/-- The numerator of the inner product with an old vertex, in `lem:extension`
(Lemma 3.4) of [Exc]. -/
theorem dotProduct_adjugate_column (M : Matrix V V ℤ) (B : Finset V) (s : B → ℤ) (u : V) :
    s ⬝ᵥ ((M.certificateMatrix B).adjugate *ᵥ fun b => M b u) =
      (s ᵥ* M.certificateCoordinates B) u := by
  rw [dotProduct_mulVec, certificateCoordinates, ← vecMul_vecMul]
  rfl

-- Lemma 3.4 [Exc]
/-- The formula `sᵀ C(·,u)/D` in `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem IsGramCertificate.gramProjection_inner (hB : M.IsGramCertificate B)
    (hM : M.IsSymm) (hx : gram ℝ x = M.map (Int.cast : ℤ → ℝ)) (s : B → ℤ) (u : V) :
    ⟪gramProjection (fun b : B => x b) (fun b => (s b : ℝ)), x u⟫ =
      ((s ᵥ* M.certificateCoordinates B) u : ℝ) / (M.certificateDet B : ℝ) := by
  have hg : gram ℝ (fun b : B => x b) = (M.certificateMatrix B).map (Int.cast : ℤ → ℝ) := by
    ext b c
    exact congrFun (congrFun hx b) c
  have hp : (gram ℝ (fun b : B => x b)).PosDef := hg ▸ hB.posDef hM
  rw [Matrix.gramProjection_inner _ hp]
  have hi : (fun b : B => ⟪x b, x u⟫) = fun b : B => (M b u : ℝ) := by
    funext b
    exact congrFun (congrFun hx b) u
  rw [hi, hg, intCast_inv_bilinear, dotProduct_adjugate_column]
  rfl

-- Lemma 3.4 [Exc]
/-- The formula `sᵀ adj(G) s/D` in `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem IsGramCertificate.gramProjection_inner_self (hB : M.IsGramCertificate B)
    (hM : M.IsSymm) (hx : gram ℝ x = M.map (Int.cast : ℤ → ℝ)) (s : B → ℤ) :
    let p := gramProjection (fun b : B => x b) (fun b => (s b : ℝ))
    ⟪p, p⟫ = (s ⬝ᵥ ((M.certificateMatrix B).adjugate *ᵥ s) : ℤ) /
      (M.certificateDet B : ℝ) := by
  have hg : gram ℝ (fun b : B => x b) = (M.certificateMatrix B).map (Int.cast : ℤ → ℝ) := by
    ext b c
    exact congrFun (congrFun hx b) c
  have hp : (gram ℝ (fun b : B => x b)).PosDef := hg ▸ hB.posDef hM
  dsimp only
  rw [Matrix.gramProjection_inner_self _ hp, hg, intCast_inv_bilinear]
  rfl

end Matrix
