/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.E6NotSumSquares

/-! # Integral coordinates in the D root lattice

The integral-coordinate step of Proposition `prop:types` (Proposition 2.6) of [Exc].
-/

open Submodule
open scoped RealInnerProductSpace

namespace LineSystem

-- Proposition 2.6 [Exc]
/-- The coordinate map used in Proposition `prop:types` (Proposition 2.6) of
[Exc] commutes with integral scalar multiplication. -/
theorem integerVector_int_smul {n : ℕ} (c : ℝ) (a : ℤ) (v : Fin n → ℤ) :
    integerVector c (a • v) = a • integerVector c v := by
  ext i
  simp [integerVector, mul_left_comm]

-- Proposition 2.6 [Exc]
/-- Proposition `prop:types` (Proposition 2.6) of [Exc]: the whole integral
span of the coordinate `D` roots has integral coordinates. -/
theorem Dn.exists_integerVector_of_mem_span {n : ℕ} {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ span ℤ (Dn n).Φ) : ∃ v : Fin n → ℤ, integerVector 1 v = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    exact ⟨dnRoot p, rfl⟩
  | zero => exact ⟨0, by ext i; simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨v, rfl⟩ := hz
    obtain ⟨u, rfl⟩ := hw
    exact ⟨v + u, integerVector_add 1 v u⟩
  | smul a z _ hz =>
    obtain ⟨v, rfl⟩ := hz
    exact ⟨a • v, integerVector_int_smul 1 a v⟩

-- Proposition 2.6 [Exc]
/-- The obstruction in Proposition `prop:types` (Proposition 2.6) of [Exc]:
the simple-root Gram matrix of `E₆` cannot occur in the integral span of `D` roots. -/
theorem E₆.not_exists_gram_in_span_Dn (n : ℕ) :
    ¬ ∃ z : Fin 6 → span ℤ (Dn n).Φ,
      Matrix.gram ℝ (fun i ↦ (z i : EuclideanSpace ℝ (Fin n))) =
        Matrix.gram ℝ E₆.simpleRoot := by
  rintro ⟨z, hz⟩
  choose y hy using fun i ↦ Dn.exists_integerVector_of_mem_span (z i).property
  apply E₆.not_exists_integral_gram_simpleRoot n
  refine ⟨y, fun i j ↦ ?_⟩
  calc
    (integerInner (y i) (y j) : ℝ) = ⟪integerVector 1 (y i), integerVector 1 (y j)⟫ := by
      rw [inner_integerVector]
      ring
    _ = ⟪(z i : EuclideanSpace ℝ (Fin n)), (z j : EuclideanSpace ℝ (Fin n))⟫ := by
      rw [hy, hy]
    _ = _ := congrFun (congrFun hz i) j

end LineSystem
