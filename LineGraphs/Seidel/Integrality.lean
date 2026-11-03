/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Apex
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Clearing the Gram determinant

Lemma `lem:414-dual` of Remark 4.14 of [CGSS].
-/

open scoped RealInnerProductSpace
open Matrix

namespace InnerProductSpace

-- Lemma (integrality), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-dual`, Remark 4.14: if a basis has integral Gram matrix and a vector
pairs integrally with the basis, the Gram determinant times its squared norm is integral.
The adjugate clears the denominator of its coordinates. -/
theorem det_gram_mul_inner_self_mem_int {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : Module.Basis ι ℝ E) (w : E)
    (hb : ∀ i j, ⟪b i, b j⟫ ∈ Set.range (Int.cast : ℤ → ℝ))
    (hw : ∀ i, ⟪w, b i⟫ ∈ Set.range (Int.cast : ℤ → ℝ)) :
    (Matrix.gram ℝ b).det * ⟪w, w⟫ ∈ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  choose B₀ hB using hb
  choose a ha using hw
  let B : Matrix ι ι ℤ := fun i j ↦ B₀ i j
  let β : ι → ℝ := fun i ↦ b.repr w i
  have hcast : Matrix.map B (Int.castRingHom ℝ) = Matrix.gram ℝ b := by
    ext i j
    exact hB i j
  have hcoord : (Matrix.gram ℝ b) *ᵥ β = fun i ↦ (a i : ℝ) := by
    funext i
    rw [ha i, real_inner_comm, ← b.sum_repr w]
    simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply, inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    simp only [β, mul_comm]
  have hclear : ∀ i, (Matrix.gram ℝ b).det * β i =
      (Matrix.adjugate B *ᵥ a) i := by
    intro i
    have h := congrArg (fun v : ι → ℝ ↦ v i)
      (congrArg (fun v : ι → ℝ ↦ (Matrix.gram ℝ b).adjugate *ᵥ v) hcoord)
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec] at h
    change (Matrix.gram ℝ b).det * β i = _ at h
    have hadj : (Matrix.gram ℝ b).adjugate =
        Matrix.map (Matrix.adjugate B) (Int.castRingHom ℝ) := by
      rw [← hcast]
      exact ((Int.castRingHom ℝ).map_adjugate B).symm
    rw [hadj] at h
    exact h.trans ((Int.castRingHom ℝ).map_mulVec (Matrix.adjugate B) a i).symm
  have hnorm : ⟪w, w⟫ = ∑ i, β i * (a i : ℝ) := by
    conv_lhs => rhs; rw [← b.sum_repr w]
    simp only [inner_sum, inner_smul_right, ← ha, β]
  refine ⟨∑ i, (Matrix.adjugate B *ᵥ a) i * a i, ?_⟩
  rw [hnorm, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [← hclear i]
  ring

end InnerProductSpace
