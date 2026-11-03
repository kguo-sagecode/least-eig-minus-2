/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Affine

/-!
# The affine D eigenvector

The vector is 2 on the original path and 1 on all four attached leaves.
The same computation includes the four-leaf star.
-/

namespace WeightedGraph

open Matrix

/-- The affine D vector is 2 at nonleaves and 1 at the four leaves. -/
def affineDEigenvector (ℓ : ℕ) : Fin (ℓ - 4 + 1) ⊕ Fin 4 → ℝ :=
  Sum.elim (fun _ => 2) (fun _ => 1)

/-- The affine D vector is positive and has eigenvalue 2, uniformly in the rank. -/
theorem affineD_eigenvector (ℓ : ℕ) :
    (∀ i, 0 < affineDEigenvector ℓ i) ∧
    (affineD ℓ).weights *ᵥ affineDEigenvector ℓ = (2 : ℝ) • affineDEigenvector ℓ := by
  constructor
  · rintro (i | i) <;> norm_num [affineDEigenvector]
  · funext i
    rcases i with i | j
    · rw [affineD, affineDEigenvector, attachLeaves_mulVec_inl, path_mulVec_const]
      simp only [Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Fin.sum_univ_four]
      norm_num only [Fin.val_zero, Fin.reduceFinMk, Fin.val_last, Fin.ext_iff]
      split_ifs <;> norm_num at * <;> contradiction
    · rw [affineD, affineDEigenvector, attachLeaves_mulVec_inr]
      norm_num

end WeightedGraph
