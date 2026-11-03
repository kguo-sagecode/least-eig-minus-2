/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.OrthGraphParameters
import LineGraphs.Computations.C1
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! # The Gram-matrix bound in [CGSS, Lemma 2.10] -/

open scoped RealInnerProductSpace
open SimpleGraph

namespace LineSystem.Hyp24

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (H : Hyp24 V)

/-- Step 210entries of `lem:2.10` ([CGSS, Lemma 2.10]): the graph determines all
inner products, including the diagonal. -/
theorem inner_Γa_eq [DecidableEq H.Γa] (x y : H.Γa) :
    ⟪(x : V), y⟫ = if x = y then 2 else if H.orthGraph.Adj x y then 0 else 1 := by
  classical
  by_cases hxy : x = y
  · subst y
    simpa using H.S.inner_self x x.property.1
  by_cases ha : H.orthGraph.Adj x y
  · rw [ite_eq_right hxy, ite_eq_left ha]
    exact ha
  have h := H.inner_eq_zero_or_one x.property y.property
    (fun he ↦ hxy (Subtype.ext he))
  rw [ite_eq_right hxy, ite_eq_right ha]
  exact h.resolve_left ha

/-- The core family in step 210gram of `lem:2.10` ([CGSS, Lemma 2.10]), expressed
using the six-part coordinates; only its first five parts enter the Gram matrix. -/
noncomputable def gramCoreVector {u v : H.Γa} (huv : u ≠ v)
    (hnav : ¬H.orthGraph.Adj u v)
    (p : TriangleVertex (H.orthGraph.commonNeighbors u v) (H.orthGraphᶜ.commonNeighbors u v)) :
    V := H.orthGraph_hasTriangleProperty.triangleVertexEquiv huv hnav p

/-- Step 210blocks of `lem:2.10` ([CGSS, Lemma 2.10]): all entries of the core Gram
matrix follow from equality and the normal-form adjacency rules. -/
theorem inner_gramCoreVector [DecidableEq H.Γa] {u v : H.Γa} (huv : u ≠ v)
    (hnav : ¬H.orthGraph.Adj u v)
    (p q : TriangleVertex (H.orthGraph.commonNeighbors u v)
      (H.orthGraphᶜ.commonNeighbors u v)) :
    ⟪H.gramCoreVector huv hnav p, H.gramCoreVector huv hnav q⟫ =
      if p = q then 2 else if triangleRelation
        (fun (w : H.orthGraphᶜ.commonNeighbors u v) (x : H.orthGraph.commonNeighbors u v) ↦
          ¬H.orthGraph.Adj w x)
        (fun (w z : H.orthGraphᶜ.commonNeighbors u v) ↦ H.orthGraph.Adj w z) p q
        then 0 else 1 := by
  rw [gramCoreVector, gramCoreVector, H.inner_Γa_eq]
  simp only [(H.orthGraph_hasTriangleProperty.triangleVertexEquiv huv hnav).injective.eq_iff,
    H.orthGraph_hasTriangleProperty.triangleVertexEquiv_adj]

/-- The five block-sum vectors in step 210sums of `lem:2.10` ([CGSS, Lemma 2.10]),
ordered as `u,v,∑K,∑L,∑M`. -/
noncomputable def blockSumVectors {u v : H.Γa} (huv : u ≠ v)
    (hnav : ¬H.orthGraph.Adj u v) : Fin 5 → V :=
  ![H.gramCoreVector huv hnav .first, H.gramCoreVector huv hnav .second,
    ∑ x : H.orthGraph.commonNeighbors u v, H.gramCoreVector huv hnav (.common x),
    ∑ x : H.orthGraph.commonNeighbors u v, H.gramCoreVector huv hnav (.left x),
    ∑ x : H.orthGraph.commonNeighbors u v, H.gramCoreVector huv hnav (.right x)]

/-- Step 210sums of `lem:2.10` ([CGSS, Lemma 2.10]): bilinearity gives the corrected
five-by-five block-sum Gram matrix. -/
theorem gram_blockSumVectors {u v : H.Γa} (huv : u ≠ v) (hnav : ¬H.orthGraph.Adj u v) :
    Matrix.gram ℝ (H.blockSumVectors huv hnav) =
      Computations.C1.blockSumMatrix (Fintype.card (H.orthGraph.commonNeighbors u v) : ℝ) := by
  classical
  have h₂ (p : Prop) [Decidable p] :
      (if p then (2 : ℝ) else 1) = 1 + if p then 1 else 0 := by
    split_ifs <;> norm_num
  have h₀ (p : Prop) [Decidable p] :
      (if p then (0 : ℝ) else 1) = 1 - if p then 1 else 0 := by
    split_ifs <;> norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.gram_apply, blockSumVectors, Computations.C1.blockSumMatrix,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      sum_inner, inner_sum, inner_gramCoreVector] <;>
    dsimp +instances only [triangleRelation, decidableTriangleRelation] <;>
    simp only [TriangleVertex.common.injEq, TriangleVertex.left.injEq,
      TriangleVertex.right.injEq, reduceCtorEq, ↓reduceIte, ne_eq, ite_not, h₂, h₀,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_ofFinset, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, sub_sub_cancel] <;>
    ring

/-- Steps 210Dgram and 210Dpsd of `lem:2.10` ([CGSS, Lemma 2.10]): the four-by-four
principal minor is a Gram matrix, hence positive semidefinite. -/
theorem blockSumMinor_posSemidef {u v : H.Γa} (huv : u ≠ v)
    (hnav : ¬H.orthGraph.Adj u v) :
    (Computations.C1.blockSumMinor
      (Fintype.card (H.orthGraph.commonNeighbors u v) : ℝ)).PosSemidef := by
  classical
  have hgram := H.gram_blockSumVectors huv hnav
  rw [Computations.C1.blockSumMinor_eq_submatrix, ← hgram]
  exact Matrix.posSemidef_gram ℝ (fun i : Fin 4 ↦ H.blockSumVectors huv hnav i.succ)

/-- Step 210paperBound of `lem:2.10` ([CGSS, Lemma 2.10]): the paper's independent
Gram-matrix proof of `k ≤ 5`, using the corrected minor and computation C1. -/
theorem card_commonNeighbors_le_five_of_gram {u v : H.Γa} (huv : u ≠ v)
    (hnav : ¬H.orthGraph.Adj u v) : Fintype.card (H.orthGraph.commonNeighbors u v) ≤ 5 := by
  -- 210psd and 210bound: the nonnegative determinant bounds `k` independently.
  have hd := (H.blockSumMinor_posSemidef huv hnav).det_nonneg
  rw [Computations.C1.det_blockSumMinor] at hd
  by_contra hn
  have hk : (5 : ℝ) < Fintype.card (H.orthGraph.commonNeighbors u v) := by
    exact_mod_cast Nat.lt_of_not_ge hn
  have hp : (0 : ℝ) < 2 * (Fintype.card (H.orthGraph.commonNeighbors u v) : ℝ) ^ 5 :=
    mul_pos (by norm_num) (pow_pos (by linarith) _)
  exact (not_lt_of_ge hd) (mul_neg_of_pos_of_neg hp (by linarith))

end LineSystem.Hyp24
