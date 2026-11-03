/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Frame
import LineGraphs.LineSystem.ModelSpans

/-!
# Computation C6 for Aₙ and Dₙ

The coordinate frame matrices `K = ∑ v vᵀ` of the two classical families, over the integer roots
(both signs), in every dimension (steps `s3c6A` and `s3c6D` of `blueprint/sec3-rootsystems.tex`):
`K = 2((n + 1)I - J)` for `Aₙ` and `K = 4(n - 1)I` for `Dₙ`. Restricted to the span (the
coordinate-sum-zero hyperplane for `Aₙ`), the frame operator is `2(n + 1)` and `4(n - 1)` times
the identity (steps `s3frameA`, `s3frameD`).
-/

open scoped RealInnerProductSpace
open Finset Submodule

namespace Computations.C6

open LineSystem

private theorem pairVector_one_neg_one_self {n : ℕ} (i : Fin n) :
    pairVector i i (1 : ℤ) (-1) = 0 := by
  ext k
  simp only [pairVector, Pi.add_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs <;> norm_num

-- Computation C6
/-- C6, step `s3c6A`: for `Aₙ`, `K = 2((n + 1)I - J)`. -/
theorem an_frame_matrix (n : ℕ) (k l : Fin (n + 1)) :
    ∑ a : An.Index n, An.root a k * An.root a l =
      2 * (((n : ℤ) + 1) * (if k = l then 1 else 0) - 1) := by
  let F : Fin (n + 1) × Fin (n + 1) → ℤ := fun p =>
    pairVector p.1 p.2 1 (-1) k * pairVector p.1 p.2 1 (-1) l
  have h1 : ∑ a : An.Index n, An.root a k * An.root a l = ∑ p, F p := by
    change ∑ a : AnIndex n, F a.val = _
    rw [← Finset.sum_filter_of_ne (p := fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2)]
    · exact (Finset.sum_subtype _ (by simp) F).symm
    intro p _ h hp
    apply h
    simp only [F, hp, pairVector_one_neg_one_self, Pi.zero_apply, mul_zero]
  rw [h1, Fintype.sum_prod_type]
  simp only [F, pairVector, Pi.add_apply, Pi.single_apply]
  simp [mul_add, mul_ite, Finset.sum_add_distrib, Finset.sum_ite_eq, eq_comm]
  split_ifs <;> simp; ring

private theorem sum_lt_indicator (n : ℕ) (k : Fin n) :
    ∑ i : Fin n, ∑ j : Fin n,
      (if i < j then (if i = k then (1 : ℤ) else 0) + (if j = k then 1 else 0) else 0) =
      (n : ℤ) - 1 := by
  set a : Fin n → ℤ := fun i => if i = k then 1 else 0 with ha
  have hsplit : ∀ i j : Fin n, (if i < j then a i + a j else 0) =
      (if i < j then a i else 0) + (if i < j then a j else 0) := by
    intro i j
    split_ifs <;> simp
  have hswap : ∑ i : Fin n, ∑ j : Fin n, (if i < j then a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, (if j < i then a i else 0) := Finset.sum_comm
  have key : ∀ i j : Fin n, (if i < j then a i else 0) + (if j < i then a i else 0) =
      if i ≠ j then a i else 0 := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  change ∑ i : Fin n, ∑ j : Fin n, (if i < j then a i + a j else 0) = _
  simp only [hsplit, Finset.sum_add_distrib]
  rw [hswap, ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, key]
  simp only [ha]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  have hc : (univ.filter fun x : Fin n => ¬k = x) = univ.erase k := by
    ext
    simp [eq_comm]
  simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    add_zero, hc, Finset.filter_true_of_mem (fun _ _ => trivial)]
  rw [Finset.card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Fin.pos k).ne')]
  simp

private theorem dn_sign_sum {n : ℕ} (i j k l : Fin n) (hij : i ≠ j) :
    ∑ st : Bool × Bool, pairVector i j (rootSign st.1) (rootSign st.2) k *
      pairVector i j (rootSign st.1) (rootSign st.2) l =
      if k = l then 4 * ((if i = k then 1 else 0) + (if j = k then 1 else 0)) else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, pairVector, Pi.add_apply, Pi.single_apply, rootSign, ite_true,
    Bool.false_eq_true, ite_false]
  by_cases hk : k = l
  · subst hk
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [eq_comm]
  · by_cases hi : k = i <;> by_cases hj : k = j <;> by_cases hi' : l = i <;>
      by_cases hj' : l = j <;> simp_all [eq_comm]

-- Computation C6
/-- C6, step `s3c6D`: for `Dₙ`, `K = 4(n - 1)I`. -/
theorem dn_frame_matrix (n : ℕ) (k l : Fin n) :
    ∑ a : Dn.Index n, Dn.root a k * Dn.root a l =
      4 * ((n : ℤ) - 1) * (if k = l then 1 else 0) := by
  have h1 : ∑ a : Dn.Index n, Dn.root a k * Dn.root a l =
      ∑ p : {p : Fin n × Fin n // p.1 < p.2},
        (if k = l then 4 * ((if p.val.1 = k then 1 else 0) +
          (if p.val.2 = k then 1 else 0)) else 0) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun p _ => dn_sign_sum _ _ k l p.property.ne
  rw [h1]
  by_cases hkl : k = l
  · subst hkl
    simp only [ite_true, mul_one]
    rw [← Finset.mul_sum]
    have h2 : ∑ p : {p : Fin n × Fin n // p.1 < p.2},
        ((if p.val.1 = k then (1 : ℤ) else 0) + (if p.val.2 = k then 1 else 0)) =
        ∑ p : Fin n × Fin n, if p.1 < p.2 then
          (if p.1 = k then (1 : ℤ) else 0) + (if p.2 = k then 1 else 0) else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
        (fun p : Fin n × Fin n =>
          (if p.1 = k then (1 : ℤ) else 0) + (if p.2 = k then 1 else 0))).symm
    rw [h2, Fintype.sum_prod_type, sum_lt_indicator]
  · simp [hkl]

end Computations.C6

namespace LineSystem

open Computations.C6

/-- The frame operator of `Aₙ` in coordinates: `2((n + 1)xₖ - ∑ⱼ xⱼ)`. -/
theorem frameSum_An_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (k : Fin (n + 1)) :
    (An n).frameSum x k = 2 * (((n : ℝ) + 1) * x k - ∑ j, x j) := by
  rw [(An.integerModel n).frameSum_apply]
  change 1 * 1 * ∑ j, ((∑ a : An.Index n, An.root a k * An.root a j : ℤ) : ℝ) * x j = _
  simp only [an_frame_matrix, one_mul]
  push_cast
  simp only [sub_mul, mul_assoc, ← Finset.mul_sum, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, one_mul]
  simp

-- Lemma "the frame identity within the span", step s3frameA
/-- C6 for `Aₙ`: on the span of the roots (coordinate sum zero), the frame operator is
`2(n + 1) = 4N/n` times the identity. -/
theorem isFrame_An (n : ℕ) : (An n).IsFrame (2 * ((n : ℝ) + 1)) := by
  intro x hx
  have hs : ∑ j, x j = 0 := span_An_le_ker_coordinateSum n hx
  ext k
  rw [frameSum_An_apply, hs, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The frame operator of `Dₙ` in coordinates: `4(n - 1)x`. -/
theorem frameSum_Dn (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (Dn n).frameSum x = (4 * ((n : ℝ) - 1)) • x := by
  ext k
  rw [(Dn.integerModel n).frameSum_apply]
  change 1 * 1 * ∑ j, ((∑ a : Dn.Index n, Dn.root a k * Dn.root a j : ℤ) : ℝ) * x j = _
  simp only [dn_frame_matrix, one_mul]
  push_cast
  simp [mul_ite, Finset.sum_ite_eq, mul_assoc]

-- Lemma "the frame identity within the span", step s3frameD
/-- C6 for `Dₙ`: the frame operator is `4(n - 1) = 4N/n` times the identity (on all of `ℝⁿ`). -/
theorem isFrame_Dn (n : ℕ) : (Dn n).IsFrame (4 * ((n : ℝ) - 1)) :=
  fun x _ => frameSum_Dn n x

end LineSystem
