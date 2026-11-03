/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Hadamard row products

Definition `def:6-pairs` and Lemma `lem:6-gram` of the Section 6 blueprint for [CGSS].
Pairs are represented by increasing pairs of row indices. Agreement counts and Hypothesis 6.1
use integer arithmetic, so subtraction in the agreement condition is not truncated.
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix

/-- The two-subsets indexing `P` in blueprint Definition `def:6-pairs`. -/
abbrev HadamardPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The real Hadamard product of two rows (also defined when the rows coincide). -/
def hadamardRowProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun c ↦ (H i c : ℝ) * (H j c : ℝ))

/-- Blueprint Definition `def:6-pairs`: the matrix `P` of pairwise row products. -/
def hadamardPairs {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (HadamardPair n) (Fin n) ℝ :=
  fun p c ↦ (H p.1.1 c : ℝ) * (H p.1.2 c : ℝ)

/-- Blueprint Definition `def:6-pairs`: columns in which four rows agree. -/
def fourRowAgreeCount {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j k l : Fin n) : ℕ :=
  (Finset.univ.filter fun c ↦ H i c = H j c ∧ H j c = H k c ∧ H k c = H l c).card

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)

-- Hypothesis 6.1
/-- Hypothesis 6.1 of [CGSS], with the nonnegative parameter `x`. -/
def FourRowAgreement (_hH : H.IsHadamard) (x : ℕ) : Prop :=
  ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    (8 * (H.fourRowAgreeCount i j k l : ℤ)) ∈
      ({(n : ℤ), (n : ℤ) - x, (n : ℤ) + x} : Set ℤ)

include hH

/-- The entry calculation `s6gsq` in blueprint Lemma `lem:6-gram`. -/
theorem entry_sq (i c : Fin n) : (H i c : ℝ) ^ 2 = 1 := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i c) with h | h <;>
    simp [h]

/-- Row orthogonality, step `s6gorth` of blueprint Lemma `lem:6-gram`. -/
theorem sum_row_mul (i j : Fin n) :
    ∑ c, (H i c : ℝ) * (H j c : ℝ) = if i = j then (n : ℝ) else 0 := by
  have h := congrFun (congrFun hH.mul_conjTranspose i) j
  simp only [mul_apply, conjTranspose_apply, star_trivial, smul_apply, smul_eq_mul,
    Fintype.card_fin, one_apply] at h
  split_ifs with hij
  · subst j
    simpa using congrArg (fun z : ℤ ↦ (z : ℝ)) h
  · simpa [hij] using congrArg (fun z : ℤ ↦ (z : ℝ)) h

/-- Column orthogonality for the computation in blueprint Lemma `lem:6-P`. -/
theorem sum_col_mul (c d : Fin n) :
    ∑ i, (H i c : ℝ) * (H i d : ℝ) = if c = d then (n : ℝ) else 0 :=
  hH.transpose.sum_row_mul c d

/-- Blueprint Lemma `lem:6-gram`, part 1: entries of `P` are signs. -/
theorem hadamardPairs_apply_mem (p : HadamardPair n) (c : Fin n) :
    H.hadamardPairs p c = 1 ∨ H.hadamardPairs p c = -1 := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem p.1.1 c) with h | h <;>
    rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem p.1.2 c) with g | g <;>
    simp [hadamardPairs, h, g]

/-- Blueprint Lemma `lem:6-gram`, part 1, step `s6gone`. -/
theorem inner_hadamardPairs_self (i j : Fin n) :
    ⟪H.hadamardRowProduct i j, H.hadamardRowProduct i j⟫ = n := by
  simp only [hadamardRowProduct, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  calc
    ∑ c, ((H i c : ℝ) * H j c) * ((H i c : ℝ) * H j c) = ∑ _c : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = (H i c : ℝ) ^ 2 * (H j c : ℝ) ^ 2 := by ring
        _ = 1 := by rw [hH.entry_sq, hH.entry_sq]; norm_num
    _ = n := by simp

/-- Blueprint Lemma `lem:6-gram`, part 2, step `s6gtwo`. The common row need not be distinct
from the other two for this identity. -/
theorem inner_hadamardRowProduct_of_ne (i j k : Fin n) (hjk : j ≠ k) :
    ⟪H.hadamardRowProduct i j, H.hadamardRowProduct i k⟫ = 0 := by
  simp only [hadamardRowProduct, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  calc
    ∑ c, ((H i c : ℝ) * H k c) * ((H i c : ℝ) * H j c) =
        ∑ c, (H j c : ℝ) * H k c := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = (H i c : ℝ) ^ 2 * ((H j c : ℝ) * H k c) := by ring
        _ = _ := by rw [hH.entry_sq]; ring
    _ = 0 := by rw [hH.sum_row_mul]; simp [hjk]

/-- Blueprint Lemma `lem:6-gram`, part 2: two row pairs meeting in exactly one row are
orthogonal (`s6gtwo`). -/
theorem inner_hadamardPairs_of_card_inter_eq_one (i j k : Fin n)
    (_hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k) :
    ⟪H.hadamardRowProduct i j, H.hadamardRowProduct i k⟫ = 0 :=
  hH.inner_hadamardRowProduct_of_ne i j k hjk

omit hH in
/-- The sixteen sign cases in step `s6gsigns` of blueprint Lemma `lem:6-gram`. -/
theorem four_sign_identity (a b c d : ℤ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) :
    (8 : ℤ) * (if a = b ∧ b = c ∧ c = d then 1 else 0) =
      1 + a * b + a * c + a * d + b * c + b * d + c * d + a * b * c * d := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> decide

/-- Blueprint Lemma `lem:6-gram`, part 3: sum the sign identity, then cancel the six
orthogonal row products (`s6gsum`). -/
theorem inner_hadamardPairs_of_disjoint (i j k l : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫ =
      8 * (H.fourRowAgreeCount i j k l : ℝ) - n := by
  have hs (c : Fin n) := four_sign_identity (H i c) (H j c) (H k c) (H l c)
    (Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i c))
    (Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem j c))
    (Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem k c))
    (Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem l c))
  have hs' (c : Fin n) :
      (8 : ℝ) * (if H i c = H j c ∧ H j c = H k c ∧ H k c = H l c then 1 else 0) =
      1 + (H i c : ℝ) * H j c + (H i c : ℝ) * H k c + (H i c : ℝ) * H l c +
        (H j c : ℝ) * H k c + (H j c : ℝ) * H l c + (H k c : ℝ) * H l c +
        (H i c : ℝ) * H j c * H k c * H l c := by exact_mod_cast hs c
  have ht := congrArg (fun f : Fin n → ℝ ↦ ∑ c, f c) (funext hs')
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hH.sum_row_mul,
    ite_eq_right hij, ite_eq_right hik, ite_eq_right hil, ite_eq_right hjk,
    ite_eq_right hjl, ite_eq_right hkl,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at ht
  have hc : (∑ c : Fin n, if H i c = H j c ∧ H j c = H k c ∧ H k c = H l c
      then (1 : ℝ) else 0) = H.fourRowAgreeCount i j k l := by
    simp [fourRowAgreeCount, ← Finset.sum_boole]
  rw [hc] at ht
  simp only [hadamardRowProduct, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  have he : (∑ c, ((H k c : ℝ) * H l c) * ((H i c : ℝ) * H j c)) =
      ∑ c, (H i c : ℝ) * H j c * H k c * H l c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he]
  linarith

/-- Blueprint Lemma `lem:6-gram`, part 4, step `s6gfour`: all products lie in `jᗮ`. -/
theorem inner_hadamardPairs_one (i j : Fin n) (hij : i ≠ j) :
    ⟪H.hadamardRowProduct i j, (WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)))⟫ = 0 := by
  simpa [hadamardRowProduct, PiLp.inner_apply, RCLike.inner_apply, hij] using
    hH.sum_row_mul i j

end IsHadamard
end Matrix
