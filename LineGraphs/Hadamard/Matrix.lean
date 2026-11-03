/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Pairs

/-!
# The matrix of Hadamard products

Blueprint Lemma `lem:6-P` and the quadratic identity `lem:6-quadratic` of [CGSS], Section 6.
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix

/-- The number of row pairs in blueprint Definition `def:6-pairs`. -/
theorem card_hadamardPair (n : ℕ) : Fintype.card (HadamardPair n) = n.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin n))

/-- Expanding the square of a sum, step `s6Psquare` of blueprint Lemma `lem:6-P`. -/
theorem two_mul_sum_hadamardPair {n : ℕ} (u : Fin n → ℝ) :
    2 * ∑ p : HadamardPair n, u p.1.1 * u p.1.2 =
      (∑ i, u i) ^ 2 - ∑ i, u i ^ 2 := by
  have hp : (∑ p : HadamardPair n, u p.1.1 * u p.1.2) =
      ∑ i, ∑ j, if i < j then u i * u j else 0 := by
    rw [← Fintype.sum_prod_type (fun p : Fin n × Fin n ↦
      if p.1 < p.2 then u p.1 * u p.2 else 0)]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter
      (fun p : Fin n × Fin n ↦ p.1 < p.2)) (by simp)
      (fun p ↦ u p.1 * u p.2)).symm
  have ht : (∑ i, ∑ j, if j < i then u i * u j else 0) =
      ∑ i, ∑ j, if i < j then u i * u j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hs : (∑ i, u i) ^ 2 =
      (∑ i, ∑ j, if i < j then u i * u j else 0) +
      (∑ i, ∑ j, if j < i then u i * u j else 0) + ∑ i, u i ^ 2 := by
    rw [pow_two, Fintype.sum_mul_sum]
    calc
      _ = ∑ i, ∑ j, ((if i < j then u i * u j else 0) +
          (if j < i then u i * u j else 0) + (if i = j then u i ^ 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.ne, not_lt_of_gt h]
        · simp [pow_two]
        · simp [h, h.ne', not_lt_of_gt h]
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [ht, ← hp] at hs
  linarith

/-- The matrix in Section 6 of [CGSS] (blueprint `def:6-CH`):
`C_H = (PPᵀ - nI)/x`. At `x = 0` the inverse convention gives the zero matrix;
the paper's quotient is used only when `x > 0`. -/
noncomputable def hadamardSignedAdj {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (x : ℕ) :
    Matrix (HadamardPair n) (HadamardPair n) ℝ :=
  (x : ℝ)⁻¹ • (H.hadamardPairs * H.hadamardPairsᵀ - (n : ℝ) • 1)

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Blueprint Lemma `lem:6-P`, part 1: the paper's formula for `PᵀP`. -/
theorem transpose_hadamardPairs_mul :
    H.hadamardPairsᵀ * H.hadamardPairs =
      ((n : ℝ) ^ 2 / 2) • 1 - ((n : ℝ) / 2) • Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  ext c d
  have hp := two_mul_sum_hadamardPair (fun i ↦ (H i c : ℝ) * H i d)
  have hs : (∑ i, ((H i c : ℝ) * H i d) ^ 2) = n := by
    simp only [mul_pow, hH.entry_sq, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hH.sum_col_mul, hs] at hp
  have he : (H.hadamardPairsᵀ * H.hadamardPairs) c d =
      ∑ p : HadamardPair n, ((H p.1.1 c : ℝ) * H p.1.1 d) *
        ((H p.1.2 c : ℝ) * H p.1.2 d) := by
    simp only [mul_apply, transpose_apply, hadamardPairs]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  simp only [sub_apply, smul_apply, smul_eq_mul, one_apply, of_apply, mul_one]
  split_ifs at hp ⊢ <;> nlinarith

/-- Blueprint Lemma `lem:6-P`, part 2: `Pj = 0`. -/
theorem hadamardPairs_mulVec_one : H.hadamardPairs *ᵥ (fun _ ↦ 1) = 0 := by
  ext p
  simpa [mulVec, dotProduct, hadamardPairs, p.2.ne] using
    hH.sum_row_mul p.1.1 p.1.2

/-- The vanishing `PJ = 0` used in step `s6Pthree` of blueprint Lemma `lem:6-P`. -/
theorem hadamardPairs_mul_allOnes :
    H.hadamardPairs * Matrix.of (fun _ _ : Fin n ↦ (1 : ℝ)) = 0 := by
  ext p c
  simpa [mul_apply, mulVec, dotProduct] using congrFun hH.hadamardPairs_mulVec_one p

/-- Blueprint Lemma `lem:6-P`, part 3: the Gram square. -/
theorem hadamardPairs_gram_sq :
    (H.hadamardPairs * H.hadamardPairsᵀ) ^ 2 =
      ((n : ℝ) ^ 2 / 2) • (H.hadamardPairs * H.hadamardPairsᵀ) := by
  rw [pow_two, Matrix.mul_assoc, ← Matrix.mul_assoc H.hadamardPairsᵀ,
    hH.transpose_hadamardPairs_mul,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
    hH.hadamardPairs_mul_allOnes, Matrix.zero_mul, smul_zero, sub_zero]

end IsHadamard
end Matrix
