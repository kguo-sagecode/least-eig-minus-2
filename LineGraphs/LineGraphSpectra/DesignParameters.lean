/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Incidence
import LineGraphs.Spectral.AllOnes

/-!
# Design parameters and the real incidence matrix

The auxiliary lemma `lem:design` used in Theorem 5.8 of [CGSS]. The shared `Design`
is Hall–Connor's labelled design, and `Design.incMatrix` remains integer valued.
`Design.realIncMatrix` is its entrywise cast to ℝ; every spectral statement below
uses this cast. No second design structure is introduced.
The observation after Theorem 5.8 that case (i) requires `v ≤ 4` is used inside
the corollaries' proofs and is not packaged as a separate lemma.
-/

open scoped BigOperators Matrix
open Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ} (D : Design P B v k b r lam)

include D

/-- Step `s5dsflags` of `lem:design`, Theorem 5.8 of [CGSS]: count flags. -/
theorem b_mul_k_eq_v_mul_r : b * k = v * r := by
  have h := Finset.card_mul_eq_card_mul (fun p label ↦ p ∈ D.block label)
    (s := Finset.univ) (t := Finset.univ) (m := r) (n := k)
    (fun p _ ↦ D.card_blocksThrough p)
    (fun label _ ↦ by simpa [Finset.bipartiteBelow] using D.card_block label)
  simpa [D.card_points, D.card_blocks] using h.symm

/-- Step `s5dspairs` of `lem:design`, Theorem 5.8 of [CGSS]: count pairs at a point. -/
theorem r_mul_k_sub_one_eq : r * (k - 1) = lam * (v - 1) := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by
    rw [D.card_points]
    exact lt_trans Nat.zero_lt_one D.one_lt_v)
  let p : P := Classical.arbitrary P
  have h := Finset.card_mul_eq_card_mul (fun q label ↦ q ∈ D.block label)
    (s := Finset.univ.erase p) (t := Finset.univ.filter (fun label ↦ p ∈ D.block label))
    (m := lam) (n := k - 1) (fun q hq ↦ ?_) (fun label hlabel ↦ ?_)
  · simpa [Finset.card_erase_of_mem (Finset.mem_univ p), D.card_points,
      D.card_blocksThrough, Nat.mul_comm] using h.symm
  · have hpq : p ≠ q := (Finset.mem_erase.mp hq).1.symm
    simpa [Finset.bipartiteAbove, Finset.filter_filter] using
      D.card_blocksThroughPair p q hpq
  · have hp : p ∈ D.block label := (Finset.mem_filter.mp hlabel).2
    have he : (Finset.univ.erase p).bipartiteBelow (fun q label ↦ q ∈ D.block label)
        label = (D.block label).erase p := by
      ext q
      simp [Finset.bipartiteBelow, and_comm]
    rw [he, Finset.card_erase_of_mem hp, D.card_block]

/-- Step `s5dskv` of `lem:design`, Theorem 5.8 of [CGSS]: blocks are point subsets. -/
theorem k_le_v : k ≤ v := by
  have : Nonempty B := Fintype.card_pos_iff.mp (D.card_blocks.symm ▸ D.b_pos)
  simpa [D.card_block, D.card_points] using
    Finset.card_le_univ (D.block (Classical.arbitrary B))

/-- Step `s5dslamzero` of `lem:design`, Theorem 5.8 of [CGSS]: positive replication. -/
theorem r_pos : 0 < r := by
  have h := D.b_mul_k_eq_v_mul_r
  have := D.b_pos
  have := D.one_lt_k
  by_contra hzero
  have : r = 0 := by omega
  simp only [this, Nat.mul_zero] at h
  nlinarith

/-- Step `s5dslam` of `lem:design`, Theorem 5.8 of [CGSS]: positive pair count. -/
theorem one_le_lam : 1 ≤ lam := by
  have h := D.r_mul_k_sub_one_eq
  have hr := D.r_pos
  have hk := D.one_lt_k
  by_contra hl
  have : lam = 0 := by omega
  simp only [this, Nat.zero_mul] at h
  have : 0 < k - 1 := by omega
  nlinarith

/-- Step `s5dsrlam` of `lem:design`, Theorem 5.8 of [CGSS]: replication bounds λ. -/
theorem lam_le_r : lam ≤ r := by
  have h := D.r_mul_k_sub_one_eq
  have hv := D.one_lt_v
  have hk := D.k_le_v
  have hsub : k - 1 ≤ v - 1 := Nat.sub_le_sub_right hk 1
  have hmul := Nat.mul_le_mul_left r hsub
  have hv' : 0 < v - 1 := by omega
  nlinarith

/-- Step `s5dsrlam` of `lem:design`, Theorem 5.8 of [CGSS]: equality means full blocks. -/
theorem lam_eq_r_iff : lam = r ↔ k = v := by
  have h := D.r_mul_k_sub_one_eq
  have hr := D.r_pos
  have hk := D.one_lt_k
  have hv := D.one_lt_v
  constructor
  · intro he
    rw [he] at h
    have : k - 1 = v - 1 := by nlinarith
    omega
  · intro he
    rw [he] at h
    have : 0 < v - 1 := by omega
    nlinarith

/-- Step `s5dsfull` of `lem:design`, Theorem 5.8 of [CGSS]: every block is full. -/
theorem block_eq_univ_of_k_eq_v (hkv : k = v) (label : B) : D.block label = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [D.card_block, D.card_points, hkv]

/-- The explicit ℤ-to-ℝ interface in `lem:design`, Theorem 5.8 of [CGSS]. -/
def realIncMatrix : Matrix P B ℝ := D.incMatrix.map (Int.castRingHom ℝ)

/-- The real zero-one entries in `lem:design`, Theorem 5.8 of [CGSS]. -/
theorem realIncMatrix_apply (p : P) (label : B) :
    D.realIncMatrix p label = if p ∈ D.block label then 1 else 0 := by
  simp [realIncMatrix, incMatrix]

/-- The real row sums in `lem:incidence`, Theorem 5.8 of [CGSS]. -/
theorem realIncMatrix_row_sum (p : P) : ∑ label, D.realIncMatrix p label = (r : ℝ) := by
  simp [D.realIncMatrix_apply, D.card_blocksThrough]

/-- The real column sums in `lem:incidence`, Theorem 5.8 of [CGSS]. -/
theorem realIncMatrix_col_sum (label : B) : ∑ p, D.realIncMatrix p label = (k : ℝ) := by
  simp [D.realIncMatrix_apply, D.card_block]

/-- Step `s5dsgram` of `lem:design`, Theorem 5.8 of [CGSS], after the explicit real cast. -/
theorem incMatrix_mul_transpose :
    D.realIncMatrix * D.realIncMatrixᵀ =
      ((r : ℝ) - lam) • (1 : Matrix P P ℝ) +
        (lam : ℝ) • Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  unfold realIncMatrix
  rw [← Matrix.transpose_map, ← Matrix.map_mul]
  ext p q
  simp only [Matrix.map_apply, D.incMatrix_mul_transpose_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  by_cases hpq : p = q <;> simp [hpq]

/-- Step `s5dsspec` of `lem:design`, Theorem 5.8 of [CGSS]: the design Gram spectrum. -/
theorem spectrumMultiset_incMatrix_mul_transpose :
    (D.realIncMatrix * D.realIncMatrixᵀ).spectrumMultiset =
      {(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam) := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by
    rw [D.card_points]
    exact lt_trans Nat.zero_lt_one D.one_lt_v)
  have hk := D.one_lt_k
  have hv := D.one_lt_v
  have hp : (r : ℝ) * ((k : ℝ) - 1) = (lam : ℝ) * ((v : ℝ) - 1) := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) D.r_mul_k_sub_one_eq
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 1 ≤ v), Nat.cast_one] using h
  rw [D.incMatrix_mul_transpose, Matrix.spectrumMultiset_smul_one_add_smul_allOnes,
    D.card_points]
  congr 2
  linarith

/-- Steps `s558nbfishrho` and `s5dsfisher`, Theorem 5.8 of [CGSS]: full row rank. -/
theorem rank_realIncMatrix_of_lam_lt_r (hl : lam < r) : D.realIncMatrix.rank = v := by
  have hrk : (0 : ℝ) < (r : ℝ) * k := by
    exact_mod_cast Nat.mul_pos D.r_pos (by have := D.one_lt_k; omega)
  have hrl : (0 : ℝ) < (r : ℝ) - lam := sub_pos.mpr (by exact_mod_cast hl)
  have hsym : (D.realIncMatrix * D.realIncMatrixᵀ).IsHermitian := by
    simp [isHermitian_iff_isSymm, Matrix.IsSymm]
  have hr := hsym.rank_add_eigenvalueMultiplicity_zero
  rw [rank_self_mul_transpose, D.card_points] at hr
  have hz : (D.realIncMatrix * D.realIncMatrixᵀ).eigenvalueMultiplicity 0 = 0 := by
    change Multiset.count 0 (D.realIncMatrix * D.realIncMatrixᵀ).spectrumMultiset = 0
    rw [D.spectrumMultiset_incMatrix_mul_transpose]
    simp [Multiset.mem_replicate, ne_of_lt hrk, ne_of_lt hrl]
  omega

/-- Step `s5dsfisher` of `lem:design`, Theorem 5.8 of [CGSS]: Fisher's inequality. -/
theorem v_le_b_of_lam_lt_r (hl : lam < r) : v ≤ b := by
  simpa [D.rank_realIncMatrix_of_lam_lt_r hl, D.card_blocks] using
    D.realIncMatrix.rank_le_card_width

end Design
