/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.TraceRank
import LineGraphs.Spectral.Positivity

/-!
# Trace bounds and scaled idempotents

Lemma 3.6 and Theorem 10.1 of the spectral toolkit. The singular-minor and
zero-product rank bounds do not need symmetry or positivity.
-/

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

namespace IsHermitian

variable (hA : A.IsHermitian)

include hA

private theorem trace_rank_gap :
    2 * ((A.rank : ℝ) * (A ^ 2).trace - A.trace ^ 2) =
      ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0),
        ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0),
          (hA.eigenvalues i - hA.eigenvalues j) ^ 2 := by
  let s := Finset.univ.filter fun i => hA.eigenvalues i ≠ 0
  -- Step `tracerank-traces`: zero eigenvalues do not affect either sum.
  have hs (j : ℕ) (hj : 0 < j) :
      ∑ i ∈ s, hA.eigenvalues i ^ j = ∑ i, hA.eigenvalues i ^ j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : hA.eigenvalues i = 0 := by simpa [s] using hi
    rw [hz, zero_pow (by omega)]
  have ht : A.trace = ∑ i ∈ s, hA.eigenvalues i := by
    simpa using (hA.trace_pow_eq_sum 1).trans (hs 1 (by omega)).symm
  have ht2 : (A ^ 2).trace = ∑ i ∈ s, hA.eigenvalues i ^ 2 :=
    (hA.trace_pow_eq_sum 2).trans (hs 2 (by omega)).symm
  -- Step `tracerank-traces`: the nonzero eigenvalues count the rank.
  have hr : A.rank = s.card := by
    rw [hA.rank_eq_card_non_zero_eigs]
    simp only [s, Fintype.card_subtype]
  -- Step `tracerank-expand`: sum over both orientations of each pair.
  have hexpand : ∑ i ∈ s, ∑ j ∈ s, (hA.eigenvalues i - hA.eigenvalues j) ^ 2 =
      2 * ((s.card : ℝ) * (∑ i ∈ s, hA.eigenvalues i ^ 2) -
        (∑ i ∈ s, hA.eigenvalues i) ^ 2) := by
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
    simp_rw [← Finset.mul_sum]
    ring
  rw [ht, ht2, hr]
  exact hexpand.symm

/-- Lemma 3.6 of the spectral toolkit: the squared trace is at most rank times the second trace
moment.
The inequality holds for all real symmetric matrices, without positivity. -/
theorem trace_sq_le_rank_mul_trace_sq :
    A.trace ^ 2 ≤ (A.rank : ℝ) * (A ^ 2).trace := by
  -- Step `tracerank-equal`: every squared eigenvalue difference is nonnegative.
  have hn : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0),
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0),
        (hA.eigenvalues i - hA.eigenvalues j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← hA.trace_rank_gap] at hn
  linarith

/-- Lemma 3.6 of the spectral toolkit, the equality case: all nonzero eigenvalues coincide. This
includes
the zero matrix, whose nonzero-eigenvalue index set is empty. -/
theorem trace_sq_eq_rank_mul_trace_sq_iff :
    A.trace ^ 2 = (A.rank : ℝ) * (A ^ 2).trace ↔
      ∀ i j, hA.eigenvalues i ≠ 0 → hA.eigenvalues j ≠ 0 →
        hA.eigenvalues i = hA.eigenvalues j := by
  -- Step `tracerank-equal`: a nonnegative sum vanishes exactly when every term vanishes.
  have hsum : (∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0),
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0),
        (hA.eigenvalues i - hA.eigenvalues j) ^ 2) = 0 ↔
      ∀ i j, hA.eigenvalues i ≠ 0 → hA.eigenvalues j ≠ 0 →
        hA.eigenvalues i = hA.eigenvalues j := by
    rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _]
    simp only [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _,
      Finset.mem_filter, Finset.mem_univ, true_and, sq_eq_zero_iff, sub_eq_zero]
    constructor
    · intro h i j hi hj
      exact h i hi j hj
    · intro h i hi j hj
      exact h i j hi hj
  rw [← hsum, ← hA.trace_rank_gap]
  constructor <;> intro h <;> linarith

/-- The notation catalogue's spectral-moment form of the trace/rank inequality. -/
theorem trace_sq_le_rank_mul_sum_sq :
    A.trace ^ 2 ≤ (A.rank : ℝ) * (A.spectrumMultiset.map (fun μ => μ ^ 2)).sum := by
  have h := hA.trace_sq_le_rank_mul_trace_sq
  rwa [hA.trace_pow_eq_sum_spectrumMultiset] at h

/-- Theorem 10.1 of the spectral toolkit, step `scaled-roots`: a scaled idempotent has only the
roots 0 and b. -/
theorem eq_zero_or_eq_of_mem_spectrumMultiset_of_sq_eq_smul {b μ : ℝ}
    (hsq : A ^ 2 = b • A) (hμ : μ ∈ A.spectrumMultiset) : μ = 0 ∨ μ = b := by
  -- Step `scaled-roots`: apply the polynomial calculus to t² - bt.
  have hp : aeval A (X ^ 2 - C b * X) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_mul, aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, hsq, sub_self]
  have he := (hA.aeval_eq_zero_iff _).mp hp μ hμ
  have hz : μ * (μ - b) = 0 := by
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C] at he
    nlinarith
  exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp

/-- Theorem 10.1 of the spectral toolkit: a positive multiple of a symmetric idempotent is
positive semidefinite. -/
theorem posSemidef_of_sq_eq_pos_smul {b : ℝ} (hb : 0 < b)
    (hsq : A ^ 2 = b • A) : A.PosSemidef := by
  -- Step `scaled-positive`: both possible spectral values are nonnegative.
  have hnonneg (μ : ℝ) (hμ : μ ∈ A.spectrumMultiset) : 0 ≤ μ := by
    rcases hA.eq_zero_or_eq_of_mem_spectrumMultiset_of_sq_eq_smul hsq hμ with rfl | rfl
    · exact le_rfl
    · exact hb.le
  exact hA.posSemidef_iff_spectrumMultiset_nonneg.mpr hnonneg

/-- Theorem 10.1 of the spectral toolkit: the rank of a symmetric scaled idempotent is trace
divided by
the nonzero scale. Positivity of the scale is unnecessary for this identity. -/
theorem rank_eq_trace_div_of_sq_eq_smul {b : ℝ} (hb : b ≠ 0)
    (hsq : A ^ 2 = b • A) : (A.rank : ℝ) = A.trace / b := by
  -- Step `scaled-trace`: every nonzero eigenvalue contributes exactly b to the trace.
  have ht : A.trace = b * (A.rank : ℝ) := by
    have he (i : n) : hA.eigenvalues i = if hA.eigenvalues i ≠ 0 then b else 0 := by
      rcases hA.eq_zero_or_eq_of_mem_spectrumMultiset_of_sq_eq_smul hsq
        (hA.eigenvalues_mem_spectrumMultiset i) with hi | hi
      · simp [hi]
      · simp [hi, hb]
    calc
      A.trace = ∑ i, hA.eigenvalues i := by simpa using hA.trace_pow_eq_sum 1
      _ = ∑ i, if hA.eigenvalues i ≠ 0 then b else 0 := Finset.sum_congr rfl fun i _ => he i
      _ = b * (A.rank : ℝ) := by
        rw [hA.rank_eq_card_non_zero_eigs]
        simp [Fintype.card_subtype, Finset.sum_ite, mul_comm]
  -- Step `scaled-divide`: cancel the nonzero scale.
  rw [ht, mul_div_cancel_left₀ _ hb]

end IsHermitian

omit [DecidableEq n] in
/-- Theorem 10.1 of the spectral toolkit: a zero product bounds the first rank by the codimension
of the
second image. No idempotence assumption is needed. -/
theorem rank_le_card_sub_rank_of_mul_eq_zero {m : Type*} [Fintype m]
    {B : Matrix n m ℝ} (hAB : A * B = 0) : A.rank ≤ Fintype.card n - B.rank := by
  -- Steps `scaled-image`, `scaled-dim`: Mathlib compares the image with the kernel.
  have h := rank_add_rank_le_card_of_mul_eq_zero hAB
  omega

omit [DecidableEq n] in
/-- Theorem 10.1 of the spectral toolkit: a principal submatrix larger than the ambient rank is
singular.
The index map may even have repetitions. -/
theorem det_principal_submatrix_eq_zero_of_rank_lt {m : Type*} [Fintype m] [DecidableEq m]
    (f : m → n) (hr : A.rank < Fintype.card m) : (A.submatrix f f).det = 0 := by
  -- Steps `scaled-factor`, `scaled-rank`: coordinate restriction cannot increase rank.
  have hle := A.rank_submatrix_le f f
  -- Step `scaled-determinant`: a nonzero determinant would give full rank.
  by_contra hd
  have hfull := rank_of_det_ne_zero hd
  omega

end Matrix
