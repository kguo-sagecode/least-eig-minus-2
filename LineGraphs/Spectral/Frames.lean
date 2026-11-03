/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Gram
import LineGraphs.Spectral.GramProducts
import LineGraphs.Spectral.Applications

/-!
# Tight frames and the relative bound

Theorem 3.7 of the spectral toolkit.
-/

open scoped BigOperators InnerProductSpace

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The frame identity implies the quadratic Gram identity. -/
theorem gram_sq_of_tightFrame (B : Matrix m n ℝ) {b : ℝ} (hB : B * Bᵀ = b • 1) :
    (Bᵀ * B) ^ 2 = b • (Bᵀ * B) := by
  -- Step `bound-poly`: reassociate to use the frame identity.
  have hp : (Bᵀ * B) * (Bᵀ * B) = Bᵀ * (B * Bᵀ) * B := by
    simp only [Matrix.mul_assoc]
  rw [pow_two, hp, hB, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Theorem 3.7 of the spectral toolkit: the Gram spectrum of a positive tight frame, including
its zero modes. -/
theorem spectrumMultiset_gram_of_tightFrame (B : Matrix m n ℝ) {b : ℝ}
    (hb : 0 < b) (hB : B * Bᵀ = b • 1) :
    (Bᵀ * B).spectrumMultiset = Multiset.replicate (Fintype.card m) b +
      Multiset.replicate (Fintype.card n - Fintype.card m) 0 := by
  classical
  -- Step `bound-roots`: the left Gram matrix is scalar.
  have hs : (B * Bᵀ).spectrumMultiset = Multiset.replicate (Fintype.card m) b := by
    rw [hB]
    have h := (isHermitian_zero (n := m) (α := ℝ)).spectrumMultiset_smul_one_add_smul b 0
    simpa [spectrumMultiset, charpoly_zero, Polynomial.roots_X_pow] using h
  -- Step `bound-full`: its zero multiplicity vanishes, so B has full row rank.
  have hz : (B * Bᵀ).eigenvalueMultiplicity 0 = 0 := by
    change (B * Bᵀ).spectrumMultiset.count 0 = 0
    rw [hs]
    simp only [Multiset.count_replicate, ne_of_gt hb, ite_false]
  have hr := Matrix.IsHermitian.rank_add_eigenvalueMultiplicity_zero
    (spectrumMultiset_gram_products B).1.isHermitian
  rw [rank_self_mul_transpose, hz, add_zero] at hr
  -- Step `bound-count`: the positive spectrum transfers, and rank determines the zeros.
  have hg := spectrumMultiset_gram_products B
  rw [hg.2.1.spectrumMultiset_eq_filter_pos_add_replicate_zero,
    ← hg.2.2.1, hs, hg.2.2.2.2, hr]
  congr 1
  apply Multiset.filter_eq_self.mpr
  intro a ha
  have ha' := Multiset.eq_of_mem_replicate ha
  simpa [ha'] using hb

/-- The shifted Gram matrix satisfies the toolkit's two-factor polynomial. -/
theorem shifted_gram_polynomial_of_tightFrame (B : Matrix m n ℝ) {b : ℝ}
    (hB : B * Bᵀ = b • 1) :
    let C := Bᵀ * B - (2 : ℝ) • 1
    (C + (2 : ℝ) • 1) * (C - (b - 2) • 1) = 0 := by
  -- Step `bound-C`: rewrite the two factors as G and G - bI.
  have hc : Bᵀ * B - (2 : ℝ) • 1 - (b - 2) • 1 = Bᵀ * B - b • 1 := by
    rw [sub_smul]
    abel
  dsimp
  rw [sub_add_cancel, hc, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← pow_two, gram_sq_of_tightFrame B hB, sub_self]

omit [DecidableEq n] in
/-- Theorem 3.7 of the spectral toolkit: the relative bound for a finite family of equiangular
unit vectors. -/
theorem card_le_relative_bound_of_abs_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : n → E) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1) (hpair : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| = α)
    (hsmall : (Module.finrank ℝ E : ℝ) * α ^ 2 < 1) :
    (Fintype.card n : ℝ) ≤
      Module.finrank ℝ E * (1 - α ^ 2) / (1 - Module.finrank ℝ E * α ^ 2) := by
  classical
  let G := gram ℝ v
  have hG : G.IsHermitian := isHermitian_gram ℝ v
  -- Step `bound-gramtrace`: count diagonal and off-diagonal squares.
  have ht : G.trace = (Fintype.card n : ℝ) := by
    simp [G, trace, diag, gram_apply, hv]
  have hentry (i j : n) : G i j * G j i =
      (if j = i then 1 - α ^ 2 else 0) + α ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp [G, gram_apply, hv]
    · have he := congrArg (fun x : ℝ => x ^ 2) (hpair i j hij)
      rw [sq_abs] at he
      simp only [G, gram_apply, Ne.symm hij, ite_false, zero_add]
      calc
        ⟪v i, v j⟫_ℝ * ⟪v j, v i⟫_ℝ = ⟪v i, v j⟫_ℝ ^ 2 := by
          have hc : ⟪v j, v i⟫_ℝ = ⟪v i, v j⟫_ℝ := real_inner_comm _ _
          rw [hc, pow_two]
        _ = α ^ 2 := he
  have ht2 : (G ^ 2).trace = (Fintype.card n : ℝ) *
      (1 - α ^ 2 + Fintype.card n * α ^ 2) := by
    simp [trace, diag, pow_two, mul_apply, hentry, Finset.sum_add_distrib]
    ring
  -- Step `bound-rho`: Gram rank is at most the ambient dimension.
  have hr : G.rank ≤ Module.finrank ℝ E := by
    rw [rank_gram_eq_finrank_span]
    exact Submodule.finrank_le _
  have hnonneg : 0 ≤ (G ^ 2).trace := by
    rw [hG.trace_pow_eq_sum]
    positivity
  have hbound := hG.trace_sq_le_rank_mul_trace_sq
  have hh : (Fintype.card n : ℝ) ^ 2 ≤ Module.finrank ℝ E *
      ((Fintype.card n : ℝ) * (1 - α ^ 2 + Fintype.card n * α ^ 2)) := by
    have hr' : (G.rank : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hr
    have hh := hbound.trans (mul_le_mul_of_nonneg_right hr' hnonneg)
    simpa only [ht, ht2] using hh
  have hd : 0 < 1 - (Module.finrank ℝ E : ℝ) * α ^ 2 := by linarith
  -- Steps `bound-zero-n`, `bound-positive-n`: handle the empty family before division.
  by_cases hn : Fintype.card n = 0
  · rw [hn, Nat.cast_zero]
    have ha : 0 ≤ 1 - α ^ 2 := by nlinarith
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hd.le
  · have hn' : (0 : ℝ) < Fintype.card n := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply (le_div_iff₀ hd).mpr
    -- Step `bound-inequality`: cancel the positive number of vectors.
    have hi : (Fintype.card n : ℝ) *
        ((Fintype.card n : ℝ) * (1 - Module.finrank ℝ E * α ^ 2)) ≤
          (Fintype.card n : ℝ) * (Module.finrank ℝ E * (1 - α ^ 2)) := by
      nlinarith [hh]
    exact (mul_le_mul_iff_right₀ hn').mp hi

end Matrix
