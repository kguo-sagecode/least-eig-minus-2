/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Multiplicity
import LineGraphs.Spectral.Rayleigh
import Mathlib.Analysis.Matrix.PosDef

/-!
# Polynomial calculus and spectral idempotents

Theorem 3.1 of the spectral toolkit. Spectral idempotents are defined for every
real number, with the zero matrix at numbers outside the spectrum. All statements
include the empty matrix.
-/

open Polynomial Module

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
  (hA : A.IsHermitian)

include hA

private theorem mulVec_conj_diagonal (d : n → ℝ) (i : n) :
    Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary (diagonal d) *ᵥ
      ⇑(hA.eigenvectorBasis i) = d i • ⇑(hA.eigenvectorBasis i) := by
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec,
    hA.star_eigenvectorUnitary_mulVec, diagonal_mulVec_single, mul_one,
    mulVec_single, hA.eigenvectorUnitary_col_eq, op_smul_eq_smul]

/-- Theorem 3.1 of the spectral toolkit, step `calc-conj`: polynomial evaluation acts diagonally
in the
orthonormal eigenbasis. -/
theorem aeval_eq_conj_diagonal (p : ℝ[X]) :
    aeval A p = Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
      (diagonal fun i => p.eval (hA.eigenvalues i)) := by
  -- Steps `calc-powers`, `calc-eval`: evaluation commutes with conjugation and the diagonal map.
  have hd : aeval (diagonal hA.eigenvalues) p =
      diagonal (fun i => p.eval (hA.eigenvalues i)) := by
    change aeval (diagonalAlgHom (n := n) (α := ℝ) ℝ hA.eigenvalues) p = _
    rw [aeval_algHom_apply]
    change diagonal (aeval hA.eigenvalues p) = _
    congr 1
    ext i
    simp
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
    aeval_algHom_apply, hd]

/-- A real polynomial in a real symmetric matrix is again symmetric. -/
theorem isHermitian_aeval (p : ℝ[X]) : (aeval A p).IsHermitian := by
  rw [hA.aeval_eq_conj_diagonal]
  have hd : (diagonal (fun i => p.eval (hA.eigenvalues i))).IsHermitian := by
    exact isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _
  exact (hd.isSelfAdjoint.map
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary)).isHermitian

/-- Theorem 3.1 of the spectral toolkit, step `calc-eval`: a polynomial sends each eigenvalue to
its evaluation. -/
theorem mulVec_aeval_eigenvectorBasis (p : ℝ[X]) (i : n) :
    aeval A p *ᵥ ⇑(hA.eigenvectorBasis i) =
      p.eval (hA.eigenvalues i) • ⇑(hA.eigenvectorBasis i) := by
  rw [hA.aeval_eq_conj_diagonal]
  exact hA.mulVec_conj_diagonal _ i

/-- Theorem 3.1 of the spectral toolkit, step `calc-rootlist`: polynomial spectral mapping,
counting all
multiplicities and merging colliding values. -/
theorem spectrumMultiset_aeval (p : ℝ[X]) :
    (aeval A p).spectrumMultiset = A.spectrumMultiset.map p.eval := by
  -- Step `calc-rootlist`: the old orthonormal basis is an eigenbasis for p(A).
  have hspec := spectrumMultiset_eq_of_orthonormal_eigenbasis hA.eigenvectorBasis
    (fun i => p.eval (hA.eigenvalues i)) (hA.mulVec_aeval_eigenvectorBasis p)
  rw [hA.spectrumMultiset_eq_eigenvalues, Multiset.map_map]
  exact hspec

/-- Theorem 3.1 of the spectral toolkit, step `calc-zero`: a polynomial annihilates A exactly when
it
vanishes on every member of the spectrum. -/
theorem aeval_eq_zero_iff (p : ℝ[X]) :
    aeval A p = 0 ↔ ∀ μ ∈ A.spectrumMultiset, p.eval μ = 0 := by
  -- Step `calc-conj`: diagonalization reduces zero evaluation to zero diagonal entries.
  have heval : aeval A p = 0 ↔ ∀ i, p.eval (hA.eigenvalues i) = 0 := by
    constructor
    · intro hp i
      exact hA.eval_eigenvalue_eq_zero hp i
    · intro hd
      have hz : diagonal (fun i => p.eval (hA.eigenvalues i)) = 0 := by
        ext i j
        simp [diagonal, hd]
      rw [hA.aeval_eq_conj_diagonal, hz, map_zero]
  -- Step `calc-zero`: the eigenvalue list enumerates the entire spectrum.
  rw [heval, hA.spectrumMultiset_eq_eigenvalues]
  simp

/-- Theorem 3.1 of the spectral toolkit, step `calc-proj`: the orthogonal projector onto the
μ-eigenspace,
defined by selecting the corresponding diagonal coordinates. -/
noncomputable def spectralIdempotent (μ : ℝ) : Matrix n n ℝ :=
  Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
    (diagonal fun i => if hA.eigenvalues i = μ then 1 else 0)

/-- The spectral idempotents are symmetric. -/
theorem isHermitian_spectralIdempotent (μ : ℝ) : (hA.spectralIdempotent μ).IsHermitian := by
  have hd : (diagonal fun i => if hA.eigenvalues i = μ then (1 : ℝ) else 0).IsHermitian :=
    isHermitian_diagonal_iff.mpr fun _ => IsSelfAdjoint.all _
  exact (hd.isSelfAdjoint.map
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary)).isHermitian

/-- Theorem 3.1 of the spectral toolkit, step `calc-select`: the projector selects exactly the basis
directions with eigenvalue μ. -/
theorem spectralIdempotent_mulVec_eigenvectorBasis (μ : ℝ) (i : n) :
    hA.spectralIdempotent μ *ᵥ ⇑(hA.eigenvectorBasis i) =
      (if hA.eigenvalues i = μ then (1 : ℝ) else 0) • ⇑(hA.eigenvectorBasis i) :=
  hA.mulVec_conj_diagonal _ i

/-- Theorem 3.1 of the spectral toolkit, step `calc-select`: the projector is the identity on its
eigenspace
and zero on every other eigenspace. The zero vector is allowed. -/
theorem spectralIdempotent_mulVec_of_eigenvector (μ : ℝ) {θ : ℝ} {x : n → ℝ}
    (hx : A *ᵥ x = θ • x) :
    hA.spectralIdempotent μ *ᵥ x = (if θ = μ then (1 : ℝ) else 0) • x := by
  -- Step `calc-select`: only coordinates whose original eigenvalue is θ can survive.
  have hcoord := (mulVec_eq_smul_iff_of_orthonormal_eigenbasis hA.eigenvectorBasis
    hA.eigenvalues hA.mulVec_eigenvectorBasis x θ).mp hx
  apply (mulVec_eq_smul_iff_of_orthonormal_eigenbasis hA.eigenvectorBasis
    (fun i => if hA.eigenvalues i = μ then 1 else 0)
    (hA.spectralIdempotent_mulVec_eigenvectorBasis μ) x _).mpr
  intro i
  by_cases hi : hA.eigenvalues i = θ
  · rw [hi]
  · have hz : hA.eigenvectorBasis.repr (WithLp.toLp 2 x) i = 0 :=
      (mul_eq_mul_right_iff.mp (hcoord i)).resolve_left hi
    simp only [hz, mul_zero]

/-- Theorem 3.1 of the spectral toolkit, step `calc-product`: different projectors are orthogonal,
and
each projector is idempotent. -/
theorem spectralIdempotent_mul (μ ν : ℝ) :
    hA.spectralIdempotent μ * hA.spectralIdempotent ν =
      if μ = ν then hA.spectralIdempotent μ else 0 := by
  -- Step `calc-product`: multiply the two diagonal selector functions.
  have hd : (diagonal fun i => if hA.eigenvalues i = μ then (1 : ℝ) else 0) *
      (diagonal fun i => if hA.eigenvalues i = ν then (1 : ℝ) else 0) =
      if μ = ν then diagonal (fun i => if hA.eigenvalues i = μ then 1 else 0) else 0 := by
    rw [diagonal_mul_diagonal]
    by_cases h : μ = ν
    · subst ν
      rw [ite_eq_left rfl]
      congr 1
      ext i
      split_ifs <;> norm_num
    · rw [ite_eq_right h, ← diagonal_zero]
      congr 1
      ext i
      by_cases hi : hA.eigenvalues i = μ <;> by_cases hj : hA.eigenvalues i = ν
      · exact (h (hi.symm.trans hj)).elim
      · simp only [hi, h, ite_true, ite_false, mul_zero]
      · simp only [hj, Ne.symm h, ite_true, ite_false, zero_mul]
      · simp only [hi, hj, ite_false, zero_mul]
  unfold spectralIdempotent
  rw [← map_mul, hd]
  split_ifs <;> simp only [map_zero]

/-- Theorem 3.1 of the spectral toolkit, step `calc-equality`: every polynomial in A is the
weighted sum
of its spectral projectors. The sum is over the distinct eigenvalues. -/
theorem aeval_eq_sum_spectralIdempotent (p : ℝ[X]) :
    aeval A p = ∑ μ ∈ A.spectrumMultiset.toFinset, p.eval μ • hA.spectralIdempotent μ := by
  -- Step `calc-equality`: on each diagonal coordinate exactly one selector survives.
  have hd : diagonal (fun i => p.eval (hA.eigenvalues i)) =
      ∑ μ ∈ A.spectrumMultiset.toFinset,
        p.eval μ • diagonal (fun i => if hA.eigenvalues i = μ then (1 : ℝ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hi : hA.eigenvalues i ∈ A.spectrumMultiset.toFinset :=
        Multiset.mem_toFinset.mpr (hA.eigenvalues_mem_spectrumMultiset i)
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, diagonal_apply_eq,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hi, ite_true]
    · simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        diagonal_apply_ne _ hij, mul_zero, Finset.sum_const_zero]
  rw [hA.aeval_eq_conj_diagonal, hd, map_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [map_smul]
  rfl

/-- Theorem 3.1 of the spectral toolkit, step `calc-sum`: the distinct spectral projectors sum to
the identity. -/
theorem sum_spectralIdempotent :
    (∑ μ ∈ A.spectrumMultiset.toFinset, hA.spectralIdempotent μ) = 1 := by
  have h := hA.aeval_eq_sum_spectralIdempotent (1 : ℝ[X])
  simpa only [map_one, eval_one, one_smul] using h.symm

/-- Theorem 3.1 of the spectral toolkit, step `calc-weight`: the spectral decomposition of A. -/
theorem eq_sum_eigenvalue_smul_spectralIdempotent :
    A = ∑ μ ∈ A.spectrumMultiset.toFinset, μ • hA.spectralIdempotent μ := by
  have h := hA.aeval_eq_sum_spectralIdempotent (X : ℝ[X])
  simpa only [aeval_X, eval_X] using h

/-- Theorem 3.1 of the spectral toolkit, step `calc-trace`: the trace of a spectral projector is the
multiplicity of its eigenvalue. -/
theorem trace_spectralIdempotent (μ : ℝ) :
    (hA.spectralIdempotent μ).trace = (A.eigenvalueMultiplicity μ : ℝ) := by
  -- Step `calc-trace`: cyclic invariance cancels the orthogonal change of basis.
  have htrace : (hA.spectralIdempotent μ).trace =
      (diagonal fun i => if hA.eigenvalues i = μ then (1 : ℝ) else 0).trace := by
    unfold spectralIdempotent
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle]
    simp
  rw [htrace, trace_diagonal, hA.eigenvalueMultiplicity_eq_card]
  simp

/-- Theorem 3.1 of the spectral toolkit, step `calc-rank`: a spectral projector has rank equal to
the
multiplicity of its eigenvalue, including rank zero outside the spectrum. -/
theorem rank_spectralIdempotent (μ : ℝ) :
    (hA.spectralIdempotent μ).rank = A.eigenvalueMultiplicity μ := by
  -- Step `calc-rank`: conjugation preserves rank, and a diagonal selector has
  -- one nonzero entry for each occurrence of μ.
  have hrank : (hA.spectralIdempotent μ).rank =
      (diagonal fun i => if hA.eigenvalues i = μ then (1 : ℝ) else 0).rank := by
    unfold spectralIdempotent
    rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
    simp [-isUnit_iff_ne_zero, -Unitary.coe_star]
  rw [hrank, rank_diagonal, hA.eigenvalueMultiplicity_eq_card]
  simp [Fintype.card_subtype]

/-- Theorem 3.1 of the spectral toolkit, step `calc-collisions`: multiplicities add when polynomial
evaluation sends different eigenvalues to the same value. -/
theorem eigenvalueMultiplicity_aeval (p : ℝ[X]) (b : ℝ) :
    (aeval A p).eigenvalueMultiplicity b =
      ∑ μ ∈ A.spectrumMultiset.toFinset.filter (fun μ => p.eval μ = b),
        A.eigenvalueMultiplicity μ := by
  -- Step `calc-collisions`: partition the eigenbasis indices by their original eigenvalues.
  have hcount : (aeval A p).eigenvalueMultiplicity b =
      (Finset.univ.filter fun i => p.eval (hA.eigenvalues i) = b).card := by
    change Multiset.count b (aeval A p).spectrumMultiset = _
    rw [hA.spectrumMultiset_aeval,
      hA.spectrumMultiset_eq_eigenvalues, Multiset.map_map, Multiset.count_map]
    simp only [Function.comp_apply, Finset.card_def, Finset.filter_val]
    congr 2
    exact funext fun i => propext (eq_comm)
  rw [hcount]
  simp_rw [hA.eigenvalueMultiplicity_eq_card]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset]
  exact (and_iff_right (hA.eigenvalues_mem_spectrumMultiset i)).symm

/-- Theorem 3.1 of the spectral toolkit, steps `calc-denom`–`calc-productformula`: Lagrange
interpolation
expresses a spectral projector as a polynomial in A. Evaluating the polynomial
product is the unambiguous Lean form of the commuting matrix product. -/
theorem spectralIdempotent_eq_aeval (μ : ℝ) :
    hA.spectralIdempotent μ = aeval A
      (∏ ν ∈ A.spectrumMultiset.toFinset.erase μ,
        C ((μ - ν)⁻¹) * (X - C ν)) := by
  let p : ℝ[X] := ∏ ν ∈ A.spectrumMultiset.toFinset.erase μ,
    C ((μ - ν)⁻¹) * (X - C ν)
  -- Steps `calc-value1`, `calc-value0`: the interpolating polynomial is the selector
  -- on the eigenvalue list.
  have hp (i : n) : p.eval (hA.eigenvalues i) =
      if hA.eigenvalues i = μ then (1 : ℝ) else 0 := by
    by_cases hi : hA.eigenvalues i = μ
    · rw [ite_eq_left hi, hi]
      simp only [p, eval_prod, eval_mul, eval_C, eval_sub, eval_X]
      apply Finset.prod_eq_one
      intro ν hν
      have hne : μ - ν ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hν).1.symm
      exact inv_mul_cancel₀ hne
    · rw [ite_eq_right hi]
      simp only [p, eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr
        ⟨hi, Multiset.mem_toFinset.mpr (hA.eigenvalues_mem_spectrumMultiset i)⟩)
      simp
  -- Step `calc-productformula`: the diagonal actions agree.
  change hA.spectralIdempotent μ = aeval A p
  rw [hA.aeval_eq_conj_diagonal]
  simp only [hp, spectralIdempotent]

/-- Theorem 3.1 of the spectral toolkit, step `calc-unique`: the action on the orthonormal
eigenbasis
uniquely determines the spectral projector. Symmetry of the candidate is unnecessary. -/
theorem eq_spectralIdempotent_of_mulVec_eigenvectorBasis (μ : ℝ) {M : Matrix n n ℝ}
    (hM : ∀ i, M *ᵥ ⇑(hA.eigenvectorBasis i) =
      (if hA.eigenvalues i = μ then (1 : ℝ) else 0) • ⇑(hA.eigenvectorBasis i)) :
    M = hA.spectralIdempotent μ := by
  -- Step `calc-unique`: equality on a basis determines the entire linear map.
  have heq (i : n) : M *ᵥ ⇑(hA.eigenvectorBasis i) =
      hA.spectralIdempotent μ *ᵥ ⇑(hA.eigenvectorBasis i) :=
    (hM i).trans (hA.spectralIdempotent_mulVec_eigenvectorBasis μ i).symm
  apply Matrix.toEuclideanLin.injective
  apply hA.eigenvectorBasis.toBasis.ext
  intro i
  apply WithLp.ofLp_injective 2
  simpa only [toLpLin_apply, OrthonormalBasis.coe_toBasis, WithLp.ofLp_toLp] using heq i

end Matrix.IsHermitian
