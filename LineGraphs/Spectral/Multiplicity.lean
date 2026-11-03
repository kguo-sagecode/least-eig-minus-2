/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Basic

/-!
# Coordinates, roots and multiplicity

Theorem 2.2 and Lemma 2.4 of the spectral toolkit
(`cgss/proofs/spectraltools/spectraltools-lamport.tex`). The eigenspace is
`Module.End.eigenspace (toLin' A) μ`, in the function coordinates `n → ℝ`; step `mul-bridge`
identifies it with the Euclidean eigenspace of `A.toEuclideanLin`, where Mathlib's count of the
sorted eigenvalues lives.
-/

open Polynomial Module

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Theorem 2.2 of the spectral toolkit, step `mul-anybasis`: any orthonormal eigenbasis, on any
finite index type, lists the root multiset. The proof identifies the characteristic polynomial
with that of the diagonal matrix in this eigenbasis, then takes its roots. -/
theorem spectrumMultiset_eq_of_orthonormal_eigenbasis {I : Type*} [Fintype I]
    {A : Matrix n n ℝ} (u : OrthonormalBasis I ℝ (EuclideanSpace ℝ n)) (μ : I → ℝ)
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) :
    A.spectrumMultiset = Finset.univ.val.map μ := by
  classical
  -- Let `P` have columns `u j`.
  let P : Matrix n I ℝ := Matrix.of fun x j => u j x
  -- Step `mul-any-orth`: `PᵀP = I` and `|I| = n`.
  have hPT : Pᵀ * P = 1 := by
    ext j k
    have := orthonormal_iff_ite.mp u.orthonormal j k
    simpa only [P, mul_apply, transpose_apply, of_apply, one_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, mul_comm] using this
  have hcard : Fintype.card I = Fintype.card n := by
    have := Module.finrank_eq_card_basis u.toBasis
    simpa using this.symm
  -- Step `mul-any-diag`: `A = P D Pᵀ`.
  have hA : A = P * (diagonal μ * Pᵀ) := by
    have hPP : P * Pᵀ = 1 := by
      ext x y
      have h1 := congrArg (fun v : EuclideanSpace ℝ n => v x)
        (u.sum_repr' (EuclideanSpace.single y 1))
      simp only [EuclideanSpace.inner_single_right, one_mul] at h1
      simpa only [P, mul_apply, of_apply, transpose_apply, one_apply, eq_comm, conj_trivial,
        WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
        PiLp.single_apply] using h1
    have hAP : A * P = P * diagonal μ := by
      ext x j
      rw [Matrix.mul_diagonal]
      have := congrFun (h j) x
      simpa only [P, mul_apply, of_apply, mul_comm, mulVec, dotProduct, Pi.smul_apply,
        smul_eq_mul] using this
    rw [← Matrix.mul_assoc, ← hAP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  -- Step `mul-any-charpoly`: `χ_A = ∏ j, (t - μ j)`.
  have hchar : A.charpoly = ∏ j, (X - C (μ j)) := by
    have key := Matrix.charpoly_mul_comm' P (diagonal μ * Pᵀ)
    rw [← hA, Matrix.mul_assoc, hPT, Matrix.mul_one, hcard] at key
    rw [← charpoly_diagonal]
    exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) key
  -- Step `mul-any-roots`: `Spec(A) = {{μ j}}`.
  have hroots : A.spectrumMultiset = Finset.univ.val.map μ := by
    unfold spectrumMultiset
    rw [hchar, Finset.prod_eq_multiset_prod]
    have hm : (Finset.univ.val.map fun j => X - C (μ j)) =
        (Finset.univ.val.map μ).map fun a => X - C a := by
      rw [Multiset.map_map]; rfl
    rw [hm, Polynomial.roots_multiset_prod_X_sub_C]
  exact hroots

/-- Theorem 2.2 of the spectral toolkit, step `mul-rootmult`: the multiplicity is Mathlib's root
multiplicity. No symmetry is needed. -/
theorem eigenvalueMultiplicity_eq_rootMultiplicity (A : Matrix n n ℝ) (μ : ℝ) :
    A.eigenvalueMultiplicity μ = A.charpoly.rootMultiplicity μ :=
  Polynomial.count_roots _

namespace IsHermitian

variable {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- Theorem 2.2 of the spectral toolkit, step `mul-sorted`: the eigenvector basis of Mathlib
reindexed by `Fin n`, so that its eigenvalues are the decreasing list `hA.eigenvalues₀`. -/
noncomputable def sortedEigenvectorBasis :
    OrthonormalBasis (Fin (Fintype.card n)) ℝ (EuclideanSpace ℝ n) :=
  -- Step `mul-reindex`.
  hA.eigenvectorBasis.reindex (Fintype.equivOfCardEq (Fintype.card_fin _)).symm

/-- Theorem 2.2 of the spectral toolkit, step `mul-sorted-equation`. -/
theorem mulVec_sortedEigenvectorBasis (i : Fin (Fintype.card n)) :
    A *ᵥ ⇑(hA.sortedEigenvectorBasis i) = hA.eigenvalues₀ i • ⇑(hA.sortedEigenvectorBasis i) := by
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  simpa only [sortedEigenvectorBasis, OrthonormalBasis.reindex_apply, Equiv.symm_symm,
    Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
    hA.mulVec_eigenvectorBasis (e i)

/-- Theorem 2.2 of the spectral toolkit, step `mul-sorted-roots`: the decreasing list
`hA.eigenvalues₀` lists the spectrum. -/
theorem spectrumMultiset_eq_eigenvalues₀ :
    A.spectrumMultiset = Finset.univ.val.map hA.eigenvalues₀ :=
  spectrumMultiset_eq_of_orthonormal_eigenbasis hA.sortedEigenvectorBasis hA.eigenvalues₀
    hA.mulVec_sortedEigenvectorBasis

include hA in
/-- Theorem 2.2 of the spectral toolkit, step `mul-card`: `|Spec(A)| = n`. -/
theorem card_spectrumMultiset : Multiset.card A.spectrumMultiset = Fintype.card n := by
  rw [hA.spectrumMultiset_eq_eigenvalues]
  simp

include hA in
/-- Theorem 2.2 of the spectral toolkit, step `mul-space`: the multiplicity is the dimension of
the eigenspace `ker (A - μ I)`, in the function coordinates. -/
theorem eigenvalueMultiplicity_eq_finrank (μ : ℝ) :
    A.eigenvalueMultiplicity μ = finrank ℝ (Module.End.eigenspace (toLin' A) μ) := by
  classical
  have hT : A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  -- Step `mul-count-reindex`: the count of `μ` is the number of sorted indices with
  -- eigenvalue `μ`.
  have hcount : A.eigenvalueMultiplicity μ =
      (Finset.univ.filter fun i => hA.eigenvalues₀ i = μ).card := by
    have h := hA.spectrumMultiset_eq_eigenvalues₀
    unfold spectrumMultiset at h
    rw [eigenvalueMultiplicity, h, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  -- Step `mul-filter`: this number is the dimension of the Euclidean eigenspace.
  have hfilter : (Finset.univ.filter fun i => hA.eigenvalues₀ i = μ).card =
      finrank ℝ (Module.End.eigenspace A.toEuclideanLin μ) :=
    hT.card_filter_eigenvalues_eq finrank_euclideanSpace μ
  -- Step `mul-bridge`: the two coordinate conventions give eigenspaces of equal dimension.
  have hbridge : finrank ℝ (Module.End.eigenspace A.toEuclideanLin μ) =
      finrank ℝ (Module.End.eigenspace (toLin' A) μ) := by
    let e : EuclideanSpace ℝ n ≃ₗ[ℝ] (n → ℝ) := WithLp.linearEquiv 2 ℝ (n → ℝ)
    -- Steps `mul-map`, `mul-intertwine`, `mul-restrict`: `e` maps one eigenspace onto the
    -- other.
    have hmap : (Module.End.eigenspace A.toEuclideanLin μ).map (e : _ →ₗ[ℝ] _) =
        Module.End.eigenspace (toLin' A) μ := by
      ext x
      simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, toLin'_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have := congrArg WithLp.ofLp hy
        simpa [e, toLpLin_apply] using this
      · intro hx
        refine ⟨WithLp.toLp 2 x, ?_, by simp [e]⟩
        simp [toLpLin_apply, hx]
    rw [← hmap, LinearEquiv.finrank_map_eq]
  rw [hcount, hfilter, hbridge]

include hA in
/-- Theorem 2.2 of the spectral toolkit, step `mul-nonzero`: `μ ∈ Spec(A)` iff there is a nonzero
`μ`-eigenvector. -/
theorem mem_spectrumMultiset_iff {μ : ℝ} :
    μ ∈ A.spectrumMultiset ↔ ∃ x : n → ℝ, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  have h1 : μ ∈ A.spectrumMultiset ↔ 0 < A.eigenvalueMultiplicity μ :=
    Multiset.count_pos.symm
  rw [h1, hA.eigenvalueMultiplicity_eq_finrank, Nat.pos_iff_ne_zero, Ne,
    Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff]
  simp only [Module.End.mem_eigenspace_iff, toLin'_apply]
  exact ⟨fun ⟨x, hx, h0⟩ => ⟨x, h0, hx⟩, fun ⟨x, h0, hx⟩ => ⟨x, hx, h0⟩⟩

include hA in
/-- Theorem 2.2 of the spectral toolkit, step `mul-spectrum`: membership agrees with Mathlib's
set-valued spectrum. -/
theorem mem_spectrumMultiset_iff_mem_spectrum {μ : ℝ} :
    μ ∈ A.spectrumMultiset ↔ μ ∈ spectrum ℝ A := by
  rw [hA.spectrum_real_eq_range_eigenvalues, hA.spectrumMultiset_eq_eigenvalues]
  simp

/-- Every entry `hA.eigenvalues i` lies in the spectrum (step `mul-list` of Theorem 2.2). -/
theorem eigenvalues_mem_spectrumMultiset (i : n) : hA.eigenvalues i ∈ A.spectrumMultiset := by
  rw [hA.spectrumMultiset_eq_eigenvalues]
  exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val _, rfl⟩

/-! ### Lemma 2.4: the extremes -/

variable [Nonempty n]

/-- Lemma 2.4 of the spectral toolkit: `λmax` belongs to the spectrum. -/
theorem largestEigenvalue_mem_spectrumMultiset : hA.largestEigenvalue ∈ A.spectrumMultiset := by
  -- Step `ext-roots`.
  have hroots := hA.spectrumMultiset_eq_eigenvalues₀
  -- Step `ext-members`.
  rw [hroots]
  exact Multiset.mem_map.mpr ⟨_, Finset.mem_univ_val _, rfl⟩

/-- Lemma 2.4 of the spectral toolkit: `λmin` belongs to the spectrum. -/
theorem leastEigenvalue_mem_spectrumMultiset : hA.leastEigenvalue ∈ A.spectrumMultiset := by
  -- Step `ext-roots`.
  have hroots := hA.spectrumMultiset_eq_eigenvalues₀
  -- Step `ext-members`.
  rw [hroots]
  exact Multiset.mem_map.mpr ⟨_, Finset.mem_univ_val _, rfl⟩

/-- Lemma 2.4 of the spectral toolkit, step `ext-upper`: every eigenvalue is at most `λmax`. -/
theorem le_largestEigenvalue_of_mem {μ : ℝ} (hμ : μ ∈ A.spectrumMultiset) :
    μ ≤ hA.largestEigenvalue := by
  -- Step `ext-roots`.
  rw [hA.spectrumMultiset_eq_eigenvalues₀] at hμ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hμ
  exact hA.eigenvalues₀_antitone (Fin.zero_le i)

/-- Lemma 2.4 of the spectral toolkit, step `ext-lower`: every eigenvalue is at least `λmin`. -/
theorem leastEigenvalue_le_of_mem {μ : ℝ} (hμ : μ ∈ A.spectrumMultiset) :
    hA.leastEigenvalue ≤ μ := by
  -- Step `ext-roots`.
  rw [hA.spectrumMultiset_eq_eigenvalues₀] at hμ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hμ
  apply hA.eigenvalues₀_antitone
  change i.val ≤ Fintype.card n - 1
  omega

/-- Lemma 2.4 of the spectral toolkit applied to the unsorted eigenvalues. -/
theorem eigenvalues_le_largestEigenvalue (i : n) : hA.eigenvalues i ≤ hA.largestEigenvalue :=
  hA.le_largestEigenvalue_of_mem (hA.eigenvalues_mem_spectrumMultiset i)

/-- Lemma 2.4 of the spectral toolkit applied to the unsorted eigenvalues. -/
theorem leastEigenvalue_le_eigenvalues (i : n) : hA.leastEigenvalue ≤ hA.eigenvalues i :=
  hA.leastEigenvalue_le_of_mem (hA.eigenvalues_mem_spectrumMultiset i)

end IsHermitian

end Matrix
