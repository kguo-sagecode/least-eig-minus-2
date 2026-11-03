/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Polynomial
import LineGraphs.Spectral.TraceRank

/-!
# A finite decomposition into eigenspaces

The four spaces in steps `s5exvalues`–`s5exspecH` of Example 5.13 (`ex:5.13`)
of [CGSS] are conveniently represented by their orthogonal projections.
This interface identifies explicit projections with the spectral toolkit's
projectors, so that their traces give both dimensions and multiplicities.
-/

open scoped BigOperators

namespace Matrix.IsHermitian

variable {n I : Type*} [Fintype n] [DecidableEq n] [Fintype I]
  {A : Matrix n n ℝ}

/-- The decomposition argument in `s5exspecH`, Example 5.13 of [CGSS]: symmetric
matrices summing to the identity and taking values in distinct eigenspaces are
the corresponding spectral projections. Idempotence need not be assumed. -/
theorem eq_spectralIdempotent_of_eigenprojections (hA : A.IsHermitian)
    (E : I → Matrix n n ℝ) (θ : I → ℝ) (hθ : Function.Injective θ)
    (hE : ∀ i, (E i).IsHermitian) (hs : ∑ i, E i = 1)
    (hAE : ∀ i, A * E i = θ i • E i) (i : I) : E i = hA.spectralIdempotent (θ i) := by
  have hEA (j : I) : E j * A = θ j • E j := by
    have he := congrArg Matrix.transpose (hAE j)
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul,
      (Matrix.isHermitian_iff_isSymm.mp hA).eq,
      (Matrix.isHermitian_iff_isSymm.mp (hE j)).eq] using he
  have hz {μ : ℝ} {x : n → ℝ} (hx : A *ᵥ x = μ • x)
      (j : I) (hne : μ ≠ θ j) : E j *ᵥ x = 0 := by
    have he := congrArg (fun M : Matrix n n ℝ ↦ M *ᵥ x) (hEA j)
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, Matrix.smul_mulVec] at he
    have hh : (μ - θ j) • (E j *ᵥ x) = 0 := by rw [sub_smul, he, sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
  apply hA.eq_spectralIdempotent_of_mulVec_eigenvectorBasis
  intro a
  have hx := hA.mulVec_eigenvectorBasis a
  by_cases he : hA.eigenvalues a = θ i
  · rw [ite_eq_left he, one_smul]
    have hv := congrArg (fun M : Matrix n n ℝ ↦ M *ᵥ ⇑(hA.eigenvectorBasis a)) hs
    rw [Matrix.sum_mulVec, Matrix.one_mulVec] at hv
    rw [Finset.sum_eq_single i] at hv
    · exact hv
    · intro j _ hji
      exact hz hx j (by rw [he]; exact fun h ↦ hji (hθ h).symm)
    · simp
  · rw [ite_eq_right he, zero_smul]
    exact hz hx i he

/-- Trace equals eigenspace dimension in the decomposition used in `s5exdims`,
Example 5.13 of [CGSS]. -/
theorem finrank_eigenspace_of_eigenprojections (hA : A.IsHermitian)
    (E : I → Matrix n n ℝ) (θ : I → ℝ) (hθ : Function.Injective θ)
    (hE : ∀ i, (E i).IsHermitian) (hs : ∑ i, E i = 1)
    (hAE : ∀ i, A * E i = θ i • E i) (i : I) :
    (Module.finrank ℝ (Module.End.eigenspace A.toLin' (θ i)) : ℝ) = (E i).trace := by
  rw [hA.eq_spectralIdempotent_of_eigenprojections E θ hθ hE hs hAE,
    hA.trace_spectralIdempotent, hA.eigenvalueMultiplicity_eq_finrank]

/-- The multiset conclusion of `s5exspecH`, Example 5.13 of [CGSS], from the
dimensions of explicit symmetric eigenspace projections. -/
theorem spectrumMultiset_eq_of_eigenprojections (hA : A.IsHermitian)
    (E : I → Matrix n n ℝ) (θ : I → ℝ) (hθ : Function.Injective θ)
    (hE : ∀ i, (E i).IsHermitian) (hs : ∑ i, E i = 1)
    (hAE : ∀ i, A * E i = θ i • E i) (m : I → ℕ)
    (ht : ∀ i, (E i).trace = (m i : ℝ)) :
    A.spectrumMultiset = ∑ i, Multiset.replicate (m i) (θ i) := by
  classical
  have hm (i : I) : A.eigenvalueMultiplicity (θ i) = m i := by
    have he := ht i
    rw [hA.eq_spectralIdempotent_of_eigenprojections E θ hθ hE hs hAE,
      hA.trace_spectralIdempotent] at he
    exact_mod_cast he
  have htotal : (∑ i, m i) = Fintype.card n := by
    have he := congrArg Matrix.trace hs
    simp only [Matrix.trace_sum, ht, Matrix.trace_one] at he
    exact_mod_cast he
  symm
  apply Multiset.eq_of_le_of_card_le
  · apply Multiset.le_iff_count.mpr
    intro μ
    by_cases hmem : ∃ i, θ i = μ
    · obtain ⟨i, rfl⟩ := hmem
      simp only [Multiset.count_sum', Multiset.count_replicate]
      have he : (fun j ↦ if θ j = θ i then m j else 0) =
          (fun j ↦ if j = i then m j else 0) := by
        ext j
        simp only [hθ.eq_iff]
      rw [he, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]
      exact le_of_eq (hm i).symm
    · have hn (i : I) : θ i ≠ μ := fun hi ↦ hmem ⟨i, hi⟩
      simp [Multiset.count_sum', Multiset.count_replicate, hn]
  · simp [Multiset.card_sum, Multiset.card_replicate, htotal,
      hA.card_spectrumMultiset]

end Matrix.IsHermitian
