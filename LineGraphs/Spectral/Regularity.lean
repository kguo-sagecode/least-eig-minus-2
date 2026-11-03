/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Regular
import LineGraphs.Spectral.Rayleigh

/-!
# Regularity detected by the spectrum

Theorem 5.4 (SP2; Lemma 5.2 of [CGSS]) of the spectral toolkit.
In the second-moment argument, Mathlib's diagonal identity supplies the entry calculation.
-/

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
  [DecidableRel X.Adj]

/-- Theorem 5.1 of the spectral toolkit, the second moment is the sum of the vertex degrees. -/
theorem sum_sq_spectrumMultiset_eq_sum_degrees :
    (X.spectrumMultiset.map (fun μ => μ ^ 2)).sum = ∑ v, (X.degree v : ℝ) := by
  -- Steps `walk-closed`, `walk-length2`: a closed walk of length two is an incident edge.
  have htrace := (X.isHermitian_adjMatrix ℝ).trace_pow_eq_sum_spectrumMultiset 2
  rw [spectrumMultiset, ← htrace, pow_two]
  exact Finset.sum_congr rfl fun v _ => X.adjMatrix_mul_self_apply_self v

/-- Theorem 5.1 of the spectral toolkit: the second adjacency moment is twice the number of edges.
-/
theorem sum_sq_spectrumMultiset_eq_twice_card_edges :
    (X.spectrumMultiset.map (fun μ => μ ^ 2)).sum = 2 * (X.edgeFinset.card : ℝ) := by
  -- Step `walk-length2`: the degree sum counts both ends of every edge.
  have hdegrees := X.sum_degrees_eq_twice_card_edges
  rw [X.sum_sq_spectrumMultiset_eq_sum_degrees]
  exact_mod_cast hdegrees

/-- Theorem 5.4 of the spectral toolkit (SP2; Lemma 5.2 of [CGSS]): on a nonempty vertex set, the
second spectral moment is `n λmax` exactly when the graph is regular. -/
theorem isRegular_iff_sum_sq_eigenvalues [Nonempty V] :
    (∃ k, X.IsRegularOfDegree k) ↔
      (X.spectrumMultiset.map (fun μ => μ ^ 2)).sum =
        (Fintype.card V : ℝ) * X.largestEigenvalue := by
  let j : V → ℝ := fun _ => 1
  have hj : j ≠ 0 := by simp [j, funext_iff]
  -- Step `sp2-forms`: the constant vector has squared norm n and form equal to the degree sum.
  have hnorm : j ⬝ᵥ j = (Fintype.card V : ℝ) := by simp [j, dotProduct]
  have hform : j ⬝ᵥ (X.adjMatrix ℝ *ᵥ j) =
      (X.spectrumMultiset.map (fun μ => μ ^ 2)).sum := by
    rw [X.sum_sq_spectrumMultiset_eq_sum_degrees]
    simp [j, dotProduct]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by positivity
  -- Step `sp2-equality`: Rayleigh equality at the constant vector is the top eigenvector equation.
  have hequality : (X.spectrumMultiset.map (fun μ => μ ^ 2)).sum =
      (Fintype.card V : ℝ) * X.largestEigenvalue ↔
      X.adjMatrix ℝ *ᵥ j = X.largestEigenvalue • j := by
    simp only [largestEigenvalue]
    rw [← (X.isHermitian_adjMatrix ℝ).rayleigh_eq_largestEigenvalue_iff hj,
      hform, hnorm, div_eq_iff hn]
    simp only [mul_comm]
  constructor
  · rintro ⟨k, hk⟩
    -- Step `sp2-reverse`: regularity identifies the constant eigenvalue with the largest one.
    have heigen : X.adjMatrix ℝ *ᵥ j = X.largestEigenvalue • j := by
      rw [hk.largestEigenvalue_eq]
      ext v
      simpa [j] using (X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hk (a := 1) (v := v))
    exact hequality.mpr heigen
  · intro hs
    have heigen := hequality.mp hs
    obtain ⟨w⟩ := ‹Nonempty V›
    -- Step `sp2-degrees`: every row sum equals the degree of the chosen vertex.
    have hdegree (v : V) : (X.degree v : ℝ) = X.largestEigenvalue := by
      simpa [j] using congrFun heigen v
    refine ⟨X.degree w, fun v => ?_⟩
    exact_mod_cast (hdegree v).trans (hdegree w).symm

end SimpleGraph
