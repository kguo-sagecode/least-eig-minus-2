/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Similarity

/-!
# Graph forms of the algebraic certificates

The direct graph interfaces for the annihilator/moment certificates used by C13
and C15, and for the intertwining certificate. The Boolean graph interfaces are
already in `Computations/SpectrumChecker.lean` and `Computations/SimilarityChecker.lean`.
These lemmas do not assert that any particular concrete certificate has been checked.
The involution argument, that Q² = I and QAQ = B give equal characteristic polynomials, is
stated here over ℝ and for graphs.
-/

open Matrix Polynomial

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Theorem 9.2 of the spectral toolkit: an annihilator and the first m moments certify the graph
spectrum. -/
theorem spectrumMultiset_eq_of_annihilatingPolynomial_trace {m : ℕ}
    (θ : Fin m → ℝ) (hθ : Function.Injective θ) (μ : Fin m → ℕ)
    (hp : aeval (G.adjMatrix ℝ) (∏ i, (X - C (θ i))) = 0)
    (ht : ∀ j : Fin m, ((G.adjMatrix ℝ) ^ j.val).trace =
      ∑ i, (μ i : ℝ) * θ i ^ j.val) :
    G.spectrumMultiset = ∑ i, Multiset.replicate (μ i) (θ i) := by
  -- Steps `cert-vandermonde`, `cert-list`: use the symmetric adjacency matrix.
  have hcert := (G.isHermitian_adjMatrix ℝ).spectrumMultiset_eq_of_annihilatingPolynomial_trace
    θ hθ μ hp ht
  exact hcert

/-- Corollary 9.3 of the spectral toolkit: common annihilating support and equal moments certify
cospectrality. -/
theorem cospectral_of_annihilatingPolynomial_trace (H : SimpleGraph W)
    [DecidableRel H.Adj] {m : ℕ} (θ : Fin m → ℝ) (hθ : Function.Injective θ)
    (hGp : aeval (G.adjMatrix ℝ) (∏ i, (X - C (θ i))) = 0)
    (hHp : aeval (H.adjMatrix ℝ) (∏ i, (X - C (θ i))) = 0)
    (ht : ∀ j : Fin m, ((G.adjMatrix ℝ) ^ j.val).trace =
      ((H.adjMatrix ℝ) ^ j.val).trace) : G.Cospectral H := by
  -- Steps `pair-Amoments`, `pair-Alist`, `pair-charpoly`: moments determine all root counts.
  have hcert := (G.isHermitian_adjMatrix ℝ).charpoly_eq_of_annihilatingPolynomial_trace
    (H.isHermitian_adjMatrix ℝ) θ hθ hGp hHp ht
  exact hcert

/-- Theorem 9.4 of the spectral toolkit: an invertible real intertwiner certifies graph
cospectrality. -/
theorem cospectral_of_intertwiner (H : SimpleGraph V) [DecidableRel H.Adj]
    {Q : Matrix V V ℝ} (hQ : Q.det ≠ 0)
    (h : Q * G.adjMatrix ℝ = H.adjMatrix ℝ * Q) : G.Cospectral H := by
  -- Steps `similarity-det`, `similarity-graphs`: conjugate the adjacency matrices.
  have hcert := Matrix.charpoly_eq_of_invertible_intertwiner hQ h
  exact hcert

/-- Theorem 9.4 of the spectral toolkit: a scaled inverse avoids computing an intertwiner's
determinant. -/
theorem cospectral_of_scaled_inverse_intertwiner (H : SimpleGraph V) [DecidableRel H.Adj]
    {Q R : Matrix V V ℝ} {d : ℝ} (hd : d ≠ 0)
    (h : Q * G.adjMatrix ℝ = H.adjMatrix ℝ * Q)
    (hQR : Q * R = d • 1) (hRQ : R * Q = d • 1) : G.Cospectral H := by
  -- Step `similarity-castQ`: the scaled matrix supplies both inverses, here directly over ℝ.
  have hcert := Matrix.charpoly_eq_of_scaled_inverse_intertwiner hd h hQR hRQ
  exact hcert

/-- Theorem 9.4 of the spectral toolkit, the involution variant: Q² = I and QAQ = B certify
cospectrality. -/
theorem cospectral_of_involution_conj (H : SimpleGraph V) [DecidableRel H.Adj]
    {Q : Matrix V V ℝ} (hQ : Q * Q = 1)
    (hconj : Q * G.adjMatrix ℝ * Q = H.adjMatrix ℝ) : G.Cospectral H := by
  -- Step `similarity-Qinverse`: Q is its own two-sided inverse.
  let U : (Matrix V V ℝ)ˣ := ⟨Q, Q, hQ, hQ⟩
  -- Step `similarity-Qconj`: invariance of the characteristic polynomial under conjugation.
  have he := Matrix.charpoly_units_conj U (G.adjMatrix ℝ)
  rw [← Matrix.coe_units_inv] at he
  change (Q * G.adjMatrix ℝ * Q).charpoly = (G.adjMatrix ℝ).charpoly at he
  rw [hconj] at he
  exact he.symm

end SimpleGraph
