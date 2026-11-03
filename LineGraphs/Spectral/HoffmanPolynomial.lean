/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Polynomial
import LineGraphs.Spectral.StrictMono

/-!
# Polynomials supported on the constant eigendirection

Theorem 7.10 of the spectral toolkit. Connectedness ensures that removing one
constant eigenvector removes the entire regular-degree eigenspace.
-/

open Matrix Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {X : SimpleGraph V}
  [DecidableRel X.Adj] {k : ℕ}

omit [DecidableEq V] in
private theorem allOnes_mulVec_of_regular_eigenvector (hk : X.IsRegularOfDegree k)
    (hc : X.Connected) {μ : ℝ} {x : V → ℝ} (hx : X.adjMatrix ℝ *ᵥ x = μ • x) :
    (of fun (_ : V) (_ : V) => (1 : ℝ)) *ᵥ x =
      if μ = (k : ℝ) then (Fintype.card V : ℝ) • x else 0 := by
  classical
  have : Nonempty V := hc.nonempty
  have hj : X.adjMatrix ℝ *ᵥ (fun _ => 1) = (k : ℝ) • (fun _ => 1) := by
    ext u
    simpa using X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) hk (a := 1) (v := u)
  by_cases hμ : μ = (k : ℝ)
  · rw [ite_eq_left hμ]
    -- Step `hoffman-simple`: the positive constant vector spans its eigenspace.
    have hnonneg (u v : V) : 0 ≤ X.adjMatrix ℝ u v := by
      simp only [adjMatrix_apply]
      split_ifs <;> norm_num
    have hs : ((X.adjMatrix ℝ).positiveSupportGraph (X.isHermitian_adjMatrix ℝ)).Connected := by
      rwa [positiveSupportGraph_adjMatrix]
    obtain ⟨c, rfl⟩ := (X.isHermitian_adjMatrix ℝ).eq_smul_of_pos_eigenvector
      hnonneg hs (fun _ => zero_lt_one) hj (hμ ▸ hx)
    -- Step `hoffman-constant`: J acts on a constant vector by the order.
    have haction : (of fun (_ : V) (_ : V) => (1 : ℝ)) *ᵥ (c • (fun _ => 1)) =
        (Fintype.card V : ℝ) • (c • (fun _ => 1)) := by
      ext u
      simp [mulVec, dotProduct, mul_comm]
    exact haction
  · rw [ite_eq_right hμ]
    -- Step `hoffman-other`: every other eigendirection has coordinate sum zero.
    have ho := (X.isHermitian_adjMatrix ℝ).dotProduct_eq_zero_of_eigenvalue_ne hj hx (Ne.symm hμ)
    have hsum : ∑ u, x u = 0 := by simpa [dotProduct] using ho
    ext u
    simpa [mulVec, dotProduct] using hsum

/-- The polynomial is a scalar multiple of J exactly when it vanishes on all
nonconstant eigendirections of a connected regular graph. -/
theorem IsRegularOfDegree.aeval_eq_smul_allOnes_iff_of_connected
    (hk : X.IsRegularOfDegree k) (hc : X.Connected) (p : ℝ[X]) :
    aeval (X.adjMatrix ℝ) p = (p.eval (k : ℝ) / Fintype.card V) • (of fun _ _ => 1) ↔
      ∀ μ ∈ X.spectrumMultiset, μ ≠ (k : ℝ) → p.eval μ = 0 := by
  classical
  have : Nonempty V := hc.nonempty
  let hA := X.isHermitian_adjMatrix ℝ
  have hn : (Fintype.card V : ℝ) ≠ 0 := by positivity
  have hJ (i : V) := allOnes_mulVec_of_regular_eigenvector hk hc (hA.mulVec_eigenvectorBasis i)
  constructor
  · intro heq μ hμ hne
    -- Step `hoffman-apply`: choose a basis eigenvector with this eigenvalue.
    have hi : ∃ i, hA.eigenvalues i = μ := by
      change μ ∈ (X.adjMatrix ℝ).spectrumMultiset at hμ
      rw [hA.spectrumMultiset_eq_eigenvalues] at hμ
      simpa using hμ
    obtain ⟨i, rfl⟩ := hi
    have hz := congrArg (fun M : Matrix V V ℝ => M *ᵥ ⇑(hA.eigenvectorBasis i)) heq
    rw [hA.mulVec_aeval_eigenvectorBasis, smul_mulVec, hJ, ite_eq_right hne, smul_zero] at hz
    -- Step `hoffman-cancel`: the basis vector is nonzero.
    have hv : (hA.eigenvectorBasis i).ofLp ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.mpr (hA.eigenvectorBasis.orthonormal.ne_zero i)
    exact (smul_eq_zero.mp hz).resolve_right hv
  · intro hp
    -- Steps `hoffman-constant`, `hoffman-other`: compare the two actions on the basis.
    have heig (i : V) : aeval (X.adjMatrix ℝ) p *ᵥ ⇑(hA.eigenvectorBasis i) =
        ((p.eval (k : ℝ) / Fintype.card V) • (of fun _ _ => 1)) *ᵥ ⇑(hA.eigenvectorBasis i) := by
      rw [hA.mulVec_aeval_eigenvectorBasis, smul_mulVec, hJ]
      by_cases hi : hA.eigenvalues i = (k : ℝ)
      · rw [ite_eq_left hi, hi, smul_smul, div_mul_cancel₀ _ hn]
      · rw [ite_eq_right hi, hp _ (hA.eigenvalues_mem_spectrumMultiset i) hi,
          zero_smul, smul_zero]
    apply Matrix.toEuclideanLin.injective
    apply hA.eigenvectorBasis.toBasis.ext
    intro i
    apply WithLp.ofLp_injective 2
    simpa only [toLpLin_apply, OrthonormalBasis.coe_toBasis, WithLp.ofLp_toLp] using heig i

/-- Theorem 7.10 of the spectral toolkit: a polynomial vanishing off the regular degree evaluates
to p(k)J/n. -/
theorem IsRegularOfDegree.aeval_eq_smul_allOnes_of_connected
    (hk : X.IsRegularOfDegree k) (hc : X.Connected) (p : ℝ[X])
    (hp : ∀ μ ∈ X.spectrumMultiset, μ ≠ (k : ℝ) → p.eval μ = 0) :
    aeval (X.adjMatrix ℝ) p = (p.eval (k : ℝ) / Fintype.card V) • (of fun _ _ => 1) := by
  -- Step `hoffman-forward`: use the forward spectral criterion.
  have he := hk.aeval_eq_smul_allOnes_iff_of_connected hc p
  exact he.mpr hp

end SimpleGraph
