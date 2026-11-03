/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Polynomial and moment certificates for real symmetric matrices

The public multiplicities are counts in `charpoly.roots`. `IsHermitian` over `ℝ` is the
usual symmetry condition. Moments include exponent zero: its trace is the matrix order.
The candidate eigenvalues may include unused values (multiplicity zero).
-/

open Polynomial
open scoped BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real roots, counted with algebraic multiplicity. -/
noncomputable def spectrumMultiset (A : Matrix n n ℝ) : Multiset ℝ := A.charpoly.roots

/-- Algebraic multiplicity over `ℝ`, compatible with the spectral toolkit's root multiset. -/
noncomputable def eigenvalueMultiplicity (A : Matrix n n ℝ) (θ : ℝ) : ℕ :=
  A.charpoly.roots.count θ

/-- The root multiset is exactly the spectral theorem's eigenvalue family. -/
theorem IsHermitian.spectrumMultiset_eq_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : A.spectrumMultiset = Finset.univ.val.map hA.eigenvalues := by
  simpa [spectrumMultiset] using hA.roots_charpoly_eq_eigenvalues

/-- The first entry of the decreasing eigenvalue enumeration, for nonempty matrices. -/
noncomputable def IsHermitian.largestEigenvalue [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : ℝ := hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩

omit [DecidableEq n] in
/-- The last index `card n - 1` of the decreasing eigenvalue enumeration `eigenvalues₀`, for a
nonempty index type. -/
def lastIndex (n : Type*) [Fintype n] [Nonempty n] : Fin (Fintype.card n) :=
  ⟨Fintype.card n - 1, Nat.sub_lt Fintype.card_pos (by decide)⟩

/-- The last entry of the decreasing eigenvalue enumeration, for nonempty matrices. -/
noncomputable def IsHermitian.leastEigenvalue [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ (lastIndex n)

theorem IsHermitian.trace_pow_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply]
  rw [trace_mul_cycle]
  simp [diagonal_pow, trace_diagonal]

/-- Trace moments expressed directly in the spectrum multiset (spectral toolkit interface). -/
theorem IsHermitian.trace_pow_eq_sum_spectrumMultiset {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = (A.spectrumMultiset.map (fun θ => θ ^ k)).sum := by
  rw [hA.spectrumMultiset_eq_eigenvalues, hA.trace_pow_eq_sum]
  rw [Multiset.map_map]
  rfl

theorem IsHermitian.eval_eigenvalue_eq_zero {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {p : ℝ[X]} (hp : aeval A p = 0) (i : n) : p.eval (hA.eigenvalues i) = 0 := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) (star hA.eigenvectorUnitary)
  have he : aeval (diagonal hA.eigenvalues) p = 0 := by
    have hh := congrArg e hp
    rw [← aeval_algHom_apply e] at hh
    simpa [e, hA.conjStarAlgAut_star_eigenvectorUnitary] using hh
  have hd : aeval (diagonal hA.eigenvalues) p =
      diagonal (fun j => p.eval (hA.eigenvalues j)) := by
    change aeval (diagonalAlgHom (n := n) (α := ℝ) ℝ hA.eigenvalues) p = _
    rw [aeval_algHom_apply]
    change diagonal (aeval hA.eigenvalues p) = _
    congr 1
    funext j
    simp
  rw [hd] at he
  simpa using congrFun (congrFun he i) i

/-- The annihilating product rules out all eigenvalues outside the supplied list. -/
theorem IsHermitian.eigenvalues_mem_of_annihilating {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {m : ℕ} (θ : Fin m → ℝ)
    (hp : aeval A (∏ i, (X - C (θ i))) = 0) (a : n) :
    ∃ i, hA.eigenvalues a = θ i := by
  have he := hA.eval_eigenvalue_eq_zero hp a
  simpa only [eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero] using he

theorem IsHermitian.eigenvalueMultiplicity_eq_card {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (θ : ℝ) :
    A.eigenvalueMultiplicity θ = (Finset.univ.filter fun a => hA.eigenvalues a = θ).card := by
  classical
  simp [eigenvalueMultiplicity, hA.roots_charpoly_eq_eigenvalues, Multiset.count_map,
    ← Finset.filter_val, eq_comm]

omit [DecidableEq n] in
private theorem sum_pow_eq_moments {m : ℕ} (f : n → ℝ) (θ : Fin m → ℝ)
    (hθ : Function.Injective θ) (hs : ∀ a, ∃ i, f a = θ i) (k : ℕ) :
    (∑ a, f a ^ k) = ∑ i, ((Finset.univ.filter fun a => f a = θ i).card : ℝ) * θ i ^ k := by
  classical
  symm
  simp_rw [← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  obtain ⟨i, hi⟩ := hs a
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hne : f a ≠ θ j := by rw [hi]; exact fun h => hji (hθ h).symm
    simp [hne]
  · simp

/-- Every certified matrix supplies a solution to the transposed Vandermonde system. -/
theorem IsHermitian.trace_pow_eq_multiplicities {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {m : ℕ} (θ : Fin m → ℝ) (hθ : Function.Injective θ)
    (hp : aeval A (∏ i, (X - C (θ i))) = 0) (k : ℕ) :
    (A ^ k).trace = ∑ i, (A.eigenvalueMultiplicity (θ i) : ℝ) * θ i ^ k := by
  classical
  rw [hA.trace_pow_eq_sum]
  simp_rw [hA.eigenvalueMultiplicity_eq_card]
  exact sum_pow_eq_moments hA.eigenvalues θ hθ (hA.eigenvalues_mem_of_annihilating θ hp) k

/-- Distinct nodes make the moment equations unique. This is precisely invertibility
of the transposed Vandermonde matrix, including the empty system. -/
theorem eq_of_vandermonde_moments {m : ℕ} {θ : Fin m → ℝ}
    (hθ : Function.Injective θ) {u v : Fin m → ℝ}
    (h : ∀ j : Fin m, (∑ i, u i * θ i ^ j.val) = ∑ i, v i * θ i ^ j.val) : u = v := by
  have hz : u - v = 0 := eq_zero_of_forall_pow_sum_mul_pow_eq_zero hθ (fun j => by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (h j))
  exact sub_eq_zero.mp hz

/-- Certificate theorem: the algebraic multiplicities are the unique real solution of
`∑ i, μᵢ θᵢʲ = tr(Aʲ)` for `0 ≤ j < m`. -/
theorem IsHermitian.multiplicities_eq_of_certificate {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {m : ℕ} (θ : Fin m → ℝ) (hθ : Function.Injective θ)
    (hp : aeval A (∏ i, (X - C (θ i))) = 0) (μ : Fin m → ℝ)
    (ht : ∀ j : Fin m, (A ^ j.val).trace = ∑ i, μ i * θ i ^ j.val) :
    ∀ i, (A.eigenvalueMultiplicity (θ i) : ℝ) = μ i := by
  have he : (fun i => (A.eigenvalueMultiplicity (θ i) : ℝ)) = μ :=
    eq_of_vandermonde_moments hθ (fun j => by
      rw [← hA.trace_pow_eq_multiplicities θ hθ hp, ht])
  exact congrFun he

/-- Certificate theorem for C13 and C15. The matrix types may have different orders;
the zeroth moment handles that case. No eigenvalue computation is performed. -/
theorem IsHermitian.charpoly_eq_of_annihilatingPolynomial_trace
    {n' : Type*} [Fintype n'] [DecidableEq n'] {A : Matrix n n ℝ} {B : Matrix n' n' ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {m : ℕ}
    (θ : Fin m → ℝ) (hθ : Function.Injective θ)
    (hAp : aeval A (∏ i, (X - C (θ i))) = 0)
    (hBp : aeval B (∏ i, (X - C (θ i))) = 0)
    (ht : ∀ j : Fin m, (A ^ j.val).trace = (B ^ j.val).trace) :
    A.charpoly = B.charpoly := by
  classical
  have hm : ∀ i, A.eigenvalueMultiplicity (θ i) = B.eigenvalueMultiplicity (θ i) := by
    intro i
    exact_mod_cast hA.multiplicities_eq_of_certificate θ hθ hAp
      (fun i => (B.eigenvalueMultiplicity (θ i) : ℝ))
      (fun j => (ht j).trans (hB.trace_pow_eq_multiplicities θ hθ hBp j.val)) i
  have hroots : A.charpoly.roots = B.charpoly.roots := by
    apply Multiset.ext.mpr
    intro x
    by_cases hx : ∃ i, x = θ i
    · obtain ⟨i, rfl⟩ := hx
      exact hm i
    · have hAz : x ∉ A.charpoly.roots := by
        rw [hA.roots_charpoly_eq_eigenvalues]
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
          Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
        rintro ⟨a, rfl⟩
        exact hx (hA.eigenvalues_mem_of_annihilating θ hAp a)
      have hBz : x ∉ B.charpoly.roots := by
        rw [hB.roots_charpoly_eq_eigenvalues]
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
          Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
        rintro ⟨a, rfl⟩
        exact hx (hB.eigenvalues_mem_of_annihilating θ hBp a)
      simp [Multiset.count_eq_zero.mpr hAz, Multiset.count_eq_zero.mpr hBz]
  rw [hA.splits_charpoly.eq_prod_roots_of_monic (charpoly_monic A),
    hB.splits_charpoly.eq_prod_roots_of_monic (charpoly_monic B), hroots]

/-- The certificate determines the whole characteristic polynomial, including zero
multiplicities for surplus candidate roots. -/
theorem IsHermitian.charpoly_eq_prod_multiplicities {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {m : ℕ} (θ : Fin m → ℝ) (hθ : Function.Injective θ)
    (hp : aeval A (∏ i, (X - C (θ i))) = 0) :
    A.charpoly = ∏ i, (X - C (θ i)) ^ A.eigenvalueMultiplicity (θ i) := by
  classical
  rw [hA.charpoly_eq]
  simp_rw [hA.eigenvalueMultiplicity_eq_card]
  symm
  simp_rw [← Finset.prod_const, Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro a _
  obtain ⟨i, hi⟩ := hA.eigenvalues_mem_of_annihilating θ hp a
  rw [Finset.prod_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hne : hA.eigenvalues a ≠ θ j := by rw [hi]; exact fun h => hji (hθ h).symm
    simp [hne]
  · simp

/-- The mathematical polynomial certificate equals the ordered product of matrix factors. -/
theorem aeval_prod_X_sub_C_eq {m : ℕ} (A : Matrix n n ℝ) (θ : Fin m → ℝ) :
    aeval A (∏ i, (X - C (θ i))) =
      (List.ofFn fun i => A - θ i • (1 : Matrix n n ℝ)).prod := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [Algebra.algebraMap_eq_smul_one]

/-- Interface name from the spectral toolkit: a proposed natural multiplicity vector
is certified by the annihilator and the first `m` moments. -/
theorem IsHermitian.spectrumMultiset_eq_of_annihilatingPolynomial_trace
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {m : ℕ}
    (θ : Fin m → ℝ) (hθ : Function.Injective θ) (μ : Fin m → ℕ)
    (hp : aeval A (∏ i, (X - C (θ i))) = 0)
    (ht : ∀ j : Fin m, (A ^ j.val).trace = ∑ i, (μ i : ℝ) * θ i ^ j.val) :
    A.spectrumMultiset = ∑ i, Multiset.replicate (μ i) (θ i) := by
  classical
  have hm : ∀ i, A.eigenvalueMultiplicity (θ i) = μ i := by
    intro i
    exact_mod_cast hA.multiplicities_eq_of_certificate θ hθ hp (fun i => (μ i : ℝ)) ht i
  unfold spectrumMultiset
  rw [hA.charpoly_eq_prod_multiplicities θ hθ hp]
  simp_rw [hm]
  rw [Polynomial.roots_prod]
  · simp only [Multiset.bind, Multiset.join, roots_pow, roots_X_sub_C, Multiset.nsmul_singleton,
      Fin.univ_val_map, Multiset.sum_coe, Finset.sum]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _)

end Matrix

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Adjacency eigenvalues with algebraic multiplicities, including zero. -/
noncomputable def spectrumMultiset (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℝ :=
  (G.adjMatrix ℝ).spectrumMultiset

/-- Algebraic multiplicity of an adjacency eigenvalue. -/
noncomputable def eigenvalueMultiplicity (G : SimpleGraph V) [DecidableRel G.Adj] (θ : ℝ) : ℕ :=
  (G.adjMatrix ℝ).eigenvalueMultiplicity θ

/-- Equality of real adjacency characteristic polynomials, across arbitrary finite vertex types. -/
def Cospectral (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop :=
  (G.adjMatrix ℝ).charpoly = (H.adjMatrix ℝ).charpoly

/-- The largest adjacency eigenvalue, requiring a nonempty vertex type. -/
noncomputable def largestEigenvalue [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (G.isHermitian_adjMatrix ℝ).largestEigenvalue

/-- The least adjacency eigenvalue, requiring a nonempty vertex type. -/
noncomputable def leastEigenvalue [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (G.isHermitian_adjMatrix ℝ).leastEigenvalue

/-- An isomorphism preserves the adjacency characteristic polynomial under any labellings. -/
theorem Iso.cospectral {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) : G.Cospectral H := by
  have he : (H.adjMatrix ℝ).submatrix e e = G.adjMatrix ℝ := by
    ext i j
    simp [adjMatrix_apply, e.map_adj_iff]
  change (G.adjMatrix ℝ).charpoly = (H.adjMatrix ℝ).charpoly
  rw [← he]
  exact Matrix.charpoly_reindex e.toEquiv.symm (H.adjMatrix ℝ)

/-- The Seidel matrix has zero diagonal and off-diagonal entries minus one on edges. -/
def seidelMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of (fun _ _ => 1) - 1 - (2 : ℝ) • G.adjMatrix ℝ

end SimpleGraph
