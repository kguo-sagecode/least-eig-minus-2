/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Polynomial
import Mathlib.LinearAlgebra.Trace

/-!
# Trace and rank formulas

The remaining assertions of Theorem 3.2 of the spectral toolkit, including the
trace formula for an arbitrary idempotent, without a symmetry hypothesis.
-/

open Polynomial Module

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

namespace IsHermitian

variable (hA : A.IsHermitian)

include hA

/-- Theorem 3.2 of the spectral toolkit, step `trace-count`: rank is order minus the zero
multiplicity. -/
theorem rank_eq_card_sub_eigenvalueMultiplicity_zero :
    A.rank = Fintype.card n - A.eigenvalueMultiplicity 0 := by
  -- Step `trace-count`: count the complement of the zero-eigenvalue indices.
  have hr := hA.rank_eq_card_non_zero_eigs
  rw [hr, Fintype.card_subtype_compl, hA.eigenvalueMultiplicity_eq_card]
  simp [Fintype.card_subtype]

/-- Rank and zero multiplicity sum to the order, avoiding natural subtraction. -/
theorem rank_add_eigenvalueMultiplicity_zero :
    A.rank + A.eigenvalueMultiplicity 0 = Fintype.card n := by
  -- Step `trace-count`: zero and nonzero eigenvalue indices partition the basis.
  have hle : A.eigenvalueMultiplicity 0 ≤ Fintype.card n := by
    rw [hA.eigenvalueMultiplicity_eq_card]
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  rw [hA.rank_eq_card_sub_eigenvalueMultiplicity_zero, Nat.sub_add_cancel hle]

/-- Theorem 3.2 of the spectral toolkit, step `trace-f`: polynomial trace is the sum of polynomial
values. -/
theorem trace_aeval_eq_sum (p : ℝ[X]) :
    (aeval A p).trace = (A.spectrumMultiset.map p.eval).sum := by
  -- Steps `trace-polysymmetric`, `trace-f`: diagonalize and cancel the change of basis.
  have ht : (aeval A p).trace = ∑ i, p.eval (hA.eigenvalues i) := by
    rw [hA.aeval_eq_conj_diagonal, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
    simp
  rw [ht, hA.spectrumMultiset_eq_eigenvalues, Multiset.map_map]
  rfl

/-- Theorem 3.2 of the spectral toolkit, step `trace-frank`: polynomial rank counts original
eigenspaces
on which the polynomial does not vanish. -/
theorem rank_aeval_eq_sum_multiplicity (p : ℝ[X]) :
    (aeval A p).rank =
      ∑ μ ∈ A.spectrumMultiset.toFinset.filter (fun μ => p.eval μ ≠ 0),
        A.eigenvalueMultiplicity μ := by
  -- Step `trace-frank`: conjugation preserves rank; a diagonal matrix counts nonzero entries.
  have hr : (aeval A p).rank =
      (Finset.univ.filter fun i => p.eval (hA.eigenvalues i) ≠ 0).card := by
    rw [hA.aeval_eq_conj_diagonal, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
    simp [-isUnit_iff_ne_zero, -Unitary.coe_star, rank_diagonal, Fintype.card_subtype]
  rw [hr]
  simp_rw [hA.eigenvalueMultiplicity_eq_card]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset]
  exact (and_iff_right (hA.eigenvalues_mem_spectrumMultiset i)).symm

end IsHermitian

omit [DecidableEq n] in
/-- Theorem 3.2 of the spectral toolkit: every real idempotent has trace equal to its
natural-number rank,
including nonsymmetric idempotents. -/
theorem trace_eq_rank_of_idempotent (hA : A * A = A) : A.trace = (A.rank : ℝ) := by
  classical
  -- Step `trace-projection`: the associated endomorphism projects onto its range.
  have hi : IsIdempotentElem A.toLin' := by
    change A.toLin' ∘ₗ A.toLin' = A.toLin'
    rw [← toLin'_mul, hA]
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem A.toLin').mpr hi
  -- Step `trace-idemvalue`: the trace of a projection is the dimension of its range.
  have ht := hp.trace
  -- Step `trace-coordinate`: return from linear maps to matrices.
  have hr : A.rank = finrank ℝ A.toLin'.range :=
    A.rank_eq_finrank_range_toLin (Pi.basisFun ℝ n) (Pi.basisFun ℝ n)
  simpa only [trace_toLin'_eq, ← hr] using ht

end Matrix
