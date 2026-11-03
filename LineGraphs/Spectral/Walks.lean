/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Regularity

/-!
# Walk counts and the first adjacency moments

The walk-count and length-zero/one parts of Theorem 5.1 of the spectral toolkit.
The second moment is in `Regularity.lean`. The triangle formulas are not proved here.
-/

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
  [DecidableRel X.Adj]

/-- Theorem 5.1 of the spectral toolkit: the trace counts closed walks with a distinguished
initial vertex. -/
theorem trace_pow_adjMatrix_eq_closedWalks (k : ℕ) :
    ((X.adjMatrix ℝ) ^ k).trace =
      (Nat.card (Σ u : V, {p : X.Walk u u // p.length = k}) : ℝ) := by
  -- Step `walk-entry`: Mathlib counts walks of each length by adjacency powers.
  have hentry := X.adjMatrix_pow_apply_eq_card_walk (α := ℝ) k
  -- Step `walk-closed`: sum the diagonal entries, counting the starting vertex.
  have htrace : ((X.adjMatrix ℝ) ^ k).trace =
      ∑ u, (Fintype.card {p : X.Walk u u // p.length = k} : ℝ) :=
    Finset.sum_congr rfl fun u _ => hentry u u
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum] using htrace

/-- Theorem 5.1 of the spectral toolkit: the quadratic form at the all-ones vector counts all
walks. -/
theorem dotProduct_pow_adjMatrix_eq_walks (k : ℕ) :
    (fun _ : V => (1 : ℝ)) ⬝ᵥ ((X.adjMatrix ℝ) ^ k *ᵥ fun _ => 1) =
      (Nat.card (Σ u : V, Σ v : V, {p : X.Walk u v // p.length = k}) : ℝ) := by
  -- Step `walk-total`: summing every matrix entry counts both endpoints.
  have hentry := X.adjMatrix_pow_apply_eq_card_walk (α := ℝ) k
  simp only [dotProduct, mulVec, one_mul, mul_one, hentry,
    Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
  rfl

/-- Theorem 5.1 of the spectral toolkit, the zeroth adjacency moment: every vertex contributes one
eigenvalue. -/
theorem card_spectrumMultiset : X.spectrumMultiset.card = Fintype.card V := by
  -- Step `walk-length0`: the spectral multiset has the matrix order.
  have hcard := (X.isHermitian_adjMatrix ℝ).card_spectrumMultiset
  exact hcard

/-- Theorem 5.1 of the spectral toolkit, the first adjacency moment: a simple graph has no loops. -/
theorem sum_spectrumMultiset_eq_zero : X.spectrumMultiset.sum = 0 := by
  -- Step `walk-length1`: the zero diagonal makes the trace vanish.
  have ht := (X.isHermitian_adjMatrix ℝ).trace_pow_eq_sum_spectrumMultiset 1
  simpa only [pow_one, trace_adjMatrix, Multiset.map_id', spectrumMultiset] using ht.symm

end SimpleGraph
