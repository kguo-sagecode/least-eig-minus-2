/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Support
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Weighted graphs for the Cartan classification

The matrix formulation of `def:rem-weighted` in the Remark 3.11 blueprint.
Finiteness and nonemptiness are assumptions on the spectral results, rather than fields
of the graph. Containment retains its specified vertex embedding.
-/

/-- A real symmetric nonnegative matrix with zero diagonal. -/
structure WeightedGraph (ι : Type*) where
  /-- The weighted adjacency matrix. -/
  weights : Matrix ι ι ℝ
  /-- The weights are symmetric. -/
  symmetric : weights.IsSymm
  /-- All weights are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ weights i j
  /-- Loops have weight zero. -/
  diag : ∀ i, weights i i = 0

namespace WeightedGraph

variable {ι κ : Type*}

/-- The support consists of the positive-weight edges. -/
def support (X : WeightedGraph ι) : SimpleGraph ι where
  Adj i j := 0 < X.weights i j
  symm := ⟨fun i j h => by simpa only [X.symmetric.apply i j] using h⟩
  loopless := ⟨fun i => by simp [X.diag i]⟩

/-- The real weighted adjacency matrix is Hermitian. -/
theorem isHermitian (X : WeightedGraph ι) : X.weights.IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr X.symmetric

/-- `X` contains `Y` along `e`, allowing omitted edges and decreased weights. -/
def Contains (X : WeightedGraph ι) (Y : WeightedGraph κ) (e : κ ↪ ι) : Prop :=
  ∀ i j, Y.weights i j ≤ X.weights (e i) (e j)

open Matrix in
/-- A nonnegative eigenvector with a zero coordinate vanishes on a connected support
(`lem:rem-propagation` of Remark 3.11). -/
theorem eq_zero_of_nonneg_eigenvector_zero [Fintype ι] (X : WeightedGraph ι)
    (hX : X.support.Connected) {x : ι → ℝ} {t : ℝ}
    (hx : ∀ i, 0 ≤ x i) (heig : X.weights *ᵥ x = t • x)
    {i₀ : ι} (hzero : x i₀ = 0) : x = 0 := by
  have hstep {i j : ι} (hij : X.support.Adj i j) (hi : x i = 0) : x j = 0 := by
    have hsum : ∑ k, X.weights i k * x k = 0 := by
      have h := congr_fun heig i
      simpa only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hi, mul_zero] using h
    have hterm : X.weights i j * x j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (X.nonneg i k) (hx k))).mp
        hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hij)
  have heq : ∀ ⦃i j⦄, X.support.Adj i j → (x i = 0) = (x j = 0) := by
    intro i j hij
    exact propext ⟨hstep hij, hstep hij.symm⟩
  funext j
  exact (hX.constant_of_edge_eq heq i₀ j) ▸ hzero

end WeightedGraph
