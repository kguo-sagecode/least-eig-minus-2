/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.GeneralizedLineGraph
import LineGraphs.LineSystem.RootType
import LineGraphs.Seidel.LatticeRoots

/-! # Exceptional graphs and their integral Gram matrices

Definitions D1, D2 and D4 for Section 2 of [Exc].
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (X : SimpleGraph V) [DecidableRel X.Adj]

-- Section 1 [Exc]
/-- Section `sec:intro` (Section 1) of [Exc]:
a connected graph with least eigenvalue at least `-2`
which is not a generalized line graph. The definition agrees with the note on finite
vertex types, the standing hypothesis of every theorem here; it also has a formal
meaning for infinite types, outside the note's scope. -/
def IsExceptional : Prop :=
  X.Connected ∧ ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef ∧
    ¬ X.IsGeneralizedLineGraph

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
the integral matrix `M(X) = 2I + A(X)`. -/
def integralGramMatrix : Matrix V V ℤ :=
  (2 : ℤ) • (1 : Matrix V V ℤ) + X.adjMatrix ℤ

-- Section 2 [Exc]
omit [Fintype V] in
/-- Section `sec:lattices` (Section 2) of [Exc]:
casting the integral matrix `M(X)` gives the real Gram matrix. -/
@[simp] theorem integralGramMatrix_cast :
    (X.integralGramMatrix.map (Int.cast : ℤ → ℝ)) =
      (2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ := by
  ext u v
  simp only [integralGramMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, adjMatrix, smul_eq_mul]
  split_ifs <;> norm_num

end SimpleGraph

namespace LineSystem.RootType

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the determinants of the irreducible
root lattices. The identification with Gram determinants is proved in `RootLattice`. -/
def latticeDet : RootType → ℕ
  | .A ℓ _ => ℓ + 1
  | .D _ _ => 4
  | .E₆ => 3
  | .E₇ => 2
  | .E₈ => 1

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: every listed lattice determinant is positive. -/
theorem latticeDet_pos (t : RootType) : 0 < t.latticeDet := by
  cases t <;> simp [latticeDet]

end LineSystem.RootType
