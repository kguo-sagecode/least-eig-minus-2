/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# The trace obstruction C24

Computation `comp:C24`, used in the remark after Theorem 4.4 of [CGSS]. The trace
form counts diagonal, adjacent, and nonadjacent entries directly; it does not need
the multiplicity parameter of `cgss/certificates/data/c24.json`.
-/

open Matrix

namespace Computations.C24

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj]

/-- Computation C24 (see `cgss/certificates/README.md`), for Theorem 4.4 of [CGSS], step `s4c24row`: the squared entries
in a row of
`aI + bA + cJ` are counted by the degree. -/
theorem sum_sq_row (u : V) (a b c : ℝ) :
    (∑ v, ((a • (1 : Matrix V V ℝ) + b • X.adjMatrix ℝ +
      c • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))) u v) ^ 2) =
    a ^ 2 + 2 * a * c + (b ^ 2 + 2 * b * c) * X.degree u +
      Fintype.card V * c ^ 2 := by
  have he (v : V) :
      ((a • (1 : Matrix V V ℝ) + b • X.adjMatrix ℝ +
        c • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))) u v) ^ 2 =
      (if v = u then a ^ 2 + 2 * a * c else 0) +
        (b ^ 2 + 2 * b * c) * (if X.Adj u v then 1 else 0) + c ^ 2 := by
    by_cases huv : u = v
    · subst v
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply_eq, mul_one,
        SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false, mul_zero,
        add_zero, of_apply, ite_true]
      ring
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply_ne huv, mul_zero,
        SimpleGraph.adjMatrix_apply, zero_add, of_apply, mul_one,
        ite_eq_right (Ne.symm huv)]
      split_ifs <;> ring
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← X.degree_eq_sum_if_adj (R := ℝ)]
  simp

-- Computation C24
/-- Computation C24 (see `cgss/certificates/README.md`), for Theorem 4.4 of [CGSS], `comp:C24`: the trace, squared-entry
sum, and strict
trace/rank obstruction for a 16-regular graph on 28 vertices. -/
theorem trace_sq_gt (hX : X.IsRegularOfDegree 16) (hn : Fintype.card V = 28) :
    let N := (2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ -
      (9 / 14 : ℝ) • (of fun _ _ ↦ (1 : ℝ))
    N.trace = 38 ∧ (∑ u, ∑ v, N u v ^ 2) = 236 ∧
      N.trace ^ 2 > 6 * (∑ u, ∑ v, N u v ^ 2) := by
  dsimp only
  have ht : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ -
      (9 / 14 : ℝ) • (of fun _ _ ↦ (1 : ℝ))).trace = 38 := by
    simp [trace, diag, SimpleGraph.adjMatrix_apply, hn]
    norm_num
  have hs : (∑ u, ∑ v, (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ -
      (9 / 14 : ℝ) • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))) u v) ^ 2) = 236 := by
    have he (u : V) := sum_sq_row (X := X) u 2 1 (-(9 / 14))
    simp only [one_smul, neg_smul, ← sub_eq_add_neg, hX.degree_eq, hn] at he
    simp_rw [he]
    norm_num [hn]
  exact ⟨ht, hs, by rw [ht, hs]; norm_num⟩

end Computations.C24
