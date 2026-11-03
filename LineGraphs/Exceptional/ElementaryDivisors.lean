/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.LatticeRank
import LineGraphs.Exceptional.LatticeCoordinates
import LineGraphs.Exceptional.ElementaryDivisorsMatrix

/-! # The lattice determinant from Smith normal form

Lemma `lem:snf` (Lemma 2.3) of [Exc]. We use Mathlib's Smith normal form of
the integral column span. Its coefficients are nonzero because they index a
basis of that span; zero diagonal entries of a square Smith matrix are omitted.
-/

open Module Submodule

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (X : SimpleGraph V) [DecidableRel X.Adj]

-- Lemma 2.3 [Exc]
/-- Lemma `lem:snf` (Lemma 2.3) of [Exc]: every Smith normal form of the
integral column span of `M(X)` has absolute coefficient product equal to the
lattice determinant. Mathlib's `Basis.SmithNormalForm` carries no divisibility-chain
condition: the theorem holds for every pair of bases related by the displayed
nonzero diagonal coefficients, whose individual values need not be elementary divisors.
A matrix Smith normal form of `M(X)` supplies such bases after zero columns are omitted.
Only the absolute product is used. Connectedness is unnecessary. -/
theorem prod_smith_coeffs_eq_latticeDet
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    {r : ℕ} (s : Basis.SmithNormalForm
      (span ℤ (Set.range X.integralGramMatrix.col)) V r) :
    ∏ i, (s.a i).natAbs = X.latticeDet := by
  classical
  obtain ⟨x, hx⟩ := X.exists_representation_iff_posSemidef.mpr hp
  let b := spanIntBasis x
  have hF : (hx.latticeGramMatrix b).det ≠ 0 := by
    rw [hx.det_latticeGramMatrix b]
    exact Int.natCast_ne_zero.mpr (ne_of_gt hx.latticeDet_pos)
  revert s
  rw [← Matrix.range_mulVecLin, hx.integralGramMatrix_eq_coordinates b]
  intro s
  calc
    ∏ i, (s.a i).natAbs = (hx.latticeGramMatrix b).det.natAbs :=
      Matrix.prod_smith_coeffs_eq_natAbs_det (latticeCoordinates b)
        (hx.latticeGramMatrix b) (latticeCoordinates_surjective b) hF s
    _ = X.latticeDet := by rw [hx.det_latticeGramMatrix b, Int.natAbs_natCast]

-- Lemma 2.3 [Exc]
/-- Lemma `lem:snf` (Lemma 2.3) of [Exc], with the Smith normal form chosen
by Mathlib: the lattice determinant is the product of its nonzero coefficients
in absolute value. -/
theorem latticeDet_eq_prod_smithNormalForm
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    let N := span ℤ (Set.range X.integralGramMatrix.col)
    let s := Submodule.smithNormalForm (Pi.basisFun ℤ V) N
    X.latticeDet = ∏ i, (s.2.a i).natAbs := by
  exact (X.prod_smith_coeffs_eq_latticeDet hp _).symm

end SimpleGraph
