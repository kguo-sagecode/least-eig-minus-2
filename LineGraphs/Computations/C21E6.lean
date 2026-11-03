/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C21E6Data
import LineGraphs.Computations.C20Data
import LineGraphs.Computations.C4E6
import LineGraphs.Computations.SimpleRootCertificates
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# C21 E₆ simple-root basis

C21: the simple-root basis of E₆ and its Gram determinant. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C21

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the scaled LDL factorization of the E₆ Gram matrix
checks. -/
theorem e6_ldl_checked : checkScaledLDL 6 16 e6Gram e6Lower e6Diagonal = true := by
  decide +kernel

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the E₆ Gram determinant is 3. -/
theorem e6_gram_det : (toMatrix (R := ℤ) 6 e6Gram).det = 3 := by
  have hl : (toMatrix (R := ℤ) 6 e6Lower).IsLowerTriangular := by
    intro i j hij
    exact (by decide +kernel : ∀ i j : Fin 6, i < j → entry e6Lower i j = 0) i j hij
  have hd : (toMatrix (R := ℤ) 6 e6Lower).det = 2 ^ 6 := by
    rw [Matrix.det_of_isLowerTriangular _ hl]
    decide +kernel
  have he := congrArg Matrix.det (checkScaledLDL_sound e6_ldl_checked)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, hd] at he
  have hp : (∏ i : Fin 6, e6Diagonal[i.val]?.getD 0) = 12288 := by decide +kernel
  rw [hp] at he
  norm_num at he
  omega

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: every E₆ root has the certified integral
coordinates. -/
theorem e6_coordinates_checked :
    checkRootCoordinates 72 8 6 C20.e6Roots e6Simple e6Coefficients = true := by
  decide +kernel

end Computations.C21

namespace LineSystem

/-- The simple roots specified by the Sage C21 certificate, with squared norm two. -/
noncomputable def E₆.simpleRoot (i : Fin 6) : EuclideanSpace ℝ (Fin 8) :=
  integerVector (1 / 2) (fun j => entry C21.e6Simple i j)

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the chosen simple roots belong to E₆. -/
theorem E₆.simpleRoot_mem (i : Fin 6) : E₆.simpleRoot i ∈ E₆.Φ := by
  apply (integerVector_mem_E₆_iff _).mpr
  exact (by decide +kernel : ∀ i : Fin 6,
    isE₆Root (fun j => entry C21.e6Simple i j) = true) i

/-- The Gram matrix of the actual normalized roots is the certified Cartan matrix. -/
theorem E₆.gram_simpleRoot : Matrix.gram ℝ E₆.simpleRoot =
    toMatrix (R := ℝ) 6 C21.e6Gram := by
  ext i j
  change ⟪integerVector (1 / 2) (fun t => entry C21.e6Simple i t),
    integerVector (1 / 2) (fun t => entry C21.e6Simple j t)⟫ = _
  rw [inner_integerVector]
  have he := (by decide +kernel : ∀ i j : Fin 6,
    integerInner (fun t : Fin 8 => entry C21.e6Simple i t)
      (fun t => entry C21.e6Simple j t) = 4 * entry C21.e6Gram i j) i j
  rw [he]
  norm_num [toMatrix]
  ring

/-- C21: the Gram determinant of the simple roots. -/
theorem E₆.det_gram_simpleRoot : (Matrix.gram ℝ E₆.simpleRoot).det = 3 := by
  rw [E₆.gram_simpleRoot, det_toMatrix_real, C21.e6_gram_det]
  norm_num

/-- The simple roots, considered in the real root span. -/
noncomputable def E₆.simpleRootInSpan (i : Fin 6) : Submodule.span ℝ E₆.Φ :=
  ⟨E₆.simpleRoot i, Submodule.subset_span (E₆.simpleRoot_mem i)⟩

/-- C21: the certified simple roots form a basis of the root span. -/
noncomputable def E₆.simpleBasis : Module.Basis (Fin 6) ℝ (Submodule.span ℝ E₆.Φ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (Matrix.linearIndependent_of_det_gram_ne_zero (v := E₆.simpleRootInSpan) (by
      change (Matrix.gram ℝ E₆.simpleRoot).det ≠ 0
      rw [E₆.det_gram_simpleRoot]
      norm_num)) (by rw [finrank_span_E₆]; exact Fintype.card_fin 6)

@[simp] theorem E₆.simpleBasis_apply (i : Fin 6) :
    (E₆.simpleBasis i : EuclideanSpace ℝ (Fin 8)) = E₆.simpleRoot i := by
  simp [simpleBasis, coe_basisOfLinearIndependentOfCardEqFinrank, simpleRootInSpan]

/-- C21: every root has integral simple-root coordinates, all of one sign. -/
theorem E₆.exists_simpleRoot_coordinates {r} (hr : r ∈ E₆.Φ) :
    ∃ z : Fin 6 → ℤ, ((∀ i, 0 ≤ z i) ∨ (∀ i, z i ≤ 0)) ∧
      r = ∑ i, (z i : ℝ) • E₆.simpleRoot i := by
  rw [E₆.tableModel.Φ_eq] at hr
  obtain ⟨a, rfl⟩ := hr
  change Fin 72 at a
  have hc := checkRootCoordinates_sound C21.e6_coordinates_checked a
  refine ⟨fun i => entry C21.e6Coefficients a i, hc.1, ?_⟩
  have he : E₆.tableModel.v a = fun j : Fin 8 =>
      ∑ i : Fin 6, entry C21.e6Coefficients a i * entry C21.e6Simple i j := by
    funext j
    exact hc.2 j
  change integerVector (1 / 2) (E₆.tableModel.v a) = _
  rw [he, integerVector_sum]
  rfl

end LineSystem

namespace Computations.C21

/-- The relabelling of the simple roots of `E₆` onto Mathlib's order of `CartanMatrix.E 6`
(Bourbaki's numbering): `e6Gram i j = CartanMatrix.E 6 (e6Relabel i) (e6Relabel j)`. -/
def e6Relabel : Fin 6 ≃ Fin 6 :=
  ⟨![1, 2, 3, 4, 5, 0], ![5, 0, 1, 2, 3, 4], by decide, by decide⟩

/-- C21: the certified Gram matrix is Mathlib's Cartan matrix `CartanMatrix.E 6`, up to the
relabelling `e6Relabel`. -/
theorem e6_gram_eq_cartan :
    toMatrix (R := ℤ) 6 e6Gram = (CartanMatrix.E 6).submatrix e6Relabel e6Relabel := by
  ext i j
  change entry e6Gram i j = CartanMatrix.E 6 (e6Relabel i) (e6Relabel j)
  exact (by decide +kernel : ∀ i j : Fin 6,
    entry e6Gram i j = CartanMatrix.E 6 (e6Relabel i) (e6Relabel j)) i j

end Computations.C21

/-- C21: the Gram matrix of the simple roots is `CartanMatrix.E 6` up to a relabelling. -/
theorem LineSystem.E₆.gram_simpleRoot_eq_cartan : Matrix.gram ℝ LineSystem.E₆.simpleRoot =
    ((CartanMatrix.E 6).submatrix C21.e6Relabel C21.e6Relabel).map (Int.cast : ℤ → ℝ) := by
  rw [LineSystem.E₆.gram_simpleRoot, ← C21.e6_gram_eq_cartan]
  rfl
