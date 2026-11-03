/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C21E7Data
import LineGraphs.Computations.C20Data
import LineGraphs.Computations.C4E7
import LineGraphs.Computations.SimpleRootCertificates
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# C21 E₇ simple-root basis

C21: the simple-root basis of E₇ and its Gram determinant. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C21

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the scaled LDL factorization of the E₇ Gram matrix
checks. -/
theorem e7_ldl_checked : checkScaledLDL 7 16 e7Gram e7Lower e7Diagonal = true := by
  decide +kernel

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the E₇ Gram determinant is 2. -/
theorem e7_gram_det : (toMatrix (R := ℤ) 7 e7Gram).det = 2 := by
  have hl : (toMatrix (R := ℤ) 7 e7Lower).IsLowerTriangular := by
    intro i j hij
    exact (by decide +kernel : ∀ i j : Fin 7, i < j → entry e7Lower i j = 0) i j hij
  have hd : (toMatrix (R := ℤ) 7 e7Lower).det = 2 ^ 7 := by
    rw [Matrix.det_of_isLowerTriangular _ hl]
    decide +kernel
  have he := congrArg Matrix.det (checkScaledLDL_sound e7_ldl_checked)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, hd] at he
  have hp : (∏ i : Fin 7, e7Diagonal[i.val]?.getD 0) = 32768 := by decide +kernel
  rw [hp] at he
  norm_num at he
  omega

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: every E₇ root has the certified integral
coordinates. -/
theorem e7_coordinates_checked :
    checkRootCoordinates 126 8 7 C20.e7Roots e7Simple e7Coefficients = true := by
  decide +kernel

end Computations.C21

namespace LineSystem

/-- The simple roots specified by the Sage C21 certificate, with squared norm two. -/
noncomputable def E₇.simpleRoot (i : Fin 7) : EuclideanSpace ℝ (Fin 8) :=
  integerVector (1 / 2) (fun j => entry C21.e7Simple i j)

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the chosen simple roots belong to E₇. -/
theorem E₇.simpleRoot_mem (i : Fin 7) : E₇.simpleRoot i ∈ E₇.Φ := by
  apply (integerVector_mem_E₇_iff _).mpr
  exact (by decide +kernel : ∀ i : Fin 7,
    isE₇Root (fun j => entry C21.e7Simple i j) = true) i

/-- The Gram matrix of the actual normalized roots is the certified Cartan matrix. -/
theorem E₇.gram_simpleRoot : Matrix.gram ℝ E₇.simpleRoot =
    toMatrix (R := ℝ) 7 C21.e7Gram := by
  ext i j
  change ⟪integerVector (1 / 2) (fun t => entry C21.e7Simple i t),
    integerVector (1 / 2) (fun t => entry C21.e7Simple j t)⟫ = _
  rw [inner_integerVector]
  have he := (by decide +kernel : ∀ i j : Fin 7,
    integerInner (fun t : Fin 8 => entry C21.e7Simple i t)
      (fun t => entry C21.e7Simple j t) = 4 * entry C21.e7Gram i j) i j
  rw [he]
  norm_num [toMatrix]
  ring

/-- C21: the Gram determinant of the simple roots. -/
theorem E₇.det_gram_simpleRoot : (Matrix.gram ℝ E₇.simpleRoot).det = 2 := by
  rw [E₇.gram_simpleRoot, det_toMatrix_real, C21.e7_gram_det]
  norm_num

/-- The simple roots, considered in the real root span. -/
noncomputable def E₇.simpleRootInSpan (i : Fin 7) : Submodule.span ℝ E₇.Φ :=
  ⟨E₇.simpleRoot i, Submodule.subset_span (E₇.simpleRoot_mem i)⟩

/-- C21: the certified simple roots form a basis of the root span. -/
noncomputable def E₇.simpleBasis : Module.Basis (Fin 7) ℝ (Submodule.span ℝ E₇.Φ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (Matrix.linearIndependent_of_det_gram_ne_zero (v := E₇.simpleRootInSpan) (by
      change (Matrix.gram ℝ E₇.simpleRoot).det ≠ 0
      rw [E₇.det_gram_simpleRoot]
      norm_num)) (by rw [finrank_span_E₇]; exact Fintype.card_fin 7)

@[simp] theorem E₇.simpleBasis_apply (i : Fin 7) :
    (E₇.simpleBasis i : EuclideanSpace ℝ (Fin 8)) = E₇.simpleRoot i := by
  simp [simpleBasis, coe_basisOfLinearIndependentOfCardEqFinrank, simpleRootInSpan]

/-- C21: every root has integral simple-root coordinates, all of one sign. -/
theorem E₇.exists_simpleRoot_coordinates {r} (hr : r ∈ E₇.Φ) :
    ∃ z : Fin 7 → ℤ, ((∀ i, 0 ≤ z i) ∨ (∀ i, z i ≤ 0)) ∧
      r = ∑ i, (z i : ℝ) • E₇.simpleRoot i := by
  rw [E₇.tableModel.Φ_eq] at hr
  obtain ⟨a, rfl⟩ := hr
  change Fin 126 at a
  have hc := checkRootCoordinates_sound C21.e7_coordinates_checked a
  refine ⟨fun i => entry C21.e7Coefficients a i, hc.1, ?_⟩
  have he : E₇.tableModel.v a = fun j : Fin 8 =>
      ∑ i : Fin 7, entry C21.e7Coefficients a i * entry C21.e7Simple i j := by
    funext j
    exact hc.2 j
  change integerVector (1 / 2) (E₇.tableModel.v a) = _
  rw [he, integerVector_sum]
  rfl

end LineSystem

namespace Computations.C21

/-- The relabelling of the simple roots of `E₇` onto Mathlib's order of `CartanMatrix.E 7`
(Bourbaki's numbering): `e7Gram i j = CartanMatrix.E 7 (e7Relabel i) (e7Relabel j)`. -/
def e7Relabel : Fin 7 ≃ Fin 7 :=
  ⟨![2, 1, 3, 4, 5, 6, 0], ![6, 1, 0, 2, 3, 4, 5], by decide, by decide⟩

/-- C21: the certified Gram matrix is Mathlib's Cartan matrix `CartanMatrix.E 7`, up to the
relabelling `e7Relabel`. -/
theorem e7_gram_eq_cartan :
    toMatrix (R := ℤ) 7 e7Gram = (CartanMatrix.E 7).submatrix e7Relabel e7Relabel := by
  ext i j
  change entry e7Gram i j = CartanMatrix.E 7 (e7Relabel i) (e7Relabel j)
  exact (by decide +kernel : ∀ i j : Fin 7,
    entry e7Gram i j = CartanMatrix.E 7 (e7Relabel i) (e7Relabel j)) i j

end Computations.C21

/-- C21: the Gram matrix of the simple roots is `CartanMatrix.E 7` up to a relabelling. -/
theorem LineSystem.E₇.gram_simpleRoot_eq_cartan : Matrix.gram ℝ LineSystem.E₇.simpleRoot =
    ((CartanMatrix.E 7).submatrix C21.e7Relabel C21.e7Relabel).map (Int.cast : ℤ → ℝ) := by
  rw [LineSystem.E₇.gram_simpleRoot, ← C21.e7_gram_eq_cartan]
  rfl
