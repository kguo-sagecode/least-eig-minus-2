/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C21E8Data
import LineGraphs.Computations.C20Data
import LineGraphs.Computations.C4E8
import LineGraphs.Computations.SimpleRootCertificates
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# C21 E₈ simple-root basis

C21: the simple-root basis of E₈ and its Gram determinant. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C21

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the scaled LDL factorization of the E₈ Gram matrix
checks. -/
theorem e8_ldl_checked : checkScaledLDL 8 16 e8Gram e8Lower e8Diagonal = true := by
  decide +kernel

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the E₈ Gram determinant is 1. -/
theorem e8_gram_det : (toMatrix (R := ℤ) 8 e8Gram).det = 1 := by
  have hl : (toMatrix (R := ℤ) 8 e8Lower).IsLowerTriangular := by
    intro i j hij
    exact (by decide +kernel : ∀ i j : Fin 8, i < j → entry e8Lower i j = 0) i j hij
  have hd : (toMatrix (R := ℤ) 8 e8Lower).det = 2 ^ 8 := by
    rw [Matrix.det_of_isLowerTriangular _ hl]
    decide +kernel
  have he := congrArg Matrix.det (checkScaledLDL_sound e8_ldl_checked)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, hd] at he
  have hp : (∏ i : Fin 8, e8Diagonal[i.val]?.getD 0) = 65536 := by decide +kernel
  rw [hp] at he
  norm_num at he
  omega

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: every E₈ root has the certified integral
coordinates. -/
theorem e8_coordinates_checked :
    checkRootCoordinates 240 8 8 C20.e8Roots e8Simple e8Coefficients = true := by
  decide +kernel

end Computations.C21

namespace LineSystem

/-- The simple roots specified by the Sage C21 certificate, with squared norm two. -/
noncomputable def E₈.simpleRoot (i : Fin 8) : EuclideanSpace ℝ (Fin 8) :=
  integerVector (1 / 2) (fun j => entry C21.e8Simple i j)

-- Computation C21
/-- Computation C21 for Remark 4.14 of [CGSS]: the chosen simple roots belong to E₈. -/
theorem E₈.simpleRoot_mem (i : Fin 8) : E₈.simpleRoot i ∈ E₈.Φ := by
  apply (integerVector_mem_E₈_iff _).mpr
  exact (by decide +kernel : ∀ i : Fin 8,
    isE₈Root (fun j => entry C21.e8Simple i j) = true) i

/-- The Gram matrix of the actual normalized roots is the certified Cartan matrix. -/
theorem E₈.gram_simpleRoot : Matrix.gram ℝ E₈.simpleRoot =
    toMatrix (R := ℝ) 8 C21.e8Gram := by
  ext i j
  change ⟪integerVector (1 / 2) (fun t => entry C21.e8Simple i t),
    integerVector (1 / 2) (fun t => entry C21.e8Simple j t)⟫ = _
  rw [inner_integerVector]
  have he := (by decide +kernel : ∀ i j : Fin 8,
    integerInner (fun t : Fin 8 => entry C21.e8Simple i t)
      (fun t => entry C21.e8Simple j t) = 4 * entry C21.e8Gram i j) i j
  rw [he]
  norm_num [toMatrix]
  ring

/-- C21: the Gram determinant of the simple roots. -/
theorem E₈.det_gram_simpleRoot : (Matrix.gram ℝ E₈.simpleRoot).det = 1 := by
  rw [E₈.gram_simpleRoot, det_toMatrix_real, C21.e8_gram_det]
  norm_num

/-- The simple roots, considered in the real root span. -/
noncomputable def E₈.simpleRootInSpan (i : Fin 8) : Submodule.span ℝ E₈.Φ :=
  ⟨E₈.simpleRoot i, Submodule.subset_span (E₈.simpleRoot_mem i)⟩

/-- C21: the certified simple roots form a basis of the root span. -/
noncomputable def E₈.simpleBasis : Module.Basis (Fin 8) ℝ (Submodule.span ℝ E₈.Φ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (Matrix.linearIndependent_of_det_gram_ne_zero (v := E₈.simpleRootInSpan) (by
      change (Matrix.gram ℝ E₈.simpleRoot).det ≠ 0
      rw [E₈.det_gram_simpleRoot]
      norm_num)) (by rw [finrank_span_E₈]; exact Fintype.card_fin 8)

@[simp] theorem E₈.simpleBasis_apply (i : Fin 8) :
    (E₈.simpleBasis i : EuclideanSpace ℝ (Fin 8)) = E₈.simpleRoot i := by
  simp [simpleBasis, coe_basisOfLinearIndependentOfCardEqFinrank, simpleRootInSpan]

/-- C21: every root has integral simple-root coordinates, all of one sign. -/
theorem E₈.exists_simpleRoot_coordinates {r} (hr : r ∈ E₈.Φ) :
    ∃ z : Fin 8 → ℤ, ((∀ i, 0 ≤ z i) ∨ (∀ i, z i ≤ 0)) ∧
      r = ∑ i, (z i : ℝ) • E₈.simpleRoot i := by
  rw [E₈.tableModel.Φ_eq] at hr
  obtain ⟨a, rfl⟩ := hr
  change Fin 240 at a
  have hc := checkRootCoordinates_sound C21.e8_coordinates_checked a
  refine ⟨fun i => entry C21.e8Coefficients a i, hc.1, ?_⟩
  have he : E₈.tableModel.v a = fun j : Fin 8 =>
      ∑ i : Fin 8, entry C21.e8Coefficients a i * entry C21.e8Simple i j := by
    funext j
    exact hc.2 j
  change integerVector (1 / 2) (E₈.tableModel.v a) = _
  rw [he, integerVector_sum]
  rfl

end LineSystem

namespace Computations.C21

/-- The relabelling of the simple roots of `E₈` onto Mathlib's order of `CartanMatrix.E 8`
(Bourbaki's numbering): `e8Gram i j = CartanMatrix.E 8 (e8Relabel i) (e8Relabel j)`. -/
def e8Relabel : Fin 8 ≃ Fin 8 :=
  ⟨![1, 2, 3, 4, 5, 6, 7, 0], ![7, 0, 1, 2, 3, 4, 5, 6], by decide, by decide⟩

/-- C21: the certified Gram matrix is Mathlib's Cartan matrix `CartanMatrix.E 8`, up to the
relabelling `e8Relabel`. -/
theorem e8_gram_eq_cartan :
    toMatrix (R := ℤ) 8 e8Gram = (CartanMatrix.E 8).submatrix e8Relabel e8Relabel := by
  ext i j
  change entry e8Gram i j = CartanMatrix.E 8 (e8Relabel i) (e8Relabel j)
  exact (by decide +kernel : ∀ i j : Fin 8,
    entry e8Gram i j = CartanMatrix.E 8 (e8Relabel i) (e8Relabel j)) i j

end Computations.C21

/-- C21: the Gram matrix of the simple roots is `CartanMatrix.E 8` up to a relabelling. -/
theorem LineSystem.E₈.gram_simpleRoot_eq_cartan : Matrix.gram ℝ LineSystem.E₈.simpleRoot =
    ((CartanMatrix.E 8).submatrix C21.e8Relabel C21.e8Relabel).map (Int.cast : ℤ → ℝ) := by
  rw [LineSystem.E₈.gram_simpleRoot, ← C21.e8_gram_eq_cartan]
  rfl
