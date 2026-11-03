/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.FCoordinates
import LineGraphs.RootSetClassification.ClassicalCartan

/-!
# The F₄ root set and its prescribed base

Steps `rFintegrality`--`rFmatrix` of `lem:F` in the blueprint for Remark 3.11
of [CGSS]. Integer coordinate calculations check the pairings and the one-sign
coefficient formulas. All finite checks are evaluated by the Lean kernel.
-/

open scoped RealInnerProductSpace

namespace RootSetModel

/-- The integer quotient for the pairings in step `rFintegrality` of Remark 3.11. -/
def fPairing (a b : F₄Index) : ℤ :=
  2 * LineSystem.integerInner (fRootEntries a) (fRootEntries b) /
    LineSystem.integerInner (fRootEntries a) (fRootEntries a)

/-- Steps `rFpairlongint`--`rFpairhalfhalf`: the quotient has no remainder in all patterns. -/
theorem fPairing_mul : ∀ a b : F₄Index,
    fPairing a b * LineSystem.integerInner (fRootEntries a) (fRootEntries a) =
      2 * LineSystem.integerInner (fRootEntries a) (fRootEntries b) := by
  decide +kernel

/-- The integrality assertion `rFintegrality` of Remark 3.11. -/
theorem F₄_crystallographic {r s : EuclideanSpace ℝ (Fin 4)}
    (hr : r ∈ F₄) (hs : s ∈ F₄) : ∃ z : ℤ, (z : ℝ) = 2 * ⟪r, s⟫ / ⟪r, r⟫ := by
  have hr0 : ⟪r, r⟫ ≠ 0 := by
    rcases F₄_inner_self hr with h | h <;> rw [h] <;> norm_num
  rw [F₄_eq_range] at hr hs
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := hs
  refine ⟨fPairing a b, (eq_div_iff hr0).mpr ?_⟩
  rw [LineSystem.inner_integerVector, LineSystem.inner_integerVector]
  have he : (fPairing a b : ℝ) *
      (LineSystem.integerInner (fRootEntries a) (fRootEntries a) : ℝ) =
      2 * (LineSystem.integerInner (fRootEntries a) (fRootEntries b) : ℝ) := by
    exact_mod_cast fPairing_mul a b
  nlinarith

-- Remark 3.11, lem:F
/-- The root-set assertion of `lem:F` in Remark 3.11 of [CGSS]. -/
theorem F₄_isRootSet : IsRootSet F₄ where
  finite := F₄_finite
  zero_notMem := F₄_zero_notMem
  span_eq_top := span_F₄_eq_top
  crystallographic := fun _ hr _ hs ↦ F₄_crystallographic hr hs
  reduced := fun _ hr t ht ↦ F₄_reduced hr t ht
  reflection_mem := fun _ hr _ hs ↦ F₄_reflection_mem hr hs

/-- Twice the simple-root coordinates of `eq:F-base` in Remark 3.11. -/
def fSimpleEntries : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 2, -2, 0; 0, 0, 2, -2; 0, 0, 0, 2; 1, -1, -1, -1]

/-- The prescribed F₄ base of `eq:F-base` in Remark 3.11. -/
noncomputable def F₄.simpleRoot (i : Fin 4) : EuclideanSpace ℝ (Fin 4) :=
  LineSystem.integerVector (1 / 2) (fSimpleEntries i)

/-- The inverse coefficient formula `eq:F-coeff` in Remark 3.11. -/
noncomputable def fCoefficients (x : EuclideanSpace ℝ (Fin 4)) : Fin 4 → ℝ :=
  ![x 0 + x 1, 2 * x 0 + x 1 + x 2, 3 * x 0 + x 1 + x 2 + x 3, 2 * x 0]

/-- Steps `rFcoord1`--`rFcoord4`: the coefficient formulas reconstruct every vector. -/
theorem sum_fCoefficients_simpleRoot (x : EuclideanSpace ℝ (Fin 4)) :
    ∑ i, fCoefficients x i • F₄.simpleRoot i = x := by
  ext j
  fin_cases j <;> simp [fCoefficients, F₄.simpleRoot, fSimpleEntries,
    LineSystem.integerVector, Fin.sum_univ_succ] <;> ring

/-- Step `rFcoeff`: the inverse formula also recovers coefficients of a combination. -/
theorem fCoefficients_sum_simpleRoot (c : Fin 4 → ℝ) :
    fCoefficients (∑ i, c i • F₄.simpleRoot i) = c := by
  funext j
  fin_cases j <;> simp [fCoefficients, F₄.simpleRoot, fSimpleEntries,
    LineSystem.integerVector, Fin.sum_univ_succ] <;> ring

/-- Step `rFbaseindependent`: the explicit inverse proves linear independence. -/
theorem F₄.simpleRoot_linearIndependent : LinearIndependent ℝ F₄.simpleRoot := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrFun (fCoefficients_sum_simpleRoot c) i
  rw [hc] at he
  fin_cases i <;> simpa [fCoefficients] using he.symm

/-- The membership assertion in step `rFbase` of Remark 3.11. -/
theorem F₄.simpleRoot_mem (i : Fin 4) : F₄.simpleRoot i ∈ F₄ := by
  have h : ∀ i : Fin 4, ∃ a : F₄Index, fRootEntries a = fSimpleEntries i := by
    decide +kernel
  obtain ⟨a, ha⟩ := h i
  rw [F₄_eq_range]
  exact ⟨a, congrArg (LineSystem.integerVector (1 / 2)) ha⟩

/-- The integer numerators of `eq:F-coeff`, applied to doubled root coordinates. -/
def fCoefficientNumerators (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![v 0 + v 1, 2 * v 0 + v 1 + v 2, 3 * v 0 + v 1 + v 2 + v 3, 2 * v 0]

/-- The integral simple-root coefficients in step `rFbase` of Remark 3.11. -/
def fIntegerCoefficients (a : F₄Index) (i : Fin 4) : ℤ :=
  fCoefficientNumerators (fRootEntries a) i / 2

/-- Steps `rFbasehalf`, `rFbasefirst`, and `rFbasezero`: all coefficients are integers
of one sign, as seen in the three coordinate patterns. -/
theorem fIntegerCoefficients_spec : ∀ a : F₄Index,
    (∀ i, 2 * fIntegerCoefficients a i = fCoefficientNumerators (fRootEntries a) i) ∧
    ((∀ i, 0 ≤ fIntegerCoefficients a i) ∨ (∀ i, fIntegerCoefficients a i ≤ 0)) := by
  decide +kernel

/-- The coefficient formulas in `rFbase` agree with their integer values on roots. -/
theorem fCoefficients_root (a : F₄Index) (i : Fin 4) :
    fCoefficients (LineSystem.integerVector (1 / 2) (fRootEntries a)) i =
      (fIntegerCoefficients a i : ℝ) := by
  have he : 2 * (fIntegerCoefficients a i : ℝ) =
      (fCoefficientNumerators (fRootEntries a) i : ℝ) := by
    exact_mod_cast (fIntegerCoefficients_spec a).1 i
  fin_cases i <;>
    dsimp [fCoefficients, fCoefficientNumerators, LineSystem.integerVector] at * <;>
    push_cast at he <;> linarith

-- Remark 3.11, lem:F
/-- The prescribed root-base assertion of `lem:F` in Remark 3.11 of [CGSS]. -/
theorem F₄_base : F₄_isRootSet.IsBase F₄.simpleRoot := by
  refine ⟨F₄.simpleRoot_mem, F₄.simpleRoot_linearIndependent, fun r hr ↦ ?_⟩
  rw [F₄_eq_range] at hr
  obtain ⟨a, rfl⟩ := hr
  refine ⟨fIntegerCoefficients a, (fIntegerCoefficients_spec a).2, ?_⟩
  simpa only [fCoefficients_root] using
    (sum_fCoefficients_simpleRoot (LineSystem.integerVector (1 / 2) (fRootEntries a))).symm

/-- Step `rFmatrix`: the squared lengths of the simple roots are 2, 2, 1, 1. -/
theorem F₄.simpleRoot_inner_self (i : Fin 4) :
    ⟪F₄.simpleRoot i, F₄.simpleRoot i⟫ = (![2, 2, 1, 1] i : ℝ) := by
  rw [F₄.simpleRoot, LineSystem.inner_integerVector]
  fin_cases i <;>
    norm_num [fSimpleEntries, LineSystem.integerInner, dotProduct, Fin.sum_univ_succ]

-- Remark 3.11, lem:F
/-- Steps `rFgram01`--`rFgram13` and `rFmatrix`: the prescribed base has Cartan matrix F₄. -/
theorem F₄_cartanMatrix (i j : Fin 4) :
    IsRootSet.cartanPairing F₄.simpleRoot i j = (CartanMatrix.F₄ i j : ℝ) := by
  simp only [IsRootSet.cartanPairing, F₄.simpleRoot, LineSystem.inner_integerVector]
  fin_cases i <;> fin_cases j <;>
    norm_num [fSimpleEntries, LineSystem.integerInner, dotProduct,
      Fin.sum_univ_succ, CartanMatrix.F₄]

end RootSetModel
