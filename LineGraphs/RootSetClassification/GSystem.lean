/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.GCoordinates
import LineGraphs.RootSetClassification.ClassicalCartan

/-!
# The G₂ root set and prescribed base

The conclusion of `lem:G` in the blueprint for Remark 3.11 of [CGSS]. The
coefficient map gives the six positive pairs in `eq:G-coeff`, proves spanning
of the zero-sum plane, and gives linear independence of the two simple roots.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- The simple-root coordinates in `eq:G-base` of Remark 3.11. -/
def gSimpleEntries : Matrix (Fin 2) (Fin 3) ℤ := !![1, -2, 1; 0, 1, -1]

/-- The simple roots of `eq:G-base`, as elements of the zero-sum plane. -/
noncomputable def G₂.simpleRoot (i : Fin 2) : g₂Space :=
  ⟨LineSystem.integerVector 1 (gSimpleEntries i), by
    have h : ∀ i : Fin 2, ∑ j, gSimpleEntries i j = 0 := by decide +kernel
    change (∑ j, (LineSystem.integerVector 1 (gSimpleEntries i)) j) = 0
    simp [LineSystem.integerVector, ← Int.cast_sum, h]⟩

/-- The inverse coordinate map for the prescribed base in step `rGcoeff`. -/
noncomputable def gCoefficients (x : g₂Space) : Fin 2 → ℝ :=
  ![x.val 0, 2 * x.val 0 + x.val 1]

/-- Step `rGspan`: the two simple roots reconstruct every vector of the zero-sum plane. -/
theorem sum_gCoefficients_simpleRoot (x : g₂Space) :
    ∑ i, gCoefficients x i • G₂.simpleRoot i = x := by
  apply Subtype.ext
  ext j
  have hx := (mem_g₂Space x).mp x.property
  fin_cases j <;>
    simp [gCoefficients, G₂.simpleRoot, gSimpleEntries, LineSystem.integerVector,
      Fin.sum_univ_succ] <;> linarith

/-- The coefficient inverse for step `rGindependent` of Remark 3.11. -/
theorem gCoefficients_sum_simpleRoot (c : Fin 2 → ℝ) :
    gCoefficients (∑ i, c i • G₂.simpleRoot i) = c := by
  funext i
  fin_cases i <;> simp [gCoefficients, G₂.simpleRoot, gSimpleEntries,
    LineSystem.integerVector, Fin.sum_univ_succ]
  ring

/-- Step `rGindependent`: the two prescribed roots are linearly independent. -/
theorem G₂.simpleRoot_linearIndependent : LinearIndependent ℝ G₂.simpleRoot := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrFun (gCoefficients_sum_simpleRoot c) i
  rw [hc] at he
  fin_cases i <;> simpa [gCoefficients] using he.symm

/-- The membership of the two roots in `eq:G-base`. -/
theorem G₂.simpleRoot_mem (i : Fin 2) : G₂.simpleRoot i ∈ G₂ := by
  have h : ∀ i : Fin 2, ∃ a : G₂Index, gRootEntries a = gSimpleEntries i := by
    decide +kernel
  obtain ⟨a, ha⟩ := h i
  rw [G₂_eq_range]
  exact ⟨a, Subtype.ext (congrArg (LineSystem.integerVector 1) ha)⟩

/-- The spanning assertion in step `rGspan` of Remark 3.11. -/
theorem span_G₂_simpleRoot : span ℝ (Set.range G₂.simpleRoot) = ⊤ := by
  apply top_unique
  intro x _
  rw [← sum_gCoefficients_simpleRoot x]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (Set.mem_range_self i))

-- Remark 3.11, lem:G
/-- The root-set assertion of `lem:G` in Remark 3.11 of [CGSS]. -/
theorem G₂_isRootSet : IsRootSet G₂ where
  finite := by rw [G₂_eq_range]; exact Set.finite_range _
  zero_notMem := by
    intro h
    have hn := gRoots_inner_self h
    simp at hn
  span_eq_top := by
    apply top_unique
    rw [← span_G₂_simpleRoot]
    exact span_mono (Set.range_subset_iff.mpr G₂.simpleRoot_mem)
  crystallographic := fun _ hr s hs ↦ gRoots_crystallographic hr s hs
  reduced := fun _ hr t ht ↦ gRoots_reduced hr t ht
  reflection_mem := fun _ hr s hs ↦ gRoots_reflection_mem hr s hs

/-- The integer coefficients in step `rGcoeff` of Remark 3.11. -/
def gIntegerCoefficients (a : G₂Index) : Fin 2 → ℤ :=
  ![gRootEntries a 0, 2 * gRootEntries a 0 + gRootEntries a 1]

/-- The six positive coefficient pairs of `eq:G-coeff` in Remark 3.11. -/
def gPositiveCoefficients : Matrix (Fin 6) (Fin 2) ℤ :=
  !![0, 1; 1, 1; 1, 2; 1, 0; 1, 3; 2, 3]

/-- Steps `rGc01`--`rGc23`: the six displayed pairs exhaust all roots up to sign. -/
theorem gIntegerCoefficients_eq_signed_positive : ∀ a : G₂Index, ∃ i : Fin 6,
    gIntegerCoefficients a = gPositiveCoefficients i ∨
      gIntegerCoefficients a = -gPositiveCoefficients i := by
  intro a
  fin_cases a
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨1, by decide +kernel⟩
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨0, by decide +kernel⟩
  · exact ⟨5, by decide +kernel⟩
  · exact ⟨5, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨3, by decide +kernel⟩
  · exact ⟨4, by decide +kernel⟩
  · exact ⟨4, by decide +kernel⟩

/-- The one-sign assertion of step `rGcoeff` of Remark 3.11. -/
theorem gIntegerCoefficients_one_sign (a : G₂Index) :
    (∀ i, 0 ≤ gIntegerCoefficients a i) ∨ (∀ i, gIntegerCoefficients a i ≤ 0) := by
  have h : ∀ i : Fin 6, ∀ j : Fin 2, 0 ≤ gPositiveCoefficients i j := by
    intro i
    fin_cases i <;> decide +kernel
  obtain ⟨i, hi | hi⟩ := gIntegerCoefficients_eq_signed_positive a
  · exact Or.inl (fun j ↦ hi ▸ h i j)
  · right
    intro j
    rw [hi]
    exact neg_nonpos.mpr (h i j)

/-- Step `rGcoeff` of `lem:G` in Remark 3.11: the real and integer coefficient maps
coincide on the G₂ roots. -/
theorem gCoefficients_root (a : G₂Index) (i : Fin 2) :
    gCoefficients (gRoot a) i = (gIntegerCoefficients a i : ℝ) := by
  fin_cases i <;> simp [gCoefficients, gIntegerCoefficients, gRoot, LineSystem.integerVector]

-- Remark 3.11, lem:G
/-- The root-base assertion of `lem:G` in Remark 3.11 of [CGSS]. -/
theorem G₂_base : G₂_isRootSet.IsBase G₂.simpleRoot := by
  refine ⟨G₂.simpleRoot_mem, G₂.simpleRoot_linearIndependent, fun r hr ↦ ?_⟩
  rw [G₂_eq_range] at hr
  obtain ⟨a, rfl⟩ := hr
  refine ⟨gIntegerCoefficients a, gIntegerCoefficients_one_sign a, ?_⟩
  simpa only [gCoefficients_root] using (sum_gCoefficients_simpleRoot (gRoot a)).symm

/-- Step `rGmatrix`: the prescribed simple Gram matrix has diagonal 6, 2 and off-diagonal -3. -/
theorem G₂.gram_simpleRoot (i j : Fin 2) :
    ⟪G₂.simpleRoot i, G₂.simpleRoot j⟫ = (!![6, -3; -3, 2] i j : ℝ) := by
  change ⟪LineSystem.integerVector 1 (gSimpleEntries i),
    LineSystem.integerVector 1 (gSimpleEntries j)⟫ = _
  rw [LineSystem.inner_integerVector]
  fin_cases i <;> fin_cases j <;>
    norm_num [gSimpleEntries, LineSystem.integerInner, dotProduct, Fin.sum_univ_succ]

-- Remark 3.11, lem:G
/-- The Cartan-matrix assertion of `lem:G` in Remark 3.11 of [CGSS]. -/
theorem G₂_cartanMatrix (i j : Fin 2) :
    IsRootSet.cartanPairing G₂.simpleRoot i j = (CartanMatrix.G₂ i j : ℝ) := by
  simp only [IsRootSet.cartanPairing, G₂.gram_simpleRoot]
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.G₂]

end RootSetModel
