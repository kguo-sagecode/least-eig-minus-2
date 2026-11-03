/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.EvenLattice
import LineGraphs.RootSetClassification.MinimalBase
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# The explicit E basis and its inverse coordinate map

Steps `rEcoefficient`, `rElattice`, and `rEgram` of `lem:E` in the blueprint
for Remark 3.11 of [CGSS]. The simple roots have exactly the order of `eq:E-base`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- Twice the E simple roots in `eq:E-base` of Remark 3.11, in their prescribed order. -/
def eSimpleEntries : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, -1, -1, -1, -1, -1, -1, 1;
     2, 2, 0, 0, 0, 0, 0, 0;
     -2, 2, 0, 0, 0, 0, 0, 0;
     0, -2, 2, 0, 0, 0, 0, 0;
     0, 0, -2, 2, 0, 0, 0, 0;
     0, 0, 0, -2, 2, 0, 0, 0;
     0, 0, 0, 0, -2, 2, 0, 0;
     0, 0, 0, 0, 0, -2, 2, 0]

/-- The E₈ simple-root family of `eq:E-base` in Remark 3.11. -/
noncomputable def E₈.simpleRoot (i : Fin 8) : EuclideanSpace ℝ (Fin 8) :=
  LineSystem.integerVector (1 / 2) (eSimpleEntries i)

/-- The inverse formulas `eq:E-coeff` in step `rEcoefficient` of Remark 3.11. -/
noncomputable def eCoefficients (x : EuclideanSpace ℝ (Fin 8)) : Fin 8 → ℝ :=
  ![2 * x 7,
    (∑ i, x i) / 2 + 2 * x 7,
    (∑ i, x i) / 2 + 3 * x 7 - x 0,
    x 2 + x 3 + x 4 + x 5 + x 6 + 5 * x 7,
    x 3 + x 4 + x 5 + x 6 + 4 * x 7,
    x 4 + x 5 + x 6 + 3 * x 7,
    x 5 + x 6 + 2 * x 7,
    x 6 + x 7]

/-- Steps `rEcoord8`--`rEcoord7`: the displayed coefficients reconstruct every vector. -/
theorem sum_eCoefficients_simpleRoot (x : EuclideanSpace ℝ (Fin 8)) :
    ∑ i, eCoefficients x i • E₈.simpleRoot i = x := by
  ext j
  fin_cases j <;>
    simp [eCoefficients, E₈.simpleRoot, eSimpleEntries, LineSystem.integerVector,
      Fin.sum_univ_succ] <;> ring

/-- Step `rEunique`: applying the coefficient map to a combination recovers its coefficients. -/
theorem eCoefficients_sum_simpleRoot (c : Fin 8 → ℝ) :
    eCoefficients (∑ i, c i • E₈.simpleRoot i) = c := by
  funext j
  fin_cases j <;>
    simp [eCoefficients, E₈.simpleRoot, eSimpleEntries, LineSystem.integerVector,
      Fin.sum_univ_succ] <;> ring

/-- Step `rEunique`: the E₈ simple roots are linearly independent. -/
theorem E₈.simpleRoot_linearIndependent : LinearIndependent ℝ E₈.simpleRoot := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he := congrFun (eCoefficients_sum_simpleRoot c) i
  rw [hc] at he
  fin_cases i <;> simpa [eCoefficients] using he.symm

/-- Step `rEsubspaces`: the full E basis spans the eight-dimensional coordinate space. -/
theorem span_E₈_simpleRoot : span ℝ (Set.range E₈.simpleRoot) = ⊤ := by
  apply top_unique
  intro x _
  rw [← sum_eCoefficients_simpleRoot x]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (Set.mem_range_self i))

/-- The real E₈ basis in `rEsubspaces` of Remark 3.11. -/
noncomputable def E₈.simpleBasis : Module.Basis (Fin 8) ℝ (EuclideanSpace ℝ (Fin 8)) :=
  Module.Basis.mk E₈.simpleRoot_linearIndependent span_E₈_simpleRoot.ge

/-- The basis in `rEsubspaces` has the prescribed vectors of `eq:E-base`. -/
@[simp] theorem E₈.simpleBasis_apply (i : Fin 8) : E₈.simpleBasis i = E₈.simpleRoot i :=
  Module.Basis.mk_apply _ _ _

/-- Step `rEsimple`: the eight displayed roots belong to the E₈ coordinate list. -/
theorem E₈.simpleRoot_mem (i : Fin 8) : E₈.simpleRoot i ∈ E₈ := by
  have he : ∀ i : Fin 8, ∃ a : LineSystem.E₈Index,
      LineSystem.e₈Root a = eSimpleEntries i := by decide +kernel
  obtain ⟨a, ha⟩ := he i
  exact ⟨a, congrArg (LineSystem.integerVector (1 / 2)) ha⟩

/-- Step `rEgram`: the prescribed E₈ order gives Mathlib's matrix without a relabelling. -/
theorem E₈.gram_simpleRoot (i j : Fin 8) :
    ⟪E₈.simpleRoot i, E₈.simpleRoot j⟫ = (CartanMatrix.E 8 i j : ℝ) := by
  have he : ∀ i j : Fin 8, LineSystem.integerInner (eSimpleEntries i) (eSimpleEntries j) =
      4 * CartanMatrix.E 8 i j := by decide +kernel
  rw [E₈.simpleRoot, E₈.simpleRoot, LineSystem.inner_integerVector, he]
  push_cast
  ring

/-- Steps `rEint0`--`rEintk`: the integral inverse formulas on the integer coset. -/
def eIntegerCoefficients (v : Fin 8 → ℤ) (k : ℤ) : Fin 8 → ℤ :=
  ![2 * v 7, k + 2 * v 7, k + 3 * v 7 - v 0,
    v 2 + v 3 + v 4 + v 5 + v 6 + 5 * v 7,
    v 3 + v 4 + v 5 + v 6 + 4 * v 7,
    v 4 + v 5 + v 6 + 3 * v 7, v 5 + v 6 + 2 * v 7, v 6 + v 7]

/-- Step `rElattice`: coefficients of the integer even-sum coset are integers. -/
theorem eCoefficients_integerVector (v : Fin 8 → ℤ) {k : ℤ} (hk : ∑ i, v i = k + k)
    (i : Fin 8) : eCoefficients (LineSystem.integerVector 1 v) i =
      (eIntegerCoefficients v k i : ℝ) := by
  have hs : (∑ i, (v i : ℝ)) = (k : ℝ) + k := by exact_mod_cast hk
  fin_cases i <;>
    simp [eCoefficients, eIntegerCoefficients, LineSystem.integerVector, hs]

/-- The coefficient map in `rEcoefficient` is additive. -/
theorem eCoefficients_add (x y : EuclideanSpace ℝ (Fin 8)) :
    eCoefficients (x + y) = eCoefficients x + eCoefficients y := by
  funext i
  fin_cases i <;> simp [eCoefficients, Finset.sum_add_distrib] <;> ring

/-- Step `rElattice`: the half-coordinate shift has integral simple-root coefficients. -/
theorem eCoefficients_halfShift : eCoefficients halfShift =
    fun i ↦ ((![1, 3, 3, 5, 4, 3, 2, 1] i : ℤ) : ℝ) := by
  funext i
  fin_cases i <;> norm_num [eCoefficients, halfShift, Fin.sum_univ_succ]

/-- Step `rElattice`: every E₈ lattice vector has integral coefficients in `eq:E-coeff`. -/
theorem exists_integer_eCoefficients {x : EuclideanSpace ℝ (Fin 8)} (hx : x ∈ e₈Lattice) :
    ∃ c : Fin 8 → ℤ, ∀ i, eCoefficients x i = (c i : ℝ) := by
  rcases hx with hx | hx
  · obtain ⟨v, ⟨k, hk⟩, rfl⟩ := hx
    exact ⟨eIntegerCoefficients v k, eCoefficients_integerVector v hk⟩
  · obtain ⟨v, ⟨k, hk⟩, he⟩ := hx
    have he' : x = LineSystem.integerVector 1 v + halfShift := sub_eq_iff_eq_add.mp he
    refine ⟨fun i ↦ eIntegerCoefficients v k i + ![1, 3, 3, 5, 4, 3, 2, 1] i, fun i ↦ ?_⟩
    rw [he', eCoefficients_add, Pi.add_apply, eCoefficients_integerVector v hk,
      eCoefficients_halfShift]
    simp

/-- Step `rEsubspaces`: the E₈ simple roots generate exactly the lattice over the integers. -/
theorem mem_e₈Lattice_iff_exists_coefficients (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ e₈Lattice ↔ ∃ c : Fin 8 → ℤ, x = ∑ i, (c i : ℝ) • E₈.simpleBasis i := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_integer_eCoefficients hx
    refine ⟨c, ?_⟩
    simpa only [E₈.simpleBasis_apply, hc] using (sum_eCoefficients_simpleRoot x).symm
  · rintro ⟨c, rfl⟩
    apply e₈Lattice.sum_mem
    intro i _
    rw [E₈.simpleBasis_apply, Int.cast_smul_eq_zsmul ℝ]
    exact e₈Lattice.zsmul_mem (E₈_subset_e₈Lattice (E₈.simpleRoot_mem i)) _

end RootSetModel
