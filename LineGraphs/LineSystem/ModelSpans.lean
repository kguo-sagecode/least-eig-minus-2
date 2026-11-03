/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Models

/-!
# Dimensions of the spans of the explicit models

The C6 frame identity must be stated for `x ∈ Submodule.span ℝ S.Φ`. In the ambient
space its right hand side is a scalar times the orthogonal projection onto this span.
Specifically, C6 asks for `∑ r ∈ S.finite.toFinset, ⟪r, x⟫ • r =
(4 * S.numLines / finrank ℝ (Submodule.span ℝ S.Φ) : ℝ) • x` for `x` in the span.
The A and exceptional subsystem models do not span their ambient coordinate spaces.
-/

open scoped RealInnerProductSpace
open Finset Module Submodule

namespace LineSystem

/-- A coordinate projection and explicit preimages of its unit vectors compute dimension. -/
theorem finrank_eq_of_coordinate_basis {n k : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (coord : Fin k → Fin n)
    (b : Fin k → EuclideanSpace ℝ (Fin n)) (hb : ∀ i, b i ∈ U)
    (hcoord : ∀ i j, b i (coord j) = if i = j then 1 else 0)
    (hzero : ∀ x ∈ U, (∀ i, x (coord i) = 0) → x = 0) : finrank ℝ U = k := by
  let f : U →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun x i ↦ x.val (coord i)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply hzero (x.val - y.val) (U.sub_mem x.property y.property)
      intro i
      exact sub_eq_zero.mpr (congrFun h i)
    · intro y
      refine ⟨⟨∑ i, y i • b i, U.sum_mem (fun i _ ↦ U.smul_mem _ (hb i))⟩, ?_⟩
      ext j
      change (∑ i, y i • b i) (coord j) = y j
      simp [hcoord]
  simpa using (LinearEquiv.ofBijective f hf).finrank_eq

/-- Two signed pair roots recover a coordinate axis in their span. -/
theorem single_mem_span_of_pairs {n : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (i j : Fin n)
    (hp : EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 ∈ U)
    (hm : EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈ U) :
    EuclideanSpace.single i (1 : ℝ) ∈ U := by
  have h := U.smul_mem (1 / 2 : ℝ) (U.add_mem hp hm)
  convert h using 1
  module

/-- Every coordinate axis lies in the span of Dₙ once two coordinates are available. -/
theorem single_mem_span_Dn {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    EuclideanSpace.single i (1 : ℝ) ∈ span ℝ (Dn n).Φ := by
  let j : Fin n := if i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hij : i ≠ j := by dsimp [j]; split_ifs <;> simp_all
  exact single_mem_span_of_pairs _ i j
    (subset_span (add_single_mem_Dn i j hij)) (subset_span (sub_single_mem_Dn i j hij))

/-- Dₙ spans the whole ambient space, including the reducible case `n = 2`. -/
theorem span_Dn_eq_top {n : ℕ} (hn : 2 ≤ n) : span ℝ (Dn n).Φ = ⊤ := by
  apply top_unique
  intro x _
  have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hx]
  exact sum_mem (fun i _ ↦ smul_mem _ _ (single_mem_span_Dn hn i))

theorem finrank_span_Dn {n : ℕ} (hn : 2 ≤ n) : finrank ℝ (span ℝ (Dn n).Φ) = n := by
  rw [span_Dn_eq_top hn]
  simp

theorem span_E₈_eq_top : span ℝ E₈.Φ = ⊤ := by
  apply top_unique
  rw [← span_Dn_eq_top (by decide : 2 ≤ 8)]
  exact span_mono Dn_Φ_subset_E₈

theorem finrank_span_E₈ : finrank ℝ (span ℝ E₈.Φ) = 8 := by
  rw [span_E₈_eq_top]
  simp

/-- The sum of the coordinates, as a linear functional. -/
noncomputable def coordinateSum (n : ℕ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem coordinateSum_integerVector {n : ℕ} (c : ℝ) (w : Fin n → ℤ) :
    coordinateSum n (integerVector c w) = c * ((∑ i, w i : ℤ) : ℝ) := by
  simp [coordinateSum, integerVector, Int.cast_sum, Finset.mul_sum]

theorem sum_anRoot {n : ℕ} (a : An.Index n) : ∑ i, anRoot a i = 0 := by
  simp [anRoot, pairVector, Finset.sum_add_distrib]

theorem sum_tripleRoot (t : TripleIndex) : ∑ i, tripleRoot t i = 0 := by
  have he (i : Fin 9) : tripleRoot t i = 1 - 3 * (if i ∈ t.val then 1 else 0) := by
    simp only [tripleRoot]
    split_ifs <;> norm_num
  simp [he, Finset.sum_sub_distrib, t.property]

theorem span_An_le_ker_coordinateSum (n : ℕ) :
    span ℝ (An n).Φ ≤ LinearMap.ker (coordinateSum (n + 1)) := by
  apply span_le.mpr
  rintro _ ⟨a, rfl⟩
  simp [LinearMap.mem_ker, coordinateSum_integerVector, sum_anRoot]

/-- A hyperplane with all coordinate differences has the expected dimension. -/
theorem finrank_eq_of_coordinate_differences {n : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (hd : ∀ i : Fin n, EuclideanSpace.single i.castSucc (1 : ℝ) -
      EuclideanSpace.single (Fin.last n) 1 ∈ U)
    (hs : U ≤ LinearMap.ker (coordinateSum (n + 1))) : finrank ℝ U = n := by
  apply finrank_eq_of_coordinate_basis U Fin.castSucc
    (fun i ↦ EuclideanSpace.single i.castSucc 1 - EuclideanSpace.single (Fin.last n) 1) hd
  · intro i j
    simp [PiLp.single_apply, eq_comm]
  · intro x hx hzero
    have hsum : ∑ i, x i = 0 := hs hx
    rw [Fin.sum_univ_castSucc] at hsum
    simp only [hzero, Finset.sum_const_zero, zero_add] at hsum
    ext i
    exact Fin.lastCases hsum (fun j ↦ hzero j) i

theorem finrank_span_An (n : ℕ) : finrank ℝ (span ℝ (An n).Φ) = n := by
  apply finrank_eq_of_coordinate_differences _ _ (span_An_le_ker_coordinateSum n)
  intro i
  exact subset_span (sub_single_mem_An _ _ (Fin.castSucc_ne_last i))

theorem span_E₈viaA₈_le_ker_coordinateSum :
    span ℝ E₈viaA₈.Φ ≤ LinearMap.ker (coordinateSum 9) := by
  apply span_le.mpr
  rintro _ ⟨a, rfl⟩
  change coordinateSum 9 (integerVector (1 / 3) (e₈ARoot a)) = 0
  rw [coordinateSum_integerVector]
  rcases a with p | ⟨t, b⟩ <;>
    simp [e₈ARoot, ← Finset.mul_sum, sum_anRoot, sum_tripleRoot]

theorem finrank_span_E₈viaA₈ : finrank ℝ (span ℝ E₈viaA₈.Φ) = 8 := by
  apply finrank_eq_of_coordinate_differences _ _ span_E₈viaA₈_le_ker_coordinateSum
  intro i
  exact subset_span (An_Φ_subset_E₈viaA₈
    (sub_single_mem_An i.castSucc (Fin.last 8) (Fin.castSucc_ne_last i)))

/-- Coordinate equality as a submodule, used for the exceptional restrictions. -/
def equalCoordinates {n : ℕ} (i j : Fin n) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {x | x i = x j}
  zero_mem' := rfl
  add_mem' := fun {x y} hx hy ↦ show x i + y i = x j + y j from congrArg₂ (· + ·) hx hy
  smul_mem' c x hx := show c * x i = c * x j from congrArg (c * ·) hx

theorem mem_orthogonalTo_sub_single_iff {n : ℕ}
    (S : LineSystem (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    x ∈ (S.orthogonalTo (EuclideanSpace.single i 1 - EuclideanSpace.single j 1)).Φ ↔
      x ∈ S.Φ ∧ x i = x j := by
  simp [orthogonalTo, inner_sub_right, EuclideanSpace.inner_single_right, sub_eq_zero]

theorem span_E₇_le_equalCoordinates : span ℝ E₇.Φ ≤ equalCoordinates 6 7 := by
  apply span_le.mpr
  intro x hx
  exact ((mem_orthogonalTo_sub_single_iff E₈ x 6 7).mp hx).2

theorem span_E₆_le_equalCoordinates :
    span ℝ E₆.Φ ≤ equalCoordinates 6 7 ⊓ equalCoordinates 5 6 := by
  apply span_le.mpr
  intro x hx
  have h := (mem_orthogonalTo_sub_single_iff E₇ x 5 6).mp hx
  exact ⟨((mem_orthogonalTo_sub_single_iff E₈ x 6 7).mp h.1).2, h.2⟩

private theorem pairs_mem_E₇ (i j : Fin 8) (hij : i ≠ j) (hi : i.val < 6) (hj : j.val < 6) :
    EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 ∈ E₇.Φ ∧
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈ E₇.Φ := by
  have hi6 : (6 : Fin 8) ≠ i := by intro h; subst i; simp at hi
  have hi7 : (7 : Fin 8) ≠ i := by intro h; subst i; simp at hi
  have hj6 : (6 : Fin 8) ≠ j := by intro h; subst j; simp at hj
  have hj7 : (7 : Fin 8) ≠ j := by intro h; subst j; simp at hj
  constructor
  · apply (mem_orthogonalTo_sub_single_iff E₈ _ 6 7).mpr
    exact ⟨Dn_Φ_subset_E₈ (add_single_mem_Dn i j hij), by simp [*]⟩
  · apply (mem_orthogonalTo_sub_single_iff E₈ _ 6 7).mpr
    exact ⟨Dn_Φ_subset_E₈ (sub_single_mem_Dn i j hij), by simp [*]⟩

private theorem pairs_mem_E₆ (i j : Fin 8) (hij : i ≠ j) (hi : i.val < 5) (hj : j.val < 5) :
    EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 ∈ E₆.Φ ∧
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈ E₆.Φ := by
  have hp := pairs_mem_E₇ i j hij (by omega) (by omega)
  have hi5 : (5 : Fin 8) ≠ i := by intro h; subst i; simp at hi
  have hi6 : (6 : Fin 8) ≠ i := by intro h; subst i; simp at hi
  have hj5 : (5 : Fin 8) ≠ j := by intro h; subst j; simp at hj
  have hj6 : (6 : Fin 8) ≠ j := by intro h; subst j; simp at hj
  constructor
  · exact (mem_orthogonalTo_sub_single_iff E₇ _ 5 6).mpr
      ⟨hp.1, by simp [*]⟩
  · exact (mem_orthogonalTo_sub_single_iff E₇ _ 5 6).mpr
      ⟨hp.2, by simp [*]⟩

theorem single_mem_span_E₇ (i : Fin 8) (hi : i.val < 6) :
    EuclideanSpace.single i (1 : ℝ) ∈ span ℝ E₇.Φ := by
  let j : Fin 8 := if i = 0 then 1 else 0
  have hij : i ≠ j := by dsimp [j]; split_ifs <;> simp_all
  have hj : j.val < 6 := by dsimp [j]; split_ifs <;> decide
  have hp := pairs_mem_E₇ i j hij hi hj
  exact single_mem_span_of_pairs _ i j (subset_span hp.1) (subset_span hp.2)

theorem single_mem_span_E₆ (i : Fin 8) (hi : i.val < 5) :
    EuclideanSpace.single i (1 : ℝ) ∈ span ℝ E₆.Φ := by
  let j : Fin 8 := if i = 0 then 1 else 0
  have hij : i ≠ j := by dsimp [j]; split_ifs <;> simp_all
  have hj : j.val < 5 := by dsimp [j]; split_ifs <;> decide
  have hp := pairs_mem_E₆ i j hij hi hj
  exact single_mem_span_of_pairs _ i j (subset_span hp.1) (subset_span hp.2)

/-- Six coordinate axes and the last positive pair form a basis of the E₇ span. -/
theorem finrank_span_E₇ : finrank ℝ (span ℝ E₇.Φ) = 7 := by
  let b : Fin 7 → EuclideanSpace ℝ (Fin 8) := fun i ↦
    if i.val < 6 then EuclideanSpace.single i.castSucc 1
    else EuclideanSpace.single 6 1 + EuclideanSpace.single 7 1
  apply finrank_eq_of_coordinate_basis _ Fin.castSucc b
  · intro i
    dsimp only [b]
    split_ifs with hi
    · exact single_mem_span_E₇ _ hi
    · apply subset_span
      apply (mem_orthogonalTo_sub_single_iff E₈ _ 6 7).mpr
      exact ⟨Dn_Φ_subset_E₈ (add_single_mem_Dn 6 7 (by decide)), by simp⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [b, Pi.single_apply, Fin.ext_iff]
  · intro x hx hz
    have he : x 6 = x 7 := span_E₇_le_equalCoordinates hx
    ext i
    fin_cases i
    all_goals first | exact hz ⟨_, by decide⟩ | exact he ▸ hz 6

private theorem ones_mem_span_E₆ : (WithLp.toLp 2 (fun _ : Fin 8 ↦ (1 : ℝ))) ∈
    span ℝ E₆.Φ := by
  have hr : integerVector (1 / 2) (halfRoot (fun _ ↦ false)) ∈ E₆.Φ := by
    rw [E₆_roots_eq_range]
    exact ⟨⟨Sum.inr (fun _ ↦ false), by decide⟩, rfl⟩
  have h := (span ℝ E₆.Φ).smul_mem (2 : ℝ) (subset_span hr)
  convert h using 1
  have hhalf : halfRoot (fun _ ↦ false) = fun _ ↦ 1 := by decide +kernel
  ext i
  change (1 : ℝ) = 2 * ((1 / 2) * (halfRoot (fun _ ↦ false) i : ℝ))
  rw [hhalf]
  norm_num

/-- Five axes and the common last three coordinates form a basis of the E₆ span. -/
theorem finrank_span_E₆ : finrank ℝ (span ℝ E₆.Φ) = 6 := by
  let u : EuclideanSpace ℝ (Fin 8) := WithLp.toLp 2 (fun _ ↦ 1)
  let tail : EuclideanSpace ℝ (Fin 8) :=
    u - ∑ i : Fin 5, EuclideanSpace.single (⟨i.val, by omega⟩ : Fin 8) 1
  have ht : tail ∈ span ℝ E₆.Φ :=
    sub_mem ones_mem_span_E₆ (sum_mem (fun i _ ↦ single_mem_span_E₆ _ i.isLt))
  let b : Fin 6 → EuclideanSpace ℝ (Fin 8) := fun i ↦
    if i.val < 5 then EuclideanSpace.single (⟨i.val, by omega⟩ : Fin 8) 1 else tail
  let coord : Fin 6 → Fin 8 := fun i ↦ ⟨i.val, by omega⟩
  apply finrank_eq_of_coordinate_basis _ coord b
  · intro i
    dsimp only [b]
    split_ifs with hi
    · exact single_mem_span_E₆ _ hi
    · exact ht
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [b, coord, tail, u, Pi.single_apply, Fin.sum_univ_succ]
  · intro x hx hz
    have he : x 6 = x 7 ∧ x 5 = x 6 := span_E₆_le_equalCoordinates hx
    ext i
    fin_cases i
    all_goals first | exact hz ⟨_, by decide⟩ | exact he.2 ▸ hz 5 |
      exact (he.2.trans he.1) ▸ hz 5

theorem single_mem_span_E₈viaSteiner (i : Fin 8) :
    EuclideanSpace.single i (1 : ℝ) ∈ span ℝ E₈viaSteiner.Φ := by
  have hr := E₈viaSteiner.integerModel.root_mem (Sum.inl (i, false))
  have h := (span ℝ E₈viaSteiner.Φ).smul_mem (Real.sqrt 2 / 2) (subset_span hr)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  convert h using 1
  ext j
  change (Pi.single i 1 : Fin 8 → ℝ) j =
    (Real.sqrt 2 / 2) * ((Real.sqrt 2)⁻¹ * ((axisRoot (i, false) j : ℤ) : ℝ))
  simp only [axisRoot, rootSign, Bool.false_eq_true, ite_false, mul_one, Pi.single_apply]
  split_ifs
  · norm_num only [Int.cast_ofNat]
    field_simp
  · norm_num

theorem finrank_span_E₈viaSteiner : finrank ℝ (span ℝ E₈viaSteiner.Φ) = 8 := by
  apply finrank_eq_of_coordinate_basis _ id (fun i ↦ EuclideanSpace.single i 1)
    single_mem_span_E₈viaSteiner
  · intro i j
    simp [eq_comm]
  · intro x _ hx
    ext i
    exact hx i

/-- The default name and the explicit model-(ii) name have the same span dimension. -/
theorem finrank_span_E₈viaD₈ : finrank ℝ (span ℝ E₈viaD₈.Φ) = 8 := finrank_span_E₈

end LineSystem
