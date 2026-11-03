/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ExceptionalCoordinates

/-!
# The even E₈ lattice

`lem:even-lattice` in the blueprint for Remark 3.11 of [CGSS]. The construction
uses the two cosets of the integer even-sum lattice, as in `relcosets`.
-/

open scoped RealInnerProductSpace
open Finset

namespace RootSetModel

/-- The integer even-sum subgroup `L₀` in step `relcosets` of Remark 3.11. -/
noncomputable def evenCoordinateLattice (n : ℕ) :
    AddSubgroup (EuclideanSpace ℝ (Fin n)) where
  carrier := {x | ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧ x = LineSystem.integerVector 1 z}
  zero_mem' := ⟨0, by simp, by ext i; simp [LineSystem.integerVector]⟩
  add_mem' := by
    rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨z + w, ?_, ?_⟩
    · simpa only [Pi.add_apply, sum_add_distrib] using hz.add hw
    · ext i; simp [LineSystem.integerVector]
  neg_mem' := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨-z, ?_, ?_⟩
    · simpa only [Pi.neg_apply, sum_neg_distrib] using hz.neg
    · ext i; simp [LineSystem.integerVector]

/-- The half-coordinate shift `v` in `relcosets` of Remark 3.11. -/
noncomputable def halfShift : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 (fun _ ↦ (1 : ℝ) / 2)

/-- Step `relcosets`: twice the half-coordinate shift has even integer coordinate sum. -/
theorem add_halfShift_mem_evenCoordinateLattice :
    halfShift + halfShift ∈ evenCoordinateLattice 8 := by
  refine ⟨fun _ ↦ 1, ?_, ?_⟩
  · norm_num
  · ext i
    norm_num [halfShift, LineSystem.integerVector]

/-- The lattice `L = L₀ ∪ (L₀ + v)` of `eq:E-lattice` in Remark 3.11.
The group laws are the five coset cases `rel00`--`relneg1`. -/
noncomputable def e₈Lattice : AddSubgroup (EuclideanSpace ℝ (Fin 8)) where
  carrier := {x | x ∈ evenCoordinateLattice 8 ∨ x - halfShift ∈ evenCoordinateLattice 8}
  zero_mem' := Or.inl (evenCoordinateLattice 8).zero_mem
  add_mem' := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl ((evenCoordinateLattice 8).add_mem hx hy)
    · right
      convert (evenCoordinateLattice 8).add_mem hx hy using 1
      abel
    · right
      convert (evenCoordinateLattice 8).add_mem hx hy using 1
      abel
    · left
      convert (evenCoordinateLattice 8).add_mem
        ((evenCoordinateLattice 8).add_mem hx hy)
        add_halfShift_mem_evenCoordinateLattice using 1
      abel
  neg_mem' := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ((evenCoordinateLattice 8).neg_mem hx)
    · right
      convert (evenCoordinateLattice 8).sub_mem
        ((evenCoordinateLattice 8).neg_mem hx)
        add_halfShift_mem_evenCoordinateLattice using 1
      abel

/-- Step `relintv`: pairing an integer vector with the half-coordinate shift. -/
theorem inner_integerVector_halfShift (z : Fin 8 → ℤ) :
    ⟪LineSystem.integerVector 1 z, halfShift⟫ = ((∑ i, z i : ℤ) : ℝ) / 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, halfShift,
    LineSystem.integerVector, one_mul, Int.cast_sum, div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- Step `relintvv`: the half-coordinate shift has squared norm two. -/
theorem inner_halfShift_self : ⟪halfShift, halfShift⟫ = (2 : ℝ) := by
  rw [PiLp.inner_apply]
  norm_num [halfShift]

/-- Step `releven0`: an integer vector with even coordinate sum has even squared norm. -/
theorem even_integerInner_of_even_sum {n : ℕ} (z : Fin n → ℤ)
    (hz : Even (∑ i, z i)) : Even (LineSystem.integerInner z z) := by
  have hs : Even (∑ i, z i * (z i + 1)) :=
    Finset.even_sum _ (fun i _ ↦ Int.even_mul_succ_self (z i))
  have he : (∑ i, z i * (z i + 1)) - ∑ i, z i = LineSystem.integerInner z z := by
    simp only [mul_add, mul_one, sum_add_distrib, LineSystem.integerInner, dotProduct]
    abel
  exact he ▸ hs.sub hz

/-- Steps `relint00`, `relintv`: all products within `L₀`, and all products with
the shift, are integers. -/
theorem inner_mem_int_evenCoordinateLattice {x y : EuclideanSpace ℝ (Fin 8)}
    (hx : x ∈ evenCoordinateLattice 8) (hy : y ∈ evenCoordinateLattice 8) :
    ∃ z : ℤ, (z : ℝ) = ⟪x, y⟫ := by
  obtain ⟨v, _, rfl⟩ := hx
  obtain ⟨w, _, rfl⟩ := hy
  exact ⟨LineSystem.integerInner v w, by simp [LineSystem.inner_integerVector]⟩

/-- Step `relintv`: even coordinate sum makes pairing with the shift integral. -/
theorem inner_halfShift_mem_int {x : EuclideanSpace ℝ (Fin 8)}
    (hx : x ∈ evenCoordinateLattice 8) : ∃ z : ℤ, (z : ℝ) = ⟪x, halfShift⟫ := by
  obtain ⟨v, ⟨z, hz⟩, rfl⟩ := hx
  refine ⟨z, ?_⟩
  rw [inner_integerVector_halfShift, hz]
  push_cast
  ring

/-- Step `relintegral`: expanding the two cosets shows that the E₈ lattice is integral. -/
theorem inner_mem_int_e₈Lattice {x y : EuclideanSpace ℝ (Fin 8)}
    (hx : x ∈ e₈Lattice) (hy : y ∈ e₈Lattice) : ∃ z : ℤ, (z : ℝ) = ⟪x, y⟫ := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact inner_mem_int_evenCoordinateLattice hx hy
  · obtain ⟨a, ha⟩ := inner_mem_int_evenCoordinateLattice hx hy
    obtain ⟨b, hb⟩ := inner_halfShift_mem_int hx
    refine ⟨a + b, ?_⟩
    rw [inner_sub_right] at ha
    push_cast
    linarith
  · obtain ⟨a, ha⟩ := inner_mem_int_evenCoordinateLattice hx hy
    obtain ⟨b, hb⟩ := inner_halfShift_mem_int hy
    refine ⟨a + b, ?_⟩
    rw [inner_sub_left, real_inner_comm y halfShift] at ha
    push_cast
    linarith
  · obtain ⟨a, ha⟩ := inner_mem_int_evenCoordinateLattice hx hy
    obtain ⟨b, hb⟩ := inner_halfShift_mem_int hx
    obtain ⟨c, hc⟩ := inner_halfShift_mem_int hy
    refine ⟨a + b + c + 2, ?_⟩
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm y halfShift, inner_halfShift_self] at ha
    rw [inner_sub_left, inner_halfShift_self] at hb hc
    push_cast
    linarith

/-- Steps `releven0`, `releven1`: every lattice squared norm is an even integer. -/
theorem inner_self_even_e₈Lattice {x : EuclideanSpace ℝ (Fin 8)} (hx : x ∈ e₈Lattice) :
    ∃ z : ℤ, Even z ∧ (z : ℝ) = ⟪x, x⟫ := by
  rcases hx with hx | hx
  · obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨LineSystem.integerInner v v, even_integerInner_of_even_sum v hv,
      by simp only [LineSystem.inner_integerVector, one_mul]⟩
  · obtain ⟨v, hv, he⟩ := hx
    have hx' : x = LineSystem.integerVector 1 v + halfShift := (sub_eq_iff_eq_add.mp he)
    obtain ⟨a, ha⟩ := inner_halfShift_mem_int (show LineSystem.integerVector 1 v ∈
      evenCoordinateLattice 8 from ⟨v, hv, rfl⟩)
    refine ⟨LineSystem.integerInner v v + 2 * a + 2,
      ((even_integerInner_of_even_sum v hv).add (even_two_mul a)).add (by decide), ?_⟩
    rw [hx', inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm (LineSystem.integerVector 1 v) halfShift, ← ha,
      inner_halfShift_self, LineSystem.inner_integerVector]
    push_cast
    ring

/-- Step `relminimum`: a nonzero lattice vector has squared length at least two. -/
theorem two_le_inner_self_of_mem_e₈Lattice {x : EuclideanSpace ℝ (Fin 8)}
    (hx : x ∈ e₈Lattice) (hx0 : x ≠ 0) : 2 ≤ ⟪x, x⟫ := by
  obtain ⟨z, ⟨k, hk⟩, hz⟩ := inner_self_even_e₈Lattice hx
  have hp : (0 : ℝ) < z := hz ▸ real_inner_self_pos.mpr hx0
  have hk' : 1 ≤ k := by
    have : (0 : ℤ) < z := by exact_mod_cast hp
    omega
  rw [← hz, hk]
  exact_mod_cast (show 2 ≤ k + k by omega)

-- Remark 3.11, lem:even-lattice
/-- The integrality, evenness, and minimum assertions of `lem:even-lattice` in
Remark 3.11 of [CGSS]. The subgroup laws are fields of `e₈Lattice`. -/
theorem E₈_lattice_even :
    (∀ x ∈ e₈Lattice, ∀ y ∈ e₈Lattice, ∃ z : ℤ, (z : ℝ) = ⟪x, y⟫) ∧
    (∀ x ∈ e₈Lattice, ∃ z : ℤ, Even z ∧ (z : ℝ) = ⟪x, x⟫) ∧
    (∀ x ∈ e₈Lattice, x ≠ 0 → 2 ≤ ⟪x, x⟫) :=
  ⟨fun _ hx _ hy ↦ inner_mem_int_e₈Lattice hx hy,
    fun _ hx ↦ inner_self_even_e₈Lattice hx,
    fun _ hx hx0 ↦ two_le_inner_self_of_mem_e₈Lattice hx hx0⟩

/-- Step `releven1`: the shifted integer norm formula, also used in `relhalfbound`. -/
theorem inner_integerVector_add_halfShift_self (v : Fin 8 → ℤ) :
    ⟪LineSystem.integerVector 1 v + halfShift, LineSystem.integerVector 1 v + halfShift⟫ =
      ((∑ i, v i * (v i + 1) : ℤ) : ℝ) + 2 := by
  rw [inner_add_left, inner_add_right, inner_add_right,
    real_inner_comm (LineSystem.integerVector 1 v) halfShift,
    inner_integerVector_halfShift, inner_halfShift_self, LineSystem.inner_integerVector]
  have he : (∑ i, v i * (v i + 1)) = LineSystem.integerInner v v + ∑ i, v i := by
    simp [mul_add, sum_add_distrib, LineSystem.integerInner, dotProduct]
  rw [he]
  push_cast
  ring

/-- Steps `relhalfbound`, `relhalfequal`: norm two forces all shifted coordinates
to be plus or minus one half. -/
theorem coordinate_eq_zero_or_neg_one_of_shift_norm_two (v : Fin 8 → ℤ)
    (hv : ⟪LineSystem.integerVector 1 v + halfShift,
      LineSystem.integerVector 1 v + halfShift⟫ = 2) : ∀ i, v i = 0 ∨ v i = -1 := by
  rw [inner_integerVector_add_halfShift_self] at hv
  have hsum : (∑ i, v i * (v i + 1)) = 0 := by
    have : ((∑ i, v i * (v i + 1) : ℤ) : ℝ) = 0 := by linarith
    exact_mod_cast this
  have hnonneg (i : Fin 8) : 0 ≤ v i * (v i + 1) := by
    have : v i ≤ -1 ∨ 0 ≤ v i := by omega
    rcases this with h | h <;> nlinarith
  intro i
  have hi : v i * (v i + 1) = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp hsum i (mem_univ i)
  rcases mul_eq_zero.mp hi with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- Step `relhalfparity`: subtracting the all-positive half-root yields even sum
for each of the 128 even sign patterns. This finite parity identity is kernel checked. -/
theorem even_sum_halfRoot_shift :
    ∀ s : Fin 7 → Bool, Even (∑ i : Fin 8, (LineSystem.halfRoot s i - 1) / 2) := by
  decide +kernel

/-- Step `relhalfparity`: the even coordinate sum determines the eighth half-root
sign from the first seven. This finite parity identity is kernel checked. -/
theorem halfRoot_restrict_of_even_signs : ∀ s : Fin 8 → Bool,
    Even (∑ i, if s i then (-1 : ℤ) else 0) →
      LineSystem.halfRoot (fun i ↦ s i.castSucc) = fun i ↦ LineSystem.rootSign (s i) := by
  decide +kernel

/-- The reverse inclusion in steps `relroots0`, `relroots1`: all E₈ roots lie in
the two-coset lattice. -/
theorem E₈_subset_e₈Lattice : E₈ ⊆ e₈Lattice := by
  rintro x ⟨a, rfl⟩
  cases a with
  | inl a =>
    left
    refine ⟨LineSystem.dnRoot a, ?_, ?_⟩
    · rcases a with ⟨p, a, b⟩
      cases a <;> cases b <;>
        norm_num [LineSystem.dnRoot, LineSystem.pairVector, LineSystem.rootSign,
          sum_add_distrib]
    · ext i
      simp [LineSystem.integerVector, LineSystem.e₈Root]
  | inr s =>
    right
    refine ⟨fun i ↦ (LineSystem.halfRoot s i - 1) / 2, even_sum_halfRoot_shift s, ?_⟩
    ext i
    rcases LineSystem.halfRoot_mem s i with hi | hi <;>
      norm_num [LineSystem.integerVector, LineSystem.e₈Root, halfShift, hi]

/-- Step `relroots0`: the integer norm-two lattice vectors are exactly signed pairs. -/
theorem mem_E₈_of_mem_evenCoordinateLattice_of_norm_two {x : EuclideanSpace ℝ (Fin 8)}
    (hx : x ∈ evenCoordinateLattice 8) (h₂ : ⟪x, x⟫ = 2) : x ∈ E₈ := by
  obtain ⟨v, _, rfl⟩ := hx
  rw [LineSystem.inner_integerVector] at h₂
  have hv' : (LineSystem.integerInner v v : ℝ) = 2 := by simpa using h₂
  have hv : LineSystem.integerInner v v = 2 := by exact_mod_cast hv'
  obtain ⟨a, rfl⟩ := LineSystem.exists_dnRoot_of_inner_self v hv
  refine ⟨Sum.inl a, ?_⟩
  ext i
  simp [LineSystem.integerVector, LineSystem.e₈Root]

/-- Step `relroots1`: the shifted norm-two lattice vectors are exactly even half-roots. -/
theorem mem_E₈_of_shift_mem_evenCoordinateLattice_of_norm_two
    {x : EuclideanSpace ℝ (Fin 8)} (hx : x - halfShift ∈ evenCoordinateLattice 8)
    (h₂ : ⟪x, x⟫ = 2) : x ∈ E₈ := by
  obtain ⟨v, hv, he⟩ := hx
  have he' : x = LineSystem.integerVector 1 v + halfShift := sub_eq_iff_eq_add.mp he
  have hvalues := coordinate_eq_zero_or_neg_one_of_shift_norm_two v (he' ▸ h₂)
  let s : Fin 8 → Bool := fun i ↦ decide (v i = -1)
  have hv' : v = fun i ↦ if s i then -1 else 0 := by
    funext i
    rcases hvalues i with hi | hi <;> simp [s, hi]
  have heven : Even (∑ i, if s i then (-1 : ℤ) else 0) := hv' ▸ hv
  have hs := halfRoot_restrict_of_even_signs s heven
  refine ⟨Sum.inr (fun i ↦ s i.castSucc), ?_⟩
  rw [he']
  ext i
  have hsi := congrFun hs i
  rcases hvalues i with hi | hi <;>
    norm_num [LineSystem.integerVector, LineSystem.e₈Root, halfShift, hsi,
      LineSystem.rootSign, s, hi]

-- Remark 3.11, lem:even-lattice
/-- The squared-norm-two characterization in `lem:even-lattice` of Remark 3.11 of [CGSS]. -/
theorem E₈_eq_norm_two : E₈ = {x | x ∈ e₈Lattice ∧ ⟪x, x⟫ = 2} := by
  ext x
  constructor
  · intro hx
    exact ⟨E₈_subset_e₈Lattice hx, LineSystem.E₈.inner_self x hx⟩
  · rintro ⟨hx | hx, h₂⟩
    · exact mem_E₈_of_mem_evenCoordinateLattice_of_norm_two hx h₂
    · exact mem_E₈_of_shift_mem_evenCoordinateLattice_of_norm_two hx h₂

end RootSetModel
