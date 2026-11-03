/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Finite

/-!
# Bounded integer spans for Theorem 3.12 of [CGSS]

`lem:312-integer-span`: integrality and evenness extend by integer span induction.
The bounded part is finite by its coordinates against the finite generating set.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `t312intReal` of `lem:312-integer-span`, Theorem 3.12 of [CGSS]. -/
theorem mem_realSpan_of_mem_intSpan {T : Set V} {x : V} (hx : x ∈ span ℤ T) :
    x ∈ span ℝ T := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact subset_span hx
  | zero => exact zero_mem _
  | add x y hx hy hx' hy' => exact add_mem hx' hy'
  | smul a x hx hx' =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact smul_mem _ _ hx'

-- Theorem 3.12
/-- `t312intExpand` and `t312intPair` of `lem:312-integer-span`, Theorem 3.12
of [CGSS]. No finiteness or norm hypothesis is needed for integrality alone. -/
theorem inner_int_of_mem_intSpan {T : Set V}
    (hT : ∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z)
    {x y : V} (hx : x ∈ span ℤ T) (hy : y ∈ span ℤ T) :
    ∃ z : ℤ, ⟪x, y⟫ = z := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact hT x hx y hy
  | zero_left y hy => exact ⟨0, by simp⟩
  | zero_right x hx => exact ⟨0, by simp⟩
  | add_left x y z hx hy hz hx' hy' =>
    obtain ⟨a, ha⟩ := hx'
    obtain ⟨b, hb⟩ := hy'
    exact ⟨a + b, by simp [inner_add_left, ha, hb]⟩
  | add_right x y z hx hy hz hy' hz' =>
    obtain ⟨a, ha⟩ := hy'
    obtain ⟨b, hb⟩ := hz'
    exact ⟨a + b, by simp [inner_add_right, ha, hb]⟩
  | smul_left a x y hx hy h =>
    obtain ⟨b, hb⟩ := h
    refine ⟨a * b, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hb, Int.cast_mul]
  | smul_right a x y hx hy h =>
    obtain ⟨b, hb⟩ := h
    refine ⟨a * b, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hb, Int.cast_mul]

/-- `t312intEven` of `lem:312-integer-span`, Theorem 3.12 of [CGSS].
The fixed vector need not itself be a generator. -/
theorem inner_even_of_mem_intSpan {T : Set V} {t x : V}
    (ht : ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = 2 * z) (hx : x ∈ span ℤ T) :
    ∃ z : ℤ, ⟪t, x⟫ = 2 * z := by
  induction hx using Submodule.span_induction with
  | mem u hu => exact ht u hu
  | zero => exact ⟨0, by simp⟩
  | add u v hu hv hu' hv' =>
    obtain ⟨a, ha⟩ := hu'
    obtain ⟨b, hb⟩ := hv'
    exact ⟨a + b, by simp [inner_add_right, ha, hb, mul_add]⟩
  | smul a u hu hu' =>
    obtain ⟨b, hb⟩ := hu'
    refine ⟨a * b, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hb, Int.cast_mul]
    ring

/-- `t312intBound` and `t312intFinite` of `lem:312-integer-span`, Theorem 3.12
of [CGSS]. The coordinates are integers between -4 and 4. Finite dimension is
unnecessary once the finite generating set is supplied. -/
theorem finite_bounded_intSpan {T : Set V} (hfin : T.Finite)
    (hnorm : ∀ t ∈ T, ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4)
    (hint : ∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z) :
    {x | x ∈ span ℤ T ∧ ⟪x, x⟫ ≤ 4}.Finite := by
  classical
  have : Finite T := hfin.to_subtype
  let Θ : Set ℝ := (fun z : ℤ ↦ (z : ℝ)) '' Set.Icc (-4) 4
  refine finite_of_inner_mem_finite (fun t : T ↦ (t : V)) (Θ := Θ) ?_ ?_ ?_
  · intro x hx
    change x ∈ span ℝ (Set.range (fun t : T ↦ (t : V)))
    rw [Subtype.range_coe]
    exact mem_realSpan_of_mem_intSpan hx.1
  · exact (Set.finite_Icc (-4 : ℤ) 4).image _
  · intro x hx t
    obtain ⟨z, hz⟩ := inner_int_of_mem_intSpan hint hx.1 (subset_span t.property)
    have hcs := real_inner_mul_inner_self_le x (t : V)
    have ht : ⟪(t : V), t⟫ ≤ 4 := by rcases hnorm t t.property with h | h <;> linarith
    have hprod : ⟪x, x⟫ * ⟪(t : V), t⟫ ≤ 4 * 4 :=
      mul_le_mul hx.2 ht real_inner_self_nonneg (by norm_num)
    have hbound : (z : ℝ) ^ 2 ≤ 16 := by rw [hz] at hcs; nlinarith
    have hlo : (-4 : ℝ) ≤ z := by nlinarith [sq_nonneg ((z : ℝ) + 4)]
    have hhi : (z : ℝ) ≤ 4 := by nlinarith [sq_nonneg ((z : ℝ) - 4)]
    exact ⟨z, ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩, hz.symm⟩

end LineSystem
