/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic

/-!
# Integer pairings and squared angle alternatives

Steps `ranginteger`--`rangthreelength` of `lem:angles` in Remark 3.11 of
[CGSS]. The nonzero perpendicular residual gives strict Cauchy--Schwarz;
the two integral pairings therefore have product one, two, or three.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- Steps `rangresidual`--`rangstrict`: nonproportional vectors satisfy the
strict squared inner-product bound, by their perpendicular residual. -/
theorem inner_sq_lt_of_not_mem_line {r s : V} (hr : r ≠ 0) (hs : s ∉ ℝ ∙ r) :
    ⟪r, s⟫ ^ 2 < ⟪r, r⟫ * ⟪s, s⟫ := by
  have hq := real_inner_self_pos.mpr hr
  have hz : s - (⟪r, s⟫ / ⟪r, r⟫) • r ≠ 0 := by
    intro he
    exact hs (mem_span_singleton.mpr ⟨_, (sub_eq_zero.mp he).symm⟩)
  have hp := real_inner_self_pos.mpr hz
  have he : ⟪s - (⟪r, s⟫ / ⟪r, r⟫) • r,
      s - (⟪r, s⟫ / ⟪r, r⟫) • r⟫ * ⟪r, r⟫ =
      ⟪s, s⟫ * ⟪r, r⟫ - ⟪r, s⟫ ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm r s]
    field_simp
    ring
  nlinarith [mul_pos hp hq]

/-- Steps `ranginteger`--`rangproducts`: the integral pairings of a
nonorthogonal, nonproportional pair have product one, two, or three. -/
theorem exists_integer_pairings (hΦ : IsRootSet Φ) {r s : V} (hr : r ∈ Φ) (hs : s ∈ Φ)
    (ho : ⟪r, s⟫ ≠ 0) (hl : s ∉ ℝ ∙ r) :
    ∃ u v : ℤ, (u : ℝ) = 2 * ⟪r, s⟫ / ⟪r, r⟫ ∧
      (v : ℝ) = 2 * ⟪r, s⟫ / ⟪s, s⟫ ∧
      (u * v = 1 ∨ u * v = 2 ∨ u * v = 3) := by
  obtain ⟨u, hu⟩ := hΦ.crystallographic r hr s hs
  obtain ⟨v, hv⟩ := hΦ.crystallographic s hs r hr
  rw [real_inner_comm r s] at hv
  have he : ((u * v : ℤ) : ℝ) = 4 * ⟪r, s⟫ ^ 2 / (⟪r, r⟫ * ⟪s, s⟫) := by
    rw [Int.cast_mul, hu, hv]
    ring
  have hq := real_inner_self_pos.mpr (hΦ.ne_zero hr)
  have ht := real_inner_self_pos.mpr (hΦ.ne_zero hs)
  have hprod := mul_pos hq ht
  have hstrict := inner_sq_lt_of_not_mem_line (hΦ.ne_zero hr) hl
  have hbounds : (0 : ℝ) < (u * v : ℤ) ∧ ((u * v : ℤ) : ℝ) < 4 := by
    rw [he]
    constructor
    · exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ho)) hprod
    · apply (div_lt_iff₀ hprod).mpr
      nlinarith
  have hb : (0 : ℤ) < u * v ∧ u * v < 4 := by exact_mod_cast hbounds
  exact ⟨u, v, hu, hv, by omega⟩

-- Remark 3.11, lem:angles
/-- Step `rangproducts` of Remark 3.11: four times the squared cosine of a
nonorthogonal pair of distinct root lines is one, two, or three. -/
theorem pairing_product_mem (hΦ : IsRootSet Φ) {r s : V} (hr : r ∈ Φ) (hs : s ∈ Φ)
    (ho : ⟪r, s⟫ ≠ 0) (hl : s ∉ ℝ ∙ r) :
    4 * ⟪r, s⟫ ^ 2 / (⟪r, r⟫ * ⟪s, s⟫) ∈ ({1, 2, 3} : Set ℝ) := by
  obtain ⟨u, v, hu, hv, hp⟩ := hΦ.exists_integer_pairings hr hs ho hl
  have he : 4 * ⟪r, s⟫ ^ 2 / (⟪r, r⟫ * ⟪s, s⟫) = ((u * v : ℤ) : ℝ) := by
    rw [Int.cast_mul, hu, hv]
    ring
  rw [he]
  rcases hp with h | h | h <;> norm_num [h]

/-- The elementary integer bounds behind steps `rangoneinteger`--`rangthreeinteger`.
The signs agree and each absolute value is at most three. -/
theorem integer_pairing_bounds {u v : ℤ} (h : u * v = 1 ∨ u * v = 2 ∨ u * v = 3) :
    (-3 ≤ u ∧ u ≤ 3) ∧ (-3 ≤ v ∧ v ≤ 3) := by
  have hp : 0 < u * v := by rcases h with h | h | h <;> omega
  have hb : u * v ≤ 3 := by rcases h with h | h | h <;> omega
  rcases mul_pos_iff.mp hp with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hu' : 1 ≤ u := hu
    have hv' : 1 ≤ v := hv
    constructor <;> constructor <;> nlinarith
  · have hu' : u ≤ -1 := by omega
    have hv' : v ≤ -1 := by omega
    constructor <;> constructor <;> nlinarith

/-- Steps `rangone`--`rangthree` in squared form: the pairing product determines
both the squared-length ratio and the squared cosine. -/
theorem squared_angle_length_cases (hΦ : IsRootSet Φ) {r s : V}
    (hr : r ∈ Φ) (hs : s ∈ Φ) (ho : ⟪r, s⟫ ≠ 0) (hl : s ∉ ℝ ∙ r) :
    (⟪r, r⟫ = ⟪s, s⟫ ∧ 4 * ⟪r, s⟫ ^ 2 = ⟪r, r⟫ * ⟪s, s⟫) ∨
    ((⟪r, r⟫ = 2 * ⟪s, s⟫ ∨ ⟪s, s⟫ = 2 * ⟪r, r⟫) ∧
      4 * ⟪r, s⟫ ^ 2 = 2 * ⟪r, r⟫ * ⟪s, s⟫) ∨
    ((⟪r, r⟫ = 3 * ⟪s, s⟫ ∨ ⟪s, s⟫ = 3 * ⟪r, r⟫) ∧
      4 * ⟪r, s⟫ ^ 2 = 3 * ⟪r, r⟫ * ⟪s, s⟫) := by
  obtain ⟨u, v, hu, hv, hp⟩ := hΦ.exists_integer_pairings hr hs ho hl
  have hq := real_inner_self_pos.mpr (hΦ.ne_zero hr)
  have ht := real_inner_self_pos.mpr (hΦ.ne_zero hs)
  have hu' := (eq_div_iff (ne_of_gt hq)).mp hu
  have hv' := (eq_div_iff (ne_of_gt ht)).mp hv
  have he : ((u * v : ℤ) : ℝ) * (⟪r, r⟫ * ⟪s, s⟫) = 4 * ⟪r, s⟫ ^ 2 := by
    push_cast
    calc
      (u : ℝ) * v * (⟪r, r⟫ * ⟪s, s⟫) =
          ((u : ℝ) * ⟪r, r⟫) * ((v : ℝ) * ⟪s, s⟫) := by ring
      _ = _ := by rw [hu', hv']; ring
  obtain ⟨⟨hu₁, hu₂⟩, -⟩ := integer_pairing_bounds hp
  -- Only the seven values of `u` are enumerated; the product fixes the possible `v`.
  interval_cases u
  · have hvv : v = -1 := by omega
    subst v
    norm_num only at hu' hv' he
    exact Or.inr (Or.inr ⟨Or.inr (by linarith), by linarith⟩)
  · have hvv : v = -1 := by omega
    subst v
    norm_num only at hu' hv' he
    exact Or.inr (Or.inl ⟨Or.inr (by linarith), by linarith⟩)
  · have hvv : v = -1 ∨ v = -2 ∨ v = -3 := by omega
    rcases hvv with rfl | rfl | rfl <;> norm_num only at hu' hv' he
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨Or.inl (by linarith), by linarith⟩)
    · exact Or.inr (Or.inr ⟨Or.inl (by linarith), by linarith⟩)
  · omega
  · have hvv : v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hvv with rfl | rfl | rfl <;> norm_num only at hu' hv' he
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨Or.inl (by linarith), by linarith⟩)
    · exact Or.inr (Or.inr ⟨Or.inl (by linarith), by linarith⟩)
  · have hvv : v = 1 := by omega
    subst v
    norm_num only at hu' hv' he
    exact Or.inr (Or.inl ⟨Or.inr (by linarith), by linarith⟩)
  · have hvv : v = 1 := by omega
    subst v
    norm_num only at hu' hv' he
    exact Or.inr (Or.inr ⟨Or.inr (by linarith), by linarith⟩)

end IsRootSet
