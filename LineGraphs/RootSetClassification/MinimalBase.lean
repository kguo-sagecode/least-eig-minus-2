/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic

/-!
# Minimal lattice vectors in an obtuse basis

`lem:minimal-base` of the blueprint for Remark 3.11 of [CGSS]. Split the integer
coefficients into positive and negative parts. Their cross product is nonpositive,
so a vector of minimal length cannot have both parts nonzero.
-/

open scoped RealInnerProductSpace

namespace RootSetModel

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Steps `rmbsplit`--`rmbone` of Remark 3.11, for a specified integer coefficient vector. -/
theorem coefficients_one_sign_of_minimal_sum (L : AddSubgroup V) {b : ℝ} (hb : 0 < b)
    (hmin : ∀ x ∈ L, x ≠ 0 → b ≤ ⟪x, x⟫) (α : Module.Basis I ℝ V)
    (hα : ∀ i, α i ∈ L) (hcross : ∀ i j, i ≠ j → ⟪α i, α j⟫ ≤ 0)
    (c : I → ℤ) (hc : ⟪∑ i, (c i : ℝ) • α i, ∑ i, (c i : ℝ) • α i⟫ = b) :
    (∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0) := by
  classical
  let p : I → ℤ := fun i ↦ max (c i) 0
  let q : I → ℤ := fun i ↦ max (-c i) 0
  let v : V := ∑ i, (p i : ℝ) • α i
  let w : V := ∑ i, (q i : ℝ) • α i
  have hp (i : I) : 0 ≤ (p i : ℝ) := by exact_mod_cast (le_max_right (c i) 0)
  have hq (i : I) : 0 ≤ (q i : ℝ) := by exact_mod_cast (le_max_right (-c i) 0)
  have hpq (i : I) : p i * q i = 0 := by
    dsimp [p, q]
    by_cases hi : 0 ≤ c i
    · rw [max_eq_left hi, max_eq_right (by omega), mul_zero]
    · rw [max_eq_right (by omega), zero_mul]
  have hv : v ∈ L := by
    apply L.sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact L.zsmul_mem (hα i) _
  have hw : w ∈ L := by
    apply L.sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact L.zsmul_mem (hα i) _
  have hsplit : (∑ i, (c i : ℝ) • α i) = v - w := by
    change (∑ i, (c i : ℝ) • α i) =
      (∑ i, (p i : ℝ) • α i) - ∑ i, (q i : ℝ) • α i
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_smul]
    have hi : c i = p i - q i := by dsimp [p, q]; omega
    rw [hi, Int.cast_sub]
  have hvw : ⟪v, w⟫ ≤ 0 := by
    simp only [v, w, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j
      have hzero : (p i : ℝ) * (q i : ℝ) = 0 := by exact_mod_cast hpq i
      rw [mul_left_comm, ← mul_assoc, hzero, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hq i)
        (mul_nonpos_of_nonneg_of_nonpos (hp j) (hcross j i (fun h ↦ hij h.symm)))
  have hz : v = 0 ∨ w = 0 := by
    by_contra! h
    have hvmin := hmin v hv h.1
    have hwmin := hmin w hw h.2
    rw [hsplit, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm v w] at hc
    nlinarith
  rcases hz with hz | hz
  · right
    intro i
    have hi := congrArg (fun x ↦ α.repr x i) hz
    have hpi : (p i : ℝ) = 0 := by simpa [v, Finsupp.single_apply] using hi
    have : p i = 0 := by exact_mod_cast hpi
    dsimp [p] at this
    omega
  · left
    intro i
    have hi := congrArg (fun x ↦ α.repr x i) hz
    have hqi : (q i : ℝ) = 0 := by simpa [w, Finsupp.single_apply] using hi
    have : q i = 0 := by exact_mod_cast hqi
    dsimp [q] at this
    omega

-- Remark 3.11, lem:minimal-base
/-- `lem:minimal-base` of Remark 3.11 of [CGSS]: in an obtuse real basis generating
a lattice over the integers, every minimal vector has integer coefficients of one sign. -/
theorem coefficients_one_sign_of_minimal (L : AddSubgroup V) {b : ℝ} (hb : 0 < b)
    (hmin : ∀ x ∈ L, x ≠ 0 → b ≤ ⟪x, x⟫) (α : Module.Basis I ℝ V)
    (hgen : ∀ x, x ∈ L ↔ ∃ c : I → ℤ, x = ∑ i, (c i : ℝ) • α i)
    (hcross : ∀ i j, i ≠ j → ⟪α i, α j⟫ ≤ 0)
    {x : V} (hx : x ∈ L) (hxb : ⟪x, x⟫ = b) :
    ∃ c : I → ℤ, ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0)) ∧
      x = ∑ i, (c i : ℝ) • α i := by
  classical
  obtain ⟨c, hc⟩ := (hgen x).mp hx
  have hα (i : I) : α i ∈ L := by
    apply (hgen (α i)).mpr
    refine ⟨Pi.single i 1, ?_⟩
    simp [Pi.single_apply]
  exact ⟨c, coefficients_one_sign_of_minimal_sum L hb hmin α hα hcross c (hc ▸ hxb), hc⟩

end RootSetModel
