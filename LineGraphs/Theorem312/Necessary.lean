/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Lengths

/-!
# The necessary colouring for Theorem 3.12 of [CGSS]

`lem:312-log` and `lem:312-necessary` of the blueprint. The colour is the parity
of the integer logarithm of the squared length of a chosen root on each line.
This works for arbitrary scales and for negative logarithms.
-/

open scoped RealInnerProductSpace
open Submodule

namespace Int

-- Theorem 3.12
/-- `t312logBounds`--`t312logDoubleUpper` of `lem:312-log`, used in Theorem 3.12
of [CGSS]. Multiplication by 2 shifts the integer logarithm by 1. -/
theorem log_two_mul {x : ℝ} (hx : 0 < x) : log 2 (2 * x) = log 2 x + 1 := by
  have hlo : (2 : ℝ) ^ log 2 x ≤ x := by
    simpa only [Nat.cast_ofNat] using zpow_log_le_self (by decide : 1 < 2) hx
  have hhi : x < (2 : ℝ) ^ (log 2 x + 1) := by
    simpa only [Nat.cast_ofNat] using lt_zpow_succ_log_self (by decide : 1 < 2) x
  have hx' : 0 < 2 * x := mul_pos (by norm_num) hx
  have hlo' : (2 : ℝ) ^ (log 2 x + 1) ≤ 2 * x := by
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    linarith only [hlo]
  have hhi' : 2 * x < (2 : ℝ) ^ ((log 2 x + 1) + 1) := by
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    linarith only [hhi]
  have hle := (zpow_le_iff_le_log (by decide : 1 < 2) hx').mp hlo'
  have hlt := (lt_zpow_iff_log_lt (by decide : 1 < 2) hx').mp hhi'
  omega

/-- `t312logHalf` of `lem:312-log`, used in Theorem 3.12 of [CGSS]. -/
theorem log_two_div {x : ℝ} (hx : 0 < x) : log 2 (x / 2) = log 2 x - 1 := by
  have h := log_two_mul (div_pos hx (by norm_num : (0 : ℝ) < 2))
  have he : 2 * (x / 2) = x := by ring
  rw [he] at h
  omega

end Int

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.12
/-- `lem:312-necessary`, Theorem 3.12 of [CGSS]. Selected root lines with
allowed angles have a compatible colouring. No common normalization of the
containing root system or nonemptiness of either colour fibre is required. -/
theorem hasBipartition_of_subset_rootLines {Φ : Set V} (hΦ : IsRootSet Φ)
    {S : Set (Submodule ℝ V)} (hsub : S ⊆ rootLines Φ) (hangle : HasAllowedAngles S) :
    HasBipartition S := by
  classical
  have hex (ℓ : S) : ∃ r ∈ Φ, ℓ.1 = span ℝ {r} := hsub ℓ.property
  choose r hr hspan using hex
  have hmem (ℓ : S) : r ℓ ∈ ℓ.1 := by rw [hspan]; exact mem_span_singleton_self _
  have hpos (ℓ : S) : 0 < ⟪r ℓ, r ℓ⟫ := real_inner_self_pos.mpr (hΦ.ne_zero (hr ℓ))
  have hdim (ℓ : S) : Module.finrank ℝ ℓ.1 = 1 := by
    rw [hspan]
    exact finrank_span_singleton (hΦ.ne_zero (hr ℓ))
  let b : S → Bool := fun ℓ ↦ decide (Int.log 2 ⟪r ℓ, r ℓ⟫ % 2 = 1)
  have hquarter (ℓ m : S) (hc : HasSquaredCosine ℓ.1 m.1 (1 / 4)) : b ℓ = b m := by
    have he := (hasSquaredCosine_iff (hdim ℓ) (hdim m) (hmem ℓ) (hΦ.ne_zero (hr ℓ))
      (hmem m) (hΦ.ne_zero (hr m))).mp hc
    have hq := hΦ.sqNorm_eq_of_four_mul_inner_sq_eq (hr ℓ) (hr m) (by nlinarith only [he])
    dsimp only [b]
    rw [hq]
  have hhalf (ℓ m : S) (hc : HasSquaredCosine ℓ.1 m.1 (1 / 2)) : b ℓ ≠ b m := by
    have he := (hasSquaredCosine_iff (hdim ℓ) (hdim m) (hmem ℓ) (hΦ.ne_zero (hr ℓ))
      (hmem m) (hΦ.ne_zero (hr m))).mp hc
    have hq := hΦ.sqNorm_eq_two_mul_or_of_two_mul_inner_sq_eq (hr ℓ) (hr m)
      (by nlinarith only [he])
    change decide (Int.log 2 ⟪r ℓ, r ℓ⟫ % 2 = 1) ≠
      decide (Int.log 2 ⟪r m, r m⟫ % 2 = 1)
    rcases hq with hq | hq
    · rw [hq, Int.log_two_mul (hpos ℓ)]
      intro h
      simp only [decide_eq_decide] at h
      omega
    · have hq' : ⟪r m, r m⟫ = ⟪r ℓ, r ℓ⟫ / 2 := by linarith only [hq]
      rw [hq', Int.log_two_div (hpos ℓ)]
      intro h
      simp only [decide_eq_decide] at h
      omega
  refine ⟨b, ?_⟩
  intro ℓ m hne
  obtain ⟨a, ha, hc⟩ := hangle ℓ.1 ℓ.2 m.1 m.2 (fun h ↦ hne (Subtype.ext h))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨fun _ ↦ Or.inl hc, fun _ ↦ Or.inl hc⟩
  · exact ⟨fun _ ↦ Or.inr hc, fun h ↦ False.elim (h (hquarter ℓ m hc))⟩
  · exact ⟨fun h ↦ False.elim (hhalf ℓ m hc h), fun _ ↦ Or.inr hc⟩

end LineSystem
