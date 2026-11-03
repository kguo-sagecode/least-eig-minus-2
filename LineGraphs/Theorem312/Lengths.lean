/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Containment

/-!
# Lengths on root lines for Theorem 3.12 of [CGSS]

`lem:312-lengths` of the blueprint. Its pairwise input from `lem:angles` is proved
here directly from crystallographic integrality, as in the ordinary proof's root-angle
lemma: the products of the two integral coefficients are 1 or 2. No classification
or assertion about lengths of an entire irreducible component is used.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Φ : Set V}

/-- The pairwise integrality input to `t312lengthQuarterRatio` and
`t312lengthHalfRatio`, Theorem 3.12 of [CGSS] (`lem:312-lengths`). -/
private theorem exists_pairing_coefficients (hΦ : IsRootSet Φ) {r s : V}
    (hr : r ∈ Φ) (hs : s ∈ Φ) :
    ∃ a b : ℤ, (a : ℝ) * ⟪r, r⟫ = 2 * ⟪r, s⟫ ∧
      (b : ℝ) * ⟪s, s⟫ = 2 * ⟪r, s⟫ ∧
      (a : ℝ) * b * (⟪r, r⟫ * ⟪s, s⟫) = 4 * ⟪r, s⟫ ^ 2 := by
  have hr0 : ⟪r, r⟫ ≠ 0 := ne_of_gt (real_inner_self_pos.mpr (hΦ.ne_zero hr))
  have hs0 : ⟪s, s⟫ ≠ 0 := ne_of_gt (real_inner_self_pos.mpr (hΦ.ne_zero hs))
  obtain ⟨a, ha⟩ := hΦ.crystallographic r hr s hs
  obtain ⟨b, hb⟩ := hΦ.crystallographic s hs r hr
  rw [real_inner_comm] at hb
  have ha' := (eq_div_iff hr0).mp ha
  have hb' := (eq_div_iff hs0).mp hb
  refine ⟨a, b, ha', hb', ?_⟩
  calc
    (a : ℝ) * b * (⟪r, r⟫ * ⟪s, s⟫) =
        ((a : ℝ) * ⟪r, r⟫) * ((b : ℝ) * ⟪s, s⟫) := by ring
    _ = 4 * ⟪r, s⟫ ^ 2 := by rw [ha', hb']; ring

-- Theorem 3.12
/-- `t312lengthQuarter` of `lem:312-lengths`, Theorem 3.12 of [CGSS].
Roots whose line squared cosine is 1/4 have equal squared lengths. -/
theorem sqNorm_eq_of_four_mul_inner_sq_eq (hΦ : IsRootSet Φ) {r s : V}
    (hr : r ∈ Φ) (hs : s ∈ Φ) (hangle : 4 * ⟪r, s⟫ ^ 2 = ⟪r, r⟫ * ⟪s, s⟫) :
    ⟪r, r⟫ = ⟪s, s⟫ := by
  have hp : 0 < ⟪r, r⟫ * ⟪s, s⟫ :=
    mul_pos (real_inner_self_pos.mpr (hΦ.ne_zero hr))
      (real_inner_self_pos.mpr (hΦ.ne_zero hs))
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pairing_coefficients hΦ hr hs
  have hab' : (a : ℝ) * b = 1 := by
    apply mul_right_cancel₀ (ne_of_gt hp)
    simpa only [one_mul] using hab.trans hangle
  have habZ : a * b = 1 := by exact_mod_cast hab'
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' habZ with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;>
    norm_num only [ha', hb', Int.cast_neg, Int.cast_one] at ha hb <;> linarith

/-- `t312lengthHalf` of `lem:312-lengths`, Theorem 3.12 of [CGSS].
At squared cosine 1/2 one squared root length is twice the other. -/
theorem sqNorm_eq_two_mul_or_of_two_mul_inner_sq_eq (hΦ : IsRootSet Φ) {r s : V}
    (hr : r ∈ Φ) (hs : s ∈ Φ) (hangle : 2 * ⟪r, s⟫ ^ 2 = ⟪r, r⟫ * ⟪s, s⟫) :
    ⟪s, s⟫ = 2 * ⟪r, r⟫ ∨ ⟪r, r⟫ = 2 * ⟪s, s⟫ := by
  have hp : 0 < ⟪r, r⟫ * ⟪s, s⟫ :=
    mul_pos (real_inner_self_pos.mpr (hΦ.ne_zero hr))
      (real_inner_self_pos.mpr (hΦ.ne_zero hs))
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pairing_coefficients hΦ hr hs
  have hab' : (a : ℝ) * b = 2 := by
    apply mul_right_cancel₀ (ne_of_gt hp)
    nlinarith only [hab, hangle]
  have habZ : a * b = 2 := by exact_mod_cast hab'
  have hbnd := Int.natAbs_le_of_dvd_ne_zero (show a ∣ 2 from ⟨b, habZ.symm⟩)
    (by decide : (2 : ℤ) ≠ 0)
  have hlo : -2 ≤ a := by omega
  have hhi : a ≤ 2 := by omega
  interval_cases a
  · have hb' : b = -1 := by omega
    left
    norm_num only [hb', Int.cast_neg, Int.cast_one, Int.cast_ofNat] at ha hb
    linarith
  · have hb' : b = -2 := by omega
    right
    norm_num only [hb', Int.cast_neg, Int.cast_one, Int.cast_ofNat] at ha hb
    linarith
  · norm_num at habZ
  · have hb' : b = 2 := by omega
    right
    norm_num only [hb', Int.cast_neg, Int.cast_one, Int.cast_ofNat] at ha hb
    linarith
  · have hb' : b = 1 := by omega
    left
    norm_num only [hb', Int.cast_neg, Int.cast_one, Int.cast_ofNat] at ha hb
    linarith

end IsRootSet
