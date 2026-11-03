/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LineAngles
import LineGraphs.RootSetClassification.ClassicalLines
import LineGraphs.RootSetClassification.ThreeLines

/-!
# The line angles of the two-length models

Steps `rCallowed` and `rCoccurrence` of Theorem C of the blueprint for Remark 3.11 of [CGSS]: the
allowed angles between distinct lines of the Bₙ, Cₙ, F₄ and G₂ models, and a witness
pair for each angle that occurs. For `n = 2` the classical models have no pair of lines
at sixty degrees (`rCtwoangles`), checked on the integer coordinates of the eight roots.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- A witness pair in step `rCoccurrence` of Remark 3.11: two roots whose squared inner
product is less than the product of their squared lengths lie on distinct lines, so their
line angle occurs. -/
theorem lineAngle_mem_lineAngles {r s : V} (hr : r ∈ Φ) (hs : s ∈ Φ)
    (hlt : ⟪r, s⟫ ^ 2 < ⟪r, r⟫ * ⟪s, s⟫) : lineAngle r s ∈ lineAngles Φ :=
  ⟨r, hr, s, hs, not_mem_line_of_inner_sq_lt hlt, rfl⟩

/-- The converse of `lineAngle_eq_pi_div_three` in `facts:rem-angles` of Remark 3.11:
a sixty-degree line angle has squared cosine one quarter. -/
theorem inner_sq_of_lineAngle_eq_pi_div_three {r s : V} (hr : r ≠ 0) (hs : s ≠ 0)
    (h : lineAngle r s = Real.pi / 3) : 4 * ⟪r, s⟫ ^ 2 = ⟪r, r⟫ * ⟪s, s⟫ := by
  have hpos : 0 < ‖r‖ * ‖s‖ := mul_pos (norm_pos_iff.mpr hr) (norm_pos_iff.mpr hs)
  have hle : |⟪r, s⟫| / (‖r‖ * ‖s‖) ≤ 1 :=
    (div_le_one hpos).mpr (abs_real_inner_le_norm r s)
  have hge : -1 ≤ |⟪r, s⟫| / (‖r‖ * ‖s‖) := by
    have := div_nonneg (abs_nonneg ⟪r, s⟫) hpos.le
    linarith
  have hc := Real.cos_arccos hge hle
  unfold lineAngle at h
  rw [h, Real.cos_pi_div_three, eq_div_iff hpos.ne'] at hc
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← sq_abs, ← hc]
  ring

end IsRootSet

namespace RootSetModel

open IsRootSet

/-- The inner products of distinct coordinate vectors, used in step `rCoccurrence`. -/
theorem inner_unit_of_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) : ⟪unit i, unit j⟫ = (0 : ℝ) := by
  simp [inner_unit, h]

/-- A coordinate vector is a unit vector (step `rCoccurrence`). -/
theorem inner_unit_self {n : ℕ} (i : Fin n) : ⟪unit i, unit i⟫ = (1 : ℝ) := by
  simp only [inner_unit, ↓reduceIte]

/-- Steps `rCright`, `rCfortyfive` of Remark 3.11: a coordinate vector is an axis root
of length one. -/
theorem unit_mem_axisRoots_one {n : ℕ} (i : Fin n) : unit i ∈ axisRoots n 1 :=
  ⟨i, Or.inl (one_smul ℝ _).symm⟩

/-- Steps `rCfortyfive`, `rCsixty` of Remark 3.11: a positive signed pair of coordinate
vectors is a D root. -/
theorem unit_add_unit_mem_Dn {n : ℕ} {i j : Fin n} (h : i ≠ j) : unit i + unit j ∈ Dn n :=
  LineSystem.add_single_mem_Dn i j h

/-- Step `rCright`: two coordinate axes are perpendicular. -/
theorem lineAngle_unit_unit {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    lineAngle (unit i) (unit j) = Real.pi / 2 ∧
      ⟪unit i, unit j⟫ ^ 2 < ⟪unit i, unit i⟫ * ⟪unit j, unit j⟫ := by
  refine ⟨lineAngle_eq_pi_div_two (inner_unit_of_ne h), ?_⟩
  rw [inner_unit_of_ne h, inner_unit_self, inner_unit_self]
  norm_num

/-- Step `rCfortyfive`: an axis and a diagonal through it meet at forty-five degrees. -/
theorem lineAngle_unit_add_unit {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    lineAngle (unit i) (unit i + unit j) = Real.pi / 4 ∧
      ⟪unit i, unit i + unit j⟫ ^ 2 < ⟪unit i, unit i⟫ * ⟪unit i + unit j, unit i + unit j⟫ := by
  have h₁ : ⟪unit i, unit i + unit j⟫ = (1 : ℝ) := by
    rw [inner_add_right, inner_unit_self, inner_unit_of_ne h, add_zero]
  have h₂ : ⟪unit i + unit j, unit i + unit j⟫ = (2 : ℝ) := by
    rw [inner_add_left, inner_add_right, inner_add_right, inner_unit_self, inner_unit_self,
      inner_unit_of_ne h, inner_unit_of_ne (Ne.symm h)]
    norm_num
  have hz (k : Fin n) : unit k ≠ 0 := by
    intro hk
    have := inner_unit_self k
    rw [hk, inner_zero_left] at this
    norm_num at this
  have hs : unit i + unit j ≠ 0 := by
    intro hk
    rw [hk, inner_zero_left] at h₂
    norm_num at h₂
  refine ⟨lineAngle_eq_pi_div_four (hz i) hs ?_, ?_⟩ <;>
    rw [h₁, h₂, inner_unit_self] <;> norm_num

/-- Step `rCsixty`: two diagonals sharing one coordinate meet at sixty degrees. -/
theorem lineAngle_add_add {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    lineAngle (unit i + unit j) (unit i + unit k) = Real.pi / 3 ∧
      ⟪unit i + unit j, unit i + unit k⟫ ^ 2 <
        ⟪unit i + unit j, unit i + unit j⟫ * ⟪unit i + unit k, unit i + unit k⟫ := by
  have hd {a b : Fin n} (hab : a ≠ b) : ⟪unit a + unit b, unit a + unit b⟫ = (2 : ℝ) := by
    rw [inner_add_left, inner_add_right, inner_add_right, inner_unit_self, inner_unit_self,
      inner_unit_of_ne hab, inner_unit_of_ne (Ne.symm hab)]
    norm_num
  have h₁ : ⟪unit i + unit j, unit i + unit k⟫ = (1 : ℝ) := by
    rw [inner_add_left, inner_add_right, inner_add_right, inner_unit_self,
      inner_unit_of_ne hik, inner_unit_of_ne (Ne.symm hij), inner_unit_of_ne hjk]
    norm_num
  have hs {a b : Fin n} (hab : a ≠ b) : unit a + unit b ≠ 0 := by
    intro he
    have := hd hab
    rw [he, inner_zero_left] at this
    norm_num at this
  refine ⟨lineAngle_eq_pi_div_three (hs hij) (hs hik) ?_, ?_⟩ <;>
    rw [h₁, hd hij, hd hik] <;> norm_num

/-- Step `rCallowedBF` for Bₙ: the squared lengths are 1 and 2. -/
theorem Bn_lengths {n : ℕ} {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ Bn n) :
    ⟪r, r⟫ = 1 ∨ ⟪r, r⟫ = 2 * 1 := by
  rcases hr with hr | hr
  · left
    rw [inner_self_of_mem_axisRoots hr]
    norm_num
  · right
    rw [(LineSystem.Dn n).inner_self r hr]
    norm_num

/-- Step `rCallowedBF` for Cₙ: the squared lengths are 2 and 4. -/
theorem Cn_lengths {n : ℕ} {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ Cn n) :
    ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 2 * 2 := by
  rcases hr with hr | hr
  · right
    rw [inner_self_of_mem_axisRoots hr]
    norm_num
  · exact Or.inl ((LineSystem.Dn n).inner_self r hr)

/-- Step `rCallowedG`: the squared lengths of G₂ are 2 and 6. -/
theorem G₂_lengths {r : g₂Space} (hr : r ∈ G₂) : ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 3 * 2 := by
  rw [Submodule.coe_inner]
  rcases gRoots_inner_self (x := (r : EuclideanSpace ℝ (Fin 3))) hr with h | h
  · exact Or.inl h
  · right
    rw [h]
    norm_num

-- Remark 3.11, thm:C
/-- Step `rCallowedBF` of blueprint Theorem C for Bₙ: distinct lines meet at 90, 60 or 45 degrees.
-/
theorem lineAngles_Bn_subset (n : ℕ) :
    lineAngles (Bn n) ⊆ {Real.pi / 2, Real.pi / 3, Real.pi / 4} :=
  (Bn_isRootSet n).lineAngles_subset_of_lengths_two one_pos fun _ hr ↦ Bn_lengths hr

/-- Step `rCclassicalsame`: Bₙ and Cₙ have the same line angles, since they have the same
lines. -/
theorem lineAngles_Bn_eq_Cn (n : ℕ) : lineAngles (Bn n) = lineAngles (Cn n) :=
  lineAngles_eq_of_rootLines_eq (Bn_isRootSet n) (Cn_isRootSet n) (Bn_Cn_same_lines n)

-- Remark 3.11, thm:C
/-- Step `rCallowedBF` of blueprint Theorem C for F₄: distinct lines meet at 90, 60 or 45 degrees.
-/
theorem lineAngles_F₄_subset :
    lineAngles F₄ ⊆ {Real.pi / 2, Real.pi / 3, Real.pi / 4} :=
  F₄_isRootSet.lineAngles_subset_of_lengths_two one_pos fun _ hr ↦
    (F₄_inner_self hr).imp id fun h ↦ h.trans (by norm_num)

-- Remark 3.11, thm:C
/-- Step `rCallowedG` of blueprint Theorem C for G₂: distinct lines meet at 90, 60 or 30 degrees. -/
theorem lineAngles_G₂_subset :
    lineAngles G₂ ⊆ {Real.pi / 2, Real.pi / 3, Real.pi / 6} :=
  G₂_isRootSet.lineAngles_subset_of_lengths_three (by norm_num) fun _ hr ↦ G₂_lengths hr

/-- Steps `rCright`, `rCfortyfive`: in rank at least two, the Bₙ lines meet at 90 and
at 45 degrees. -/
theorem pi_div_two_pi_div_four_mem_lineAngles_Bn {n : ℕ} (hn : 2 ≤ n) :
    Real.pi / 2 ∈ lineAngles (Bn n) ∧ Real.pi / 4 ∈ lineAngles (Bn n) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  obtain ⟨ha, hlt⟩ := lineAngle_unit_unit hij
  obtain ⟨hb, hlt'⟩ := lineAngle_unit_add_unit hij
  constructor
  · rw [← ha]
    exact lineAngle_mem_lineAngles (Or.inl (unit_mem_axisRoots_one i))
      (Or.inl (unit_mem_axisRoots_one j)) hlt
  · rw [← hb]
    exact lineAngle_mem_lineAngles (Or.inl (unit_mem_axisRoots_one i))
      (Or.inr (unit_add_unit_mem_Dn hij)) hlt'

/-- Step `rCsixty`: in rank at least three, two Bₙ lines meet at 60 degrees. -/
theorem pi_div_three_mem_lineAngles_Bn {n : ℕ} (hn : 3 ≤ n) : Real.pi / 3 ∈ lineAngles (Bn n) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hik : i ≠ k := by simp [i, k, Fin.ext_iff]
  have hjk : j ≠ k := by simp [j, k, Fin.ext_iff]
  obtain ⟨ha, hlt⟩ := lineAngle_add_add hij hik hjk
  rw [← ha]
  exact lineAngle_mem_lineAngles (Or.inr (unit_add_unit_mem_Dn hij))
    (Or.inr (unit_add_unit_mem_Dn hik)) hlt

/-- The integer coordinates of the eight B₂ roots, for step `rCtwoangles`. -/
def b₂Entries : (Fin 2 × Bool) ⊕ LineSystem.DnIndex 2 → Fin 2 → ℤ
  | .inl a => fun k ↦ if k = a.1 then LineSystem.rootSign a.2 else 0
  | .inr a => LineSystem.dnRoot a

/-- Every B₂ root has the integer coordinates of `b₂Entries` (`rCtwoangles`). -/
theorem exists_b₂Entries {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Bn 2) :
    ∃ a, x = LineSystem.integerVector 1 (b₂Entries a) := by
  rcases hx with ⟨i, rfl | rfl⟩ | ⟨a, rfl⟩
  · refine ⟨.inl (i, false), ?_⟩
    ext k
    by_cases hk : k = i <;>
      simp [b₂Entries, LineSystem.integerVector, LineSystem.rootSign, unit, hk]
  · refine ⟨.inl (i, true), ?_⟩
    ext k
    by_cases hk : k = i <;>
      simp [b₂Entries, LineSystem.integerVector, LineSystem.rootSign, unit, hk]
  · exact ⟨.inr a, rfl⟩

/-- Steps `rCtwoaxes`--`rCtwomixed`: no two B₂ roots have squared cosine one quarter,
checked on all sixty-four pairs of integer coordinates. -/
theorem b₂Entries_ne : ∀ a b : (Fin 2 × Bool) ⊕ LineSystem.DnIndex 2,
    4 * LineSystem.integerInner (b₂Entries a) (b₂Entries b) ^ 2 ≠
      LineSystem.integerInner (b₂Entries a) (b₂Entries a) *
        LineSystem.integerInner (b₂Entries b) (b₂Entries b) := by
  decide +kernel

/-- Step `rCtwoangles`: in rank two the classical lines have no sixty-degree pair. -/
theorem pi_div_three_notMem_lineAngles_B₂ : Real.pi / 3 ∉ lineAngles (Bn 2) := by
  rintro ⟨r, hr, s, hs, -, h⟩
  have he := inner_sq_of_lineAngle_eq_pi_div_three ((Bn_isRootSet 2).ne_zero hr)
    ((Bn_isRootSet 2).ne_zero hs) h
  obtain ⟨a, rfl⟩ := exists_b₂Entries hr
  obtain ⟨b, rfl⟩ := exists_b₂Entries hs
  simp only [LineSystem.inner_integerVector, one_mul] at he
  exact b₂Entries_ne a b (by exact_mod_cast he)

/-- Steps `rCright`, `rCfortyfive`, `rCsixty` for F₄: its lines meet at 90, 60 and
45 degrees. -/
theorem angles_mem_lineAngles_F₄ :
    Real.pi / 2 ∈ lineAngles F₄ ∧ Real.pi / 3 ∈ lineAngles F₄ ∧
      Real.pi / 4 ∈ lineAngles F₄ := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have hax (i : Fin 4) : unit i ∈ F₄ := Or.inl (Or.inr (unit_mem_axisRoots_one i))
  have hd {i j : Fin 4} (h : i ≠ j) : unit i + unit j ∈ F₄ :=
    Or.inl (Or.inl (unit_add_unit_mem_Dn h))
  obtain ⟨ha, hlt⟩ := lineAngle_unit_unit h01
  obtain ⟨hb, hlt'⟩ := lineAngle_add_add h01 h02 h12
  obtain ⟨hc, hlt''⟩ := lineAngle_unit_add_unit h01
  refine ⟨?_, ?_, ?_⟩
  · rw [← ha]
    exact lineAngle_mem_lineAngles (hax 0) (hax 1) hlt
  · rw [← hb]
    exact lineAngle_mem_lineAngles (hd h01) (hd h02) hlt'
  · rw [← hc]
    exact lineAngle_mem_lineAngles (hax 0) (hd h01) hlt''

/-- Steps `rCGsixty`--`rCGthirty` of Remark 3.11: a coordinate difference lies in the
zero-sum plane of G₂. -/
theorem unit_sub_unit_mem_g₂Space (i j : Fin 3) : unit i - unit j ∈ g₂Space := by
  rw [mem_g₂Space]
  fin_cases i <;> fin_cases j <;> simp [unit]

/-- Steps `rCGsixty`--`rCGthirty` of Remark 3.11: a long G₂ root lies in the zero-sum plane. -/
theorem g₂LongRoot_mem_g₂Space (i : Fin 3) : g₂LongRoot i ∈ g₂Space := by
  rw [mem_g₂Space]
  fin_cases i <;> simp [g₂LongRoot_apply] <;> norm_num

/-- Steps `rCGsixty`, `rCGright`, `rCGthirty`: the G₂ lines meet at 90, 60 and
30 degrees. -/
theorem angles_mem_lineAngles_G₂ :
    Real.pi / 2 ∈ lineAngles G₂ ∧ Real.pi / 3 ∈ lineAngles G₂ ∧
      Real.pi / 6 ∈ lineAngles G₂ := by
  let a : g₂Space := ⟨unit 0 - unit 1, unit_sub_unit_mem_g₂Space 0 1⟩
  let b : g₂Space := ⟨unit 0 - unit 2, unit_sub_unit_mem_g₂Space 0 2⟩
  let c : g₂Space := ⟨unit 1 - unit 2, unit_sub_unit_mem_g₂Space 1 2⟩
  let l : g₂Space := ⟨g₂LongRoot 0, g₂LongRoot_mem_g₂Space 0⟩
  have ha : a ∈ G₂ := Or.inl (LineSystem.sub_single_mem_An 0 1 (by decide))
  have hb : b ∈ G₂ := Or.inl (LineSystem.sub_single_mem_An 0 2 (by decide))
  have hc : c ∈ G₂ := Or.inl (LineSystem.sub_single_mem_An 1 2 (by decide))
  have hl : l ∈ G₂ := Or.inr ⟨0, Or.inl rfl⟩
  have hsub (i j p q : Fin 3) : ⟪unit i - unit j, unit p - unit q⟫ =
      ((if i = p then 1 else 0) - (if i = q then 1 else 0) - (if j = p then 1 else 0) +
        (if j = q then 1 else 0) : ℝ) := by
    simp only [inner_sub_left, inner_sub_right, inner_unit]
    ring
  have haa : ⟪a, a⟫ = 2 := by
    rw [Submodule.coe_inner, hsub]
    norm_num [Fin.ext_iff]
  have hbb : ⟪b, b⟫ = 2 := by
    rw [Submodule.coe_inner, hsub]
    norm_num [Fin.ext_iff]
  have hcc : ⟪c, c⟫ = 2 := by
    rw [Submodule.coe_inner, hsub]
    norm_num [Fin.ext_iff]
  have hab : ⟪a, b⟫ = 1 := by
    rw [Submodule.coe_inner, hsub]
    norm_num [Fin.ext_iff]
  have hll : ⟪l, l⟫ = 6 := by
    rw [Submodule.coe_inner]
    exact g₂LongRoot_inner_self 0
  have hlc : ⟪l, c⟫ = 0 := by
    rw [Submodule.coe_inner, inner_g₂LongRoot]
    simp [c, unit]
  have hla : ⟪l, a⟫ = 3 := by
    rw [Submodule.coe_inner, inner_g₂LongRoot]
    simp [a, unit]
  have hz {x : g₂Space} (hx : ⟪x, x⟫ = 2 ∨ ⟪x, x⟫ = 6) : x ≠ 0 := by
    rintro rfl
    rw [inner_zero_left] at hx
    norm_num at hx
  refine ⟨?_, ?_, ?_⟩
  · rw [← lineAngle_eq_pi_div_two hlc]
    exact lineAngle_mem_lineAngles hl hc (by rw [hlc, hll, hcc]; norm_num)
  · rw [← lineAngle_eq_pi_div_three (hz (Or.inl haa)) (hz (Or.inl hbb))
      (by rw [hab, haa, hbb]; norm_num)]
    exact lineAngle_mem_lineAngles ha hb (by rw [hab, haa, hbb]; norm_num)
  · rw [← lineAngle_eq_pi_div_six (hz (Or.inr hll)) (hz (Or.inl haa))
      (by rw [hla, hll, haa]; norm_num)]
    exact lineAngle_mem_lineAngles hl ha (by rw [hla, hll, haa]; norm_num)

-- Remark 3.11, thm:C
/-- Steps `rCallowed`, `rCoccurrence` of blueprint Theorem C for the classical lines: for `n ≥ 3`
all three angles 90, 60 and 45 degrees occur. -/
theorem lineAngles_Bn {n : ℕ} (hn : 3 ≤ n) :
    lineAngles (Bn n) = {Real.pi / 2, Real.pi / 3, Real.pi / 4} := by
  refine Set.Subset.antisymm (lineAngles_Bn_subset n) ?_
  obtain ⟨h₂, h₄⟩ := pi_div_two_pi_div_four_mem_lineAngles_Bn (by omega : 2 ≤ n)
  rintro θ (rfl | rfl | rfl)
  exacts [h₂, pi_div_three_mem_lineAngles_Bn hn, h₄]

-- Remark 3.11, thm:C
/-- Step `rCtwoangles` of blueprint Theorem C: for `n = 2` the classical lines meet only at 90 and
45 degrees. -/
theorem lineAngles_B₂ : lineAngles (Bn 2) = {Real.pi / 2, Real.pi / 4} := by
  apply Set.Subset.antisymm
  · intro θ hθ
    rcases lineAngles_Bn_subset 2 hθ with h | h | h
    · exact Or.inl h
    · exact (pi_div_three_notMem_lineAngles_B₂ (h ▸ hθ)).elim
    · exact Or.inr h
  · obtain ⟨h₂, h₄⟩ := pi_div_two_pi_div_four_mem_lineAngles_Bn le_rfl
    rintro θ (rfl | rfl)
    exacts [h₂, h₄]

-- Remark 3.11, thm:C
/-- Steps `rCallowedBF`, `rCoccurrence` of blueprint Theorem C for F₄: all three angles 90, 60 and
45 degrees occur, and no other. -/
theorem lineAngles_F₄ : lineAngles F₄ = {Real.pi / 2, Real.pi / 3, Real.pi / 4} := by
  refine Set.Subset.antisymm lineAngles_F₄_subset ?_
  obtain ⟨h₂, h₃, h₄⟩ := angles_mem_lineAngles_F₄
  rintro θ (rfl | rfl | rfl)
  exacts [h₂, h₃, h₄]

-- Remark 3.11, thm:C
/-- Steps `rCallowedG`, `rCoccurrence` of blueprint Theorem C for G₂: all three angles 90, 60 and
30 degrees occur, and no other. -/
theorem lineAngles_G₂ : lineAngles G₂ = {Real.pi / 2, Real.pi / 3, Real.pi / 6} := by
  refine Set.Subset.antisymm lineAngles_G₂_subset ?_
  obtain ⟨h₂, h₃, h₆⟩ := angles_mem_lineAngles_G₂
  rintro θ (rfl | rfl | rfl)
  exacts [h₂, h₃, h₆]

end RootSetModel
