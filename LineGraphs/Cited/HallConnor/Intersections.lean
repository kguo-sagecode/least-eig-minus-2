/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Incidence

/-!
# Intersection moments and the block graph

The lemmas `hc:lem:moments` and `hc:lem:intersections` of the Hall–Connor blueprint,
for the nonexistence assertion in Remark 5.12 and Example 5.13 of [CGSS].
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

/-- The intersection multiplicities of `hc:lem:moments` ([CGSS], Remark 5.12).
The distinguished label itself is excluded, even when different labels give equal blocks. -/
def intersectionCount (D : Design P B 15 5 21 7 2) (X : B) (i : ℕ) : ℕ :=
  ((Finset.univ.erase X).filter fun Y ↦ (D.block X ∩ D.block Y).card = i).card

variable (D : Design P B 15 5 21 7 2)

/-- Grouping block labels by intersection size (`hcMomZero`–`hcMomTwo`;
[CGSS], Remark 5.12). All weights and sums are integral. -/
theorem sum_intersectionCount (X : B) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range 6, f i * (D.intersectionCount X i : ℤ) =
      ∑ Y ∈ Finset.univ.erase X, f (D.block X ∩ D.block Y).card := by
  have hbound (Y : B) (_hY : Y ∈ Finset.univ.erase X) :
      (D.block X ∩ D.block Y).card ∈ Finset.range 6 := by
    have h := Finset.card_le_card (Finset.inter_subset_left (s₁ := D.block X)
      (s₂ := D.block Y))
    rw [D.card_block] at h
    simpa using Nat.lt_succ_of_le h
  simpa [intersectionCount, mul_comm] using
    (Finset.sum_fiberwise_of_maps_to' hbound f)

/-- The incidence count before deleting the distinguished block (`hcMomOne`;
[CGSS], Remark 5.12). -/
theorem sum_inter_card (X : B) :
    ∑ Y, ((D.block X ∩ D.block Y).card : ℤ) = 35 := by
  have h : ∑ Y, ((D.block X ∩ D.block Y).card : ℚ) = 35 := by
    simpa only [D.G_apply] using D.G_row_sum X
  exact_mod_cast h

/-- The ordered-pair count before deleting the distinguished block (`hcMomTwo`;
[CGSS], Remark 5.12). Expanding the diagonal of `G²` counts ordered point pairs. -/
theorem sum_sq_inter_card (X : B) :
    ∑ Y, ((D.block X ∩ D.block Y).card : ℤ) ^ 2 = 75 := by
  have h := congrFun (congrFun D.G_mul_G X) X
  have he : ∑ Y, ((D.block X ∩ D.block Y).card : ℚ) ^ 2 = 75 := by
    norm_num [Matrix.mul_apply, D.G_apply, Finset.inter_comm, D.card_block, pow_two] at h ⊢
    exact h
  exact_mod_cast he

/-- The ungrouped moments of `hc:lem:moments`, after deleting the distinguished label
([CGSS], Remark 5.12). The subtraction in the second moment is in `ℤ`. -/
theorem intersection_moments_sum (X : B) :
    (Finset.univ.erase X).card = 20 ∧
    (∑ Y ∈ Finset.univ.erase X, ((D.block X ∩ D.block Y).card : ℤ)) = 30 ∧
    (∑ Y ∈ Finset.univ.erase X,
      ((D.block X ∩ D.block Y).card : ℤ) *
        (((D.block X ∩ D.block Y).card : ℤ) - 1)) = 20 := by
  have h₁ := Finset.sum_erase_add Finset.univ
    (fun Y ↦ ((D.block X ∩ D.block Y).card : ℤ)) (Finset.mem_univ X)
  have h₂ := Finset.sum_erase_add Finset.univ
    (fun Y ↦ ((D.block X ∩ D.block Y).card : ℤ) ^ 2) (Finset.mem_univ X)
  simp only [Finset.inter_self, D.card_block, D.sum_inter_card, D.sum_sq_inter_card] at h₁ h₂
  norm_num only at h₁ h₂
  refine ⟨by simp [D.card_blocks], by linarith, ?_⟩
  simp only [mul_sub, mul_one, ← pow_two, Finset.sum_sub_distrib]
  linarith

/-- The three integral intersection moments `hc:lem:moments` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13). -/
theorem intersection_moments_15_5_2 (X : B) :
    (∑ i ∈ Finset.range 6, (D.intersectionCount X i : ℤ)) = 20 ∧
    (∑ i ∈ Finset.range 6, (i : ℤ) * D.intersectionCount X i) = 30 ∧
    (∑ i ∈ Finset.range 6, (i : ℤ) * ((i : ℤ) - 1) * D.intersectionCount X i) = 20 ∧
    (∑ Y ∈ Finset.univ.erase X, ((D.block X ∩ D.block Y).card : ℤ)) = 30 := by
  obtain ⟨h₀, h₁, h₂⟩ := D.intersection_moments_sum X
  refine ⟨?_, ?_, ?_, h₁⟩
  · simpa [h₀] using D.sum_intersectionCount X (fun _ ↦ 1)
  · exact (D.sum_intersectionCount X (fun i ↦ (i : ℤ))).trans h₁
  · exact (D.sum_intersectionCount X (fun i ↦ (i : ℤ) * ((i : ℤ) - 1))).trans h₂

/-- Distinct block labels meet in one or two points: `hcInterPolynomial` and
`hcInterSupport` of `hc:lem:intersections` (Hall–Connor Lemma 4.1 at `k = 5`;
[CGSS], Remark 5.12 and Example 5.13). -/
theorem inter_card_eq_one_or_two {X Y : B} (hXY : X ≠ Y) :
    (D.block X ∩ D.block Y).card = 1 ∨ (D.block X ∩ D.block Y).card = 2 := by
  let f : B → ℤ := fun Z ↦ (D.block X ∩ D.block Z).card
  obtain ⟨h₀, h₁, h₂⟩ := D.intersection_moments_sum X
  have hsum : ∑ Z ∈ Finset.univ.erase X, (f Z - 1) * (f Z - 2) = 0 := by
    have he (Z : B) : (f Z - 1) * (f Z - 2) = f Z * (f Z - 1) - 2 * f Z + 2 := by
      ring
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const]
    change (∑ Z ∈ Finset.univ.erase X, f Z * (f Z - 1)) -
      2 * (∑ Z ∈ Finset.univ.erase X, f Z) + (Finset.univ.erase X).card • (2 : ℤ) = 0
    rw [h₀, h₁, h₂]
    norm_num
  have hnonneg (Z : B) : 0 ≤ (f Z - 1) * (f Z - 2) := by
    have hn : 0 ≤ f Z := Int.natCast_nonneg _
    by_cases hz : f Z = 0
    · norm_num [hz]
    by_cases ho : f Z = 1
    · simp [ho]
    exact mul_nonneg (by omega) (by omega)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun Z _ ↦ hnonneg Z)).mp hsum Y
    (Finset.mem_erase.mpr ⟨hXY.symm, Finset.mem_univ Y⟩)
  rcases mul_eq_zero.mp hzero with h | h
  · left
    have he : ((D.block X ∩ D.block Y).card : ℤ) = 1 := sub_eq_zero.mp h
    exact_mod_cast he
  · right
    have he : ((D.block X ∩ D.block Y).card : ℤ) = 2 := sub_eq_zero.mp h
    exact_mod_cast he

/-- The zero fibres in `hcInterSupport` ([CGSS], Remark 5.12). -/
theorem intersectionCount_eq_zero (X : B) {i : ℕ} (hi₁ : i ≠ 1) (hi₂ : i ≠ 2) :
    D.intersectionCount X i = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro Y hY
  obtain ⟨hY, hi⟩ := Finset.mem_filter.mp hY
  have hXY : X ≠ Y := (Finset.mem_erase.mp hY).1.symm
  rcases D.inter_card_eq_one_or_two hXY with h | h
  · exact hi₁ (hi.symm.trans h)
  · exact hi₂ (hi.symm.trans h)

/-- The two nonzero intersection multiplicities in `hcInterCounts`
([CGSS], Remark 5.12): there are ten labels of each kind. -/
theorem intersectionCount_one_two (X : B) :
    D.intersectionCount X 1 = 10 ∧ D.intersectionCount X 2 = 10 := by
  obtain ⟨h₀, h₁, _⟩ := D.intersection_moments_15_5_2 X
  have hz₀ := D.intersectionCount_eq_zero X (i := 0) (by decide) (by decide)
  have hz₃ := D.intersectionCount_eq_zero X (i := 3) (by decide) (by decide)
  have hz₄ := D.intersectionCount_eq_zero X (i := 4) (by decide) (by decide)
  have hz₅ := D.intersectionCount_eq_zero X (i := 5) (by decide) (by decide)
  norm_num [Finset.sum_range_succ, hz₀, hz₃, hz₄, hz₅] at h₀ h₁
  omega

/-- Decidable adjacency for the block graph (`hc:def:graph`; [CGSS], Remark 5.12). -/
instance decidableRelZ : DecidableRel D.Z.Adj := fun X Y ↦
  inferInstanceAs (Decidable (X ≠ Y ∧ (D.block X ∩ D.block Y).card = 1))

/-- Every block has ten neighbours, `hc:lem:intersections` (Hall–Connor Lemma 4.1 at
`k = 5`; [CGSS], Remark 5.12). -/
theorem card_neighbors (X : B) : (D.Z.neighborFinset X).card = 10 := by
  have he : D.Z.neighborFinset X =
      (Finset.univ.erase X).filter (fun Y ↦ (D.block X ∩ D.block Y).card = 1) := by
    ext Y
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Z, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true, ne_comm]
  rw [he]
  exact (D.intersectionCount_one_two X).1

/-- Exactly ten other labels meet a block in two points, `hc:lem:intersections`
(Hall–Connor Lemma 4.1 at `k = 5`; [CGSS], Remark 5.12). -/
theorem card_filter_inter_card_eq_two (X : B) :
    ((Finset.univ.erase X).filter (fun Y ↦ (D.block X ∩ D.block Y).card = 2)).card = 10 :=
  (D.intersectionCount_one_two X).2

end Design
