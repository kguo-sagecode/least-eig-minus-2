/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Intersections

/-!
# Common neighbours in the Hall–Connor block graph

The four-fibre count `hc:lem:common` (Hall–Connor Lemma 4.2 at block size five), used in
Remark 5.12 and Example 5.13 of [CGSS].
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

/-- The four intersection fibres of `hc:lem:common` ([CGSS], Remark 5.12). -/
def intersectionPairCount (D : Design P B 15 5 21 7 2) (X Y : B) (i j : ℕ) : ℕ :=
  (((Finset.univ.erase X).erase Y).filter fun Z ↦
    (D.block X ∩ D.block Z).card = i ∧ (D.block Y ∩ D.block Z).card = j).card

variable (D : Design P B 15 5 21 7 2)

/-- Grouping the four fibres in `hcCommonTotal`–`hcCommonProduct`
([CGSS], Remark 5.12). -/
theorem sum_intersectionPairCount (X Y : B) (f : ℕ → ℕ → ℤ) :
    f 1 1 * D.intersectionPairCount X Y 1 1 +
      f 1 2 * D.intersectionPairCount X Y 1 2 +
      f 2 1 * D.intersectionPairCount X Y 2 1 +
      f 2 2 * D.intersectionPairCount X Y 2 2 =
    ∑ Z ∈ (Finset.univ.erase X).erase Y,
      f (D.block X ∩ D.block Z).card (D.block Y ∩ D.block Z).card := by
  have hbound (Z : B) (hZ : Z ∈ (Finset.univ.erase X).erase Y) :
      ((D.block X ∩ D.block Z).card, (D.block Y ∩ D.block Z).card) ∈
        ({1, 2} : Finset ℕ) ×ˢ ({1, 2} : Finset ℕ) := by
    have hXZ := (Finset.mem_erase.mp (Finset.mem_erase.mp hZ).2).1.symm
    have hYZ := (Finset.mem_erase.mp hZ).1.symm
    simpa only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] using
      And.intro (D.inter_card_eq_one_or_two hXZ) (D.inter_card_eq_one_or_two hYZ)
  have h := Finset.sum_fiberwise_of_maps_to' hbound (fun ij ↦ f ij.1 ij.2)
  simpa [Finset.sum_product, intersectionPairCount, mul_comm, add_assoc] using h

/-- The four explicit equations of `hcCommonTotal`, `hcCommonFirst`, `hcCommonSecond`,
and `hcCommonProduct` ([CGSS], Remark 5.12). Both diagonal terms of `G²` are removed. -/
theorem intersection_pair_count_equations {X Y : B} (hXY : X ≠ Y) :
    let a : ℤ := D.intersectionPairCount X Y 1 1
    let b : ℤ := D.intersectionPairCount X Y 1 2
    let c : ℤ := D.intersectionPairCount X Y 2 1
    let d : ℤ := D.intersectionPairCount X Y 2 2
    let s : ℤ := (D.block X ∩ D.block Y).card
    a + b + c + d = 19 ∧
      a + b + 2 * c + 2 * d = 30 - s ∧
      a + 2 * b + c + 2 * d = 30 - s ∧
      a + 2 * b + 2 * c + 4 * d = 50 - 5 * s := by
  dsimp only
  have hY : Y ∈ Finset.univ.erase X := Finset.mem_erase.mpr ⟨hXY.symm, Finset.mem_univ Y⟩
  have hX : X ∈ Finset.univ.erase Y := Finset.mem_erase.mpr ⟨hXY, Finset.mem_univ X⟩
  have hcard : ((Finset.univ.erase X).erase Y).card = 19 := by
    simp [Finset.card_erase_of_mem hY, D.card_blocks]
  have hfirst := Finset.sum_erase_add (Finset.univ.erase X)
    (fun Z ↦ ((D.block X ∩ D.block Z).card : ℤ)) hY
  rw [(D.intersection_moments_sum X).2.1] at hfirst
  have hsecond := Finset.sum_erase_add (Finset.univ.erase Y)
    (fun Z ↦ ((D.block Y ∩ D.block Z).card : ℤ)) hX
  rw [(D.intersection_moments_sum Y).2.1, Finset.erase_right_comm,
    Finset.inter_comm (D.block Y) (D.block X)] at hsecond
  have hproduct :
      ∑ Z, ((D.block X ∩ D.block Z).card : ℤ) * (D.block Y ∩ D.block Z).card =
        5 * ((D.block X ∩ D.block Y).card : ℤ) + 50 := by
    have h := congrFun (congrFun D.G_mul_G X) Y
    simp only [Matrix.mul_apply, D.G_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, mul_one,
      Finset.inter_comm (D.block _) (D.block Y)] at h
    rw [Finset.inter_comm (D.block Y) (D.block X)] at h
    exact_mod_cast h
  have hremoveX := Finset.sum_erase_add Finset.univ
    (fun Z ↦ ((D.block X ∩ D.block Z).card : ℤ) * (D.block Y ∩ D.block Z).card)
    (Finset.mem_univ X)
  have hremoveY := Finset.sum_erase_add (Finset.univ.erase X)
    (fun Z ↦ ((D.block X ∩ D.block Z).card : ℤ) * (D.block Y ∩ D.block Z).card) hY
  simp only [Finset.inter_self, D.card_block, hproduct,
    Finset.inter_comm (D.block Y) (D.block X)] at hremoveX hremoveY
  norm_num only at hremoveX hremoveY
  have h₀ := D.sum_intersectionPairCount X Y (fun _ _ ↦ 1)
  have h₁ := D.sum_intersectionPairCount X Y (fun i _ ↦ i)
  have h₂ := D.sum_intersectionPairCount X Y (fun _ j ↦ j)
  have h₃ := D.sum_intersectionPairCount X Y (fun i j ↦ (i : ℤ) * j)
  norm_num only [Finset.sum_const, hcard, Nat.cast_ofNat, nsmul_eq_mul, one_mul] at h₀ h₁ h₂ h₃
  exact ⟨h₀, by linarith, by linarith, by linarith⟩

/-- The intersection table `hc:lem:common` (Hall–Connor Lemma 4.2 at `k = 5`;
[CGSS], Remark 5.12): rows `(5,4,4,6)` and `(4,6,6,3)`. -/
theorem intersection_pair_counts {X Y : B} (hXY : X ≠ Y) :
    let s := (D.block X ∩ D.block Y).card
    D.intersectionPairCount X Y 1 1 = (if s = 1 then 5 else 4) ∧
      D.intersectionPairCount X Y 1 2 = (if s = 1 then 4 else 6) ∧
      D.intersectionPairCount X Y 2 1 = (if s = 1 then 4 else 6) ∧
      D.intersectionPairCount X Y 2 2 = (if s = 1 then 6 else 3) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := D.intersection_pair_count_equations hXY
  rcases D.inter_card_eq_one_or_two hXY with h | h <;>
    simp [h] at h₁ h₂ h₃ ⊢ <;> omega

/-- Adjacent labels have five common neighbours and distinct nonadjacent labels have four,
`hcCommonNeighbours` of `hc:lem:common` ([CGSS], Remark 5.12). -/
theorem card_commonNeighbors {X Y : B} (hXY : X ≠ Y) :
    (D.Z.commonNeighbors X Y).ncard = if D.Z.Adj X Y then 5 else 4 := by
  have he : D.Z.commonNeighbors X Y =
      ↑(((Finset.univ.erase X).erase Y).filter fun Z ↦
        (D.block X ∩ D.block Z).card = 1 ∧ (D.block Y ∩ D.block Z).card = 1) := by
    ext Z
    simp [SimpleGraph.mem_commonNeighbors, Design.Z, ne_comm, and_comm, and_left_comm, and_assoc]
  rw [he, Set.ncard_coe_finset]
  have h := (D.intersection_pair_counts hXY).1
  by_cases hadj : D.Z.Adj X Y
  · rw [ite_eq_left hadj]
    simpa only [intersectionPairCount, ite_eq_left hadj.2] using h
  · rw [ite_eq_right hadj]
    have hs : (D.block X ∩ D.block Y).card ≠ 1 := fun hs ↦ hadj ⟨hXY, hs⟩
    simpa only [intersectionPairCount, ite_eq_right hs] using h

end Design
