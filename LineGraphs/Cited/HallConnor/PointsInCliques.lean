/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.CliqueCounts

/-!
# Point multiplicities in a six-clique

The sum-of-squares proof `hc:lem:point-clique` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13).
-/

open scoped BigOperators

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- Every point lies in two blocks of each six-clique, `hc:lem:point-clique`
([CGSS], Remark 5.12 and Example 5.13). Both moment subtractions are taken in `ℤ`. -/
theorem card_blocksThrough_in_sixClique {S : Finset B} (hS : S ∈ D.sixCliques) (p : P) :
    (S.filter (fun X ↦ p ∈ D.block X)).card = 2 := by
  have hs := (D.mem_sixCliques S).mp hS
  let m : P → ℕ := fun q ↦ (S.filter (fun X ↦ q ∈ D.block X)).card
  have hfirstNat : ∑ q, m q = 30 := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun q X ↦ q ∈ D.block X) (s := Finset.univ) (t := S)
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow, D.card_block, hs.card_eq, m] using h
  have hf (q : P) :
      S.offDiag.filter (fun XY ↦ q ∈ D.block XY.1 ∧ q ∈ D.block XY.2) =
        (S.filter (fun X ↦ q ∈ D.block X)).offDiag := by
    ext XY
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    tauto
  have hpairs (XY : B × B) (hXY : XY ∈ S.offDiag) :
      (Finset.univ.filter (fun q ↦ q ∈ D.block XY.1 ∧ q ∈ D.block XY.2)).card = 1 := by
    have he : Finset.univ.filter (fun q ↦ q ∈ D.block XY.1 ∧ q ∈ D.block XY.2) =
        D.block XY.1 ∩ D.block XY.2 := by ext q; simp
    rw [he]
    obtain ⟨hX, hY, hne⟩ := Finset.mem_offDiag.mp hXY
    exact (hs.isClique hX hY hne).2
  have hsecondNat : (∑ q, (m q * m q - m q)) = 30 := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun q (XY : B × B) ↦ q ∈ D.block XY.1 ∧ q ∈ D.block XY.2)
      (s := Finset.univ) (t := S.offDiag)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, hf, Finset.offDiag_card] at h
    calc
      _ = ∑ XY ∈ S.offDiag,
          (Finset.univ.filter (fun q ↦ q ∈ D.block XY.1 ∧ q ∈ D.block XY.2)).card := h
      _ = ∑ _ ∈ S.offDiag, 1 := Finset.sum_congr rfl hpairs
      _ = 30 := by simp [Finset.offDiag_card, hs.card_eq]
  have hcast (n : ℕ) : ((n * n - n : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
    rw [← Nat.mul_sub_one]
    cases n with
    | zero => norm_num
    | succ n => simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_succ,
        add_sub_cancel_right]
  have hfirst : ∑ q, (m q : ℤ) = 30 := by exact_mod_cast hfirstNat
  have hsecond : (∑ q, (m q : ℤ) * ((m q : ℤ) - 1)) = 30 := by
    have h : (∑ q, ((m q * m q - m q : ℕ) : ℤ)) = 30 := by exact_mod_cast hsecondNat
    simpa only [hcast] using h
  have hsquares : (∑ q, ((m q : ℤ) - 2) ^ 2) = 0 := by
    have he (q : P) : ((m q : ℤ) - 2) ^ 2 =
        (m q : ℤ) * ((m q : ℤ) - 1) - 3 * (m q : ℤ) + 4 := by ring
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hfirst, hsecond, Finset.sum_const, Finset.card_univ, D.card_points]
    norm_num
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ ↦ sq_nonneg ((m q : ℤ) - 2))).mp
    hsquares p (Finset.mem_univ p)
  have hm : (m p : ℤ) = 2 := by nlinarith [sq_nonneg ((m p : ℤ) - 2)]
  exact_mod_cast hm

end Design
