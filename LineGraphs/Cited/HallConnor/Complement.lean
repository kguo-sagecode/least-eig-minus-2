/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Nonexistence

/-!
# Complementary labelled designs

The general constructor `hc:def:compl` and the excluded complementary parameters
`hc:cor:complement` of the Hall–Connor blueprint ([CGSS], Remark 5.12 and Example 5.13).
-/

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable {v k b r lam : ℕ} (D : Design P B v k b r lam)

/-- Complementary block sizes, `hcComplGeneralSize` ([CGSS], Section 5). -/
theorem card_compl_block (X : B) : (D.block X)ᶜ.card = v - k := by
  rw [Finset.card_compl, D.card_points, D.card_block]

/-- Complementary replication counts, `hcComplGeneralPoint` ([CGSS], Section 5). -/
theorem card_blocksThrough_compl (p : P) :
    (Finset.univ.filter (fun X ↦ p ∈ (D.block X)ᶜ)).card = b - r := by
  have he : Finset.univ.filter (fun X ↦ p ∈ (D.block X)ᶜ) =
      (Finset.univ.filter (fun X ↦ p ∈ D.block X))ᶜ := by ext X; simp
  rw [he, Finset.card_compl, D.card_blocks, D.card_blocksThrough]

/-- General inclusion–exclusion for complementary pairs, `hcComplGeneralPair`
([CGSS], Section 5). All differences are natural differences. -/
theorem card_blocksThroughPair_compl (p q : P) (hpq : p ≠ q) :
    (Finset.univ.filter (fun X ↦ p ∈ (D.block X)ᶜ ∧ q ∈ (D.block X)ᶜ)).card =
      b + lam - 2 * r := by
  let A : Finset B := Finset.univ.filter (fun X ↦ p ∈ D.block X)
  let A' : Finset B := Finset.univ.filter (fun X ↦ q ∈ D.block X)
  have hA : A.card = r := D.card_blocksThrough p
  have hA' : A'.card = r := D.card_blocksThrough q
  have hinter : A ∩ A' =
      Finset.univ.filter (fun X ↦ p ∈ D.block X ∧ q ∈ D.block X) := by
    ext X
    simp [A, A']
  have he : Finset.univ.filter (fun X ↦ p ∈ (D.block X)ᶜ ∧ q ∈ (D.block X)ᶜ) =
      (A ∪ A')ᶜ := by
    ext X
    simp [A, A']
  have hu := Finset.card_union_add_card_inter A A'
  rw [hinter, D.card_blocksThroughPair p q hpq, hA, hA'] at hu
  have hc := Finset.card_compl_add_card (A ∪ A')
  rw [D.card_blocks] at hc
  rw [he]
  omega

/-- The general labelled complement `hc:def:compl` ([CGSS], Section 5).
The bound `2 ≤ v - k` supplies the required strict lower bound on block size. -/
def compl (hk : 2 ≤ v - k) : Design P B v (v - k) b (b - r) (b + lam - 2 * r) where
  card_points := D.card_points
  card_blocks := D.card_blocks
  block := fun X ↦ (D.block X)ᶜ
  card_block := D.card_compl_block
  card_blocksThrough := D.card_blocksThrough_compl
  card_blocksThroughPair := D.card_blocksThroughPair_compl
  one_lt_v := D.one_lt_v
  one_lt_k := by omega
  b_pos := D.b_pos

/-- The complementary parameters also contradict Hall–Connor, `hc:cor:complement`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem false_of_parameters_15_10_9 (D : Design P B 15 10 21 14 9) : False :=
  (D.compl (by decide)).false_of_parameters_15_5_2

/-- The bundled complementary nonexistence statement `hc:cor:complement`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem not_nonempty_15_10_9 : ¬ Nonempty (Design (Fin 15) (Fin 21) 15 10 21 14 9) :=
  fun ⟨D⟩ ↦ D.false_of_parameters_15_10_9

end Design
