/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.LocalRestrictions

/-!
# The local partition at an edge

The partition and clique counts in `hc:lem:split` of the Hall–Connor blueprint,
used in Remark 5.12 and Example 5.13 of [CGSS].
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

/-- The four parts at a pair of labels in `hc:lem:split` ([CGSS], Remark 5.12).
The Boolean arguments prescribe adjacency to the first and second label. -/
def neighborFiber (D : Design P B 15 5 21 7 2) (X Y : B) (a b : Bool) : Finset B :=
  ((Finset.univ.erase X).erase Y).filter fun T ↦
    decide (D.Z.Adj X T) = a ∧ decide (D.Z.Adj Y T) = b

variable (D : Design P B 15 5 21 7 2)

/-- The intersection-size description of the four parts, `hcLocalFibreM`–`hcLocalFibreR`
([CGSS], Remark 5.12). -/
theorem neighborFiber_eq (X Y : B) (a b : Bool) :
    D.neighborFiber X Y a b =
      ((Finset.univ.erase X).erase Y).filter fun T ↦
        (D.block X ∩ D.block T).card = (if a then 1 else 2) ∧
        (D.block Y ∩ D.block T).card = (if b then 1 else 2) := by
  ext T
  simp only [neighborFiber, Finset.mem_filter]
  by_cases hTX : T = X
  · subst T
    simp
  by_cases hTY : T = Y
  · subst T
    simp
  have hX := D.inter_card_eq_one_or_two (Ne.symm hTX)
  have hY := D.inter_card_eq_one_or_two (Ne.symm hTY)
  rcases hX with hX | hX <;> rcases hY with hY | hY <;>
    cases a <;> cases b <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] <;>
    simp [Z, hTX, hTY, hX, hY, Ne.symm hTX, Ne.symm hTY]

/-- The four part sizes `hcLocalSizes` ([CGSS], Remark 5.12): `(5,4,4,6)`. -/
theorem card_neighborFiber_of_adj {X Y : B} (hXY : D.Z.Adj X Y) :
    (D.neighborFiber X Y true true).card = 5 ∧
      (D.neighborFiber X Y true false).card = 4 ∧
      (D.neighborFiber X Y false true).card = 4 ∧
      (D.neighborFiber X Y false false).card = 6 := by
  have h := D.intersection_pair_counts hXY.ne
  simpa [D.neighborFiber_eq, intersectionPairCount, hXY.2] using h

/-- The two neighbourhood decompositions `hcLocalNeighboursOne` and
`hcLocalNeighboursTwo` ([CGSS], Remark 5.12). -/
theorem neighborFinset_eq_fibers {X Y : B} (hXY : D.Z.Adj X Y) :
    D.Z.neighborFinset X =
      insert Y (D.neighborFiber X Y true true ∪ D.neighborFiber X Y true false) := by
  ext T
  rw [SimpleGraph.mem_neighborFinset]
  by_cases hTX : T = X
  · subst T
    simp [neighborFiber, hXY.ne]
  by_cases hTY : T = Y
  · subst T
    simp [hXY]
  simp [neighborFiber, hTX, hTY]
  tauto

/-- The four parts are disjoint, `hcLocalDisjoint` ([CGSS], Remark 5.12). -/
theorem disjoint_neighborFiber (X Y : B) {a b c d : Bool} (h : (a, b) ≠ (c, d)) :
    Disjoint (D.neighborFiber X Y a b) (D.neighborFiber X Y c d) := by
  apply Finset.disjoint_left.mpr
  intro T hT hT'
  obtain ⟨_, ha, hb⟩ := Finset.mem_filter.mp hT
  obtain ⟨_, hc, hd⟩ := Finset.mem_filter.mp hT'
  exact h (Prod.ext (ha.symm.trans hc) (hb.symm.trans hd))

/-- A usable form of the claw restriction in `hcLocalUPair`, `hcLocalVPair`, and
`hcLocalMClaw` ([CGSS], Remark 5.12). Three distinct neighbours contain an edge. -/
theorem adj_or_adj_or_adj_of_three_neighbors {X A B₁ C₁ : B}
    (hXA : D.Z.Adj X A) (hXB : D.Z.Adj X B₁) (hXC : D.Z.Adj X C₁)
    (hAB : A ≠ B₁) (hAC : A ≠ C₁) (hBC : B₁ ≠ C₁) :
    D.Z.Adj A B₁ ∨ D.Z.Adj A C₁ ∨ D.Z.Adj B₁ C₁ := by
  by_contra h
  obtain ⟨hAB', hAC', hBC'⟩ :
      ¬ D.Z.Adj A B₁ ∧ ¬ D.Z.Adj A C₁ ∧ ¬ D.Z.Adj B₁ C₁ := by tauto
  have hi : Function.Injective (![X, A, B₁, C₁] : Fin 4 → B) := by
    have hXA' := hXA.ne
    have hXB' := hXB.ne
    have hXC' := hXC.ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact D.Z_clawFree ⟨![X, A, B₁, C₁], hi⟩ hXA hXB hXC hAB' hAC' hBC'

/-- The exclusive neighbours form a clique, `hcLocalU` and, on exchanging the labels,
`hcLocalV` ([CGSS], Remark 5.12). -/
theorem isClique_neighborFiber_true_false {X Y : B} (hXY : D.Z.Adj X Y) :
    D.Z.IsClique (D.neighborFiber X Y true false : Set B) := by
  intro A hA B₁ hB hAB
  have ha : A ≠ Y ∧ A ≠ X ∧ D.Z.Adj X A ∧ ¬ D.Z.Adj Y A := by
    simpa [neighborFiber, and_assoc] using hA
  have hb : B₁ ≠ Y ∧ B₁ ≠ X ∧ D.Z.Adj X B₁ ∧ ¬ D.Z.Adj Y B₁ := by
    simpa [neighborFiber, and_assoc] using hB
  have h := D.adj_or_adj_or_adj_of_three_neighbors hXY ha.2.2.1 hb.2.2.1
    ha.1.symm hb.1.symm hAB
  exact h.resolve_left ha.2.2.2 |>.resolve_left hb.2.2.2

/-- Each exclusive neighbour has two neighbours in the common part, `hcLocalTwo`
([CGSS], Remark 5.12). -/
theorem card_common_part_neighbors {X Y Z₁ : B} (hXY : D.Z.Adj X Y)
    (hZ : Z₁ ∈ D.neighborFiber X Y true false) :
    ((D.neighborFiber X Y true true).filter (D.Z.Adj Z₁)).card = 2 := by
  let M := D.neighborFiber X Y true true
  let U := D.neighborFiber X Y true false
  have hZ' : Z₁ ≠ Y ∧ Z₁ ≠ X ∧ D.Z.Adj X Z₁ ∧ ¬ D.Z.Adj Y Z₁ := by
    simpa [neighborFiber, and_assoc] using hZ
  have hnot : ¬ D.Z.Adj Z₁ Y := fun h ↦ hZ'.2.2.2 h.symm
  have hUfilter : U.filter (D.Z.Adj Z₁) = U.erase Z₁ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hTU, hZT⟩
      exact ⟨hZT.ne.symm, hTU⟩
    · rintro ⟨hTZ, hTU⟩
      exact ⟨hTU, D.isClique_neighborFiber_true_false hXY hZ hTU hTZ.symm⟩
  have hdecomp : (D.Z.neighborFinset X).filter (D.Z.Adj Z₁) =
      U.erase Z₁ ∪ M.filter (D.Z.Adj Z₁) := by
    rw [D.neighborFinset_eq_fibers hXY, Finset.filter_insert, ite_eq_right hnot,
      Finset.filter_union, hUfilter, Finset.union_comm]
  have hdis : Disjoint (U.erase Z₁) (M.filter (D.Z.Adj Z₁)) :=
    (D.disjoint_neighborFiber X Y (by decide : (true, false) ≠ (true, true))).mono
      (Finset.erase_subset _ _) (Finset.filter_subset _ _)
  have hset : ((D.Z.neighborFinset X).filter (D.Z.Adj Z₁) : Set B) =
      D.Z.commonNeighbors X Z₁ := by
    ext T
    simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_commonNeighbors]
  have hc : ((D.Z.neighborFinset X).filter (D.Z.Adj Z₁)).card = 5 := by
    have h := D.card_commonNeighbors hZ'.2.2.1.ne
    rw [ite_eq_left hZ'.2.2.1, ← hset, Set.ncard_coe_finset] at h
    exact h
  rw [hdecomp, Finset.card_union_of_disjoint hdis, Finset.card_erase_of_mem hZ,
    (D.card_neighborFiber_of_adj hXY).2.1] at hc
  change (M.filter (D.Z.Adj Z₁)).card = 2
  omega

/-- Exactly eight edges join the common and exclusive parts, `hcLocalEdgeSwap` and
`hcLocalEight` ([CGSS], Remark 5.12). -/
theorem sum_card_common_part_neighbors {X Y : B} (hXY : D.Z.Adj X Y) :
    (∑ Z₁ ∈ D.neighborFiber X Y true true,
      ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card) = 8 := by
  calc
    _ = ∑ T ∈ D.neighborFiber X Y true false,
        ((D.neighborFiber X Y true true).filter (fun Z₁ ↦ D.Z.Adj Z₁ T)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow D.Z.Adj
    _ = ∑ _ ∈ D.neighborFiber X Y true false, 2 := by
      apply Finset.sum_congr rfl
      intro T hT
      have he : (D.neighborFiber X Y true true).filter (fun Z₁ ↦ D.Z.Adj Z₁ T) =
          (D.neighborFiber X Y true true).filter (D.Z.Adj T) := by
        ext Z₁
        simp only [Finset.mem_filter, D.Z.adj_comm]
      rw [he, D.card_common_part_neighbors hXY hT]
    _ = 8 := by simp [(D.card_neighborFiber_of_adj hXY).2.1]

/-- The third block in `hcLocalPick` ([CGSS], Remark 5.12): some common neighbour has
at least two neighbours in the four-element exclusive part. -/
theorem exists_common_neighbor_with_two_neighbors {X Y : B} (hXY : D.Z.Adj X Y) :
    ∃ Z₁ ∈ D.neighborFiber X Y true true,
      2 ≤ ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card := by
  by_contra h
  push Not at h
  have hle := Finset.sum_le_sum (s := D.neighborFiber X Y true true)
    (g := fun _ ↦ (1 : ℕ)) (fun T hT ↦ Nat.le_of_lt_succ (h T hT))
  rw [D.sum_card_common_part_neighbors hXY] at hle
  norm_num [(D.card_neighborFiber_of_adj hXY).1] at hle

end Design
