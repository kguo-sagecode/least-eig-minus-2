/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.Neighborhood

/-!
# Counts at the selected third block

The defect and common-neighbour counts `hcLocalDefect` and `hcLocalCounts`, and the
five-block application `hcLocalNoCross`, in `hc:lem:split` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13).
-/

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable (D : Design P B 15 5 21 7 2)

/-- Exchanging the endpoints exchanges the part labels (`hcLocalFibreU`, `hcLocalFibreV`;
[CGSS], Remark 5.12). -/
theorem neighborFiber_swap (X Y : B) (a b : Bool) :
    D.neighborFiber Y X b a = D.neighborFiber X Y a b := by
  ext T
  simp only [neighborFiber, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
  tauto

/-- Common neighbours counted as a filtered neighbourhood (`hcLocalFirst` and
`hcLocalSecond`; [CGSS], Remark 5.12). -/
theorem card_filter_neighborFinset {X Z₁ : B} (hXZ : D.Z.Adj X Z₁) :
    ((D.Z.neighborFinset X).filter (D.Z.Adj Z₁)).card = 5 := by
  have hset : ((D.Z.neighborFinset X).filter (D.Z.Adj Z₁) : Set B) =
      D.Z.commonNeighbors X Z₁ := by
    ext T
    simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_commonNeighbors]
  have h := D.card_commonNeighbors hXZ.ne
  rw [ite_eq_left hXZ, ← hset, Set.ncard_coe_finset] at h
  exact h

/-- The first common-neighbour equation `hcLocalFirst` ([CGSS], Remark 5.12).
The second is obtained by exchanging `X` and `Y`. -/
theorem common_part_neighbor_sum {X Y Z₁ : B} (hXY : D.Z.Adj X Y)
    (hXZ : D.Z.Adj X Z₁) (hYZ : D.Z.Adj Y Z₁) :
    ((D.neighborFiber X Y true true).filter (D.Z.Adj Z₁)).card +
      ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card = 4 := by
  have hn := D.card_filter_neighborFinset hXZ
  rw [D.neighborFinset_eq_fibers hXY, Finset.filter_insert, ite_eq_left hYZ.symm,
    Finset.filter_union] at hn
  have hnY : Y ∉
      (D.neighborFiber X Y true true).filter (D.Z.Adj Z₁) ∪
        (D.neighborFiber X Y true false).filter (D.Z.Adj Z₁) := by
    simp [neighborFiber]
  have hdis : Disjoint
      ((D.neighborFiber X Y true true).filter (D.Z.Adj Z₁))
      ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)) :=
    (D.disjoint_neighborFiber X Y (by decide : (true, true) ≠ (true, false))).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [Finset.card_insert_of_notMem hnY, Finset.card_union_of_disjoint hdis] at hn
  omega

/-- The nonneighbours of the third label in the exclusive part, `hcLocalDefect`
([CGSS], Remark 5.12). -/
def localDefect (X Y Z₁ : B) : ℕ :=
  ((D.neighborFiber X Y true false).filter fun T ↦ ¬ D.Z.Adj Z₁ T).card

/-- Neighbours and nonneighbours partition the exclusive part, `hcLocalDefect`
([CGSS], Remark 5.12). -/
theorem localDefect_add_neighbors {X Y : B} (hXY : D.Z.Adj X Y) (Z₁ : B) :
    D.localDefect X Y Z₁ +
      ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card = 4 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := D.neighborFiber X Y true false) (p := D.Z.Adj Z₁)
  rw [(D.card_neighborFiber_of_adj hXY).2.1] at h
  exact (Nat.add_comm _ _).trans h

/-- The defect is at most two and the other two local counts are `j` and `4 - j`,
`hcLocalDefect`, `hcLocalFirst`, and `hcLocalSecond` ([CGSS], Remark 5.12). -/
theorem local_counts {X Y Z₁ : B} (hXY : D.Z.Adj X Y)
    (hZ : Z₁ ∈ D.neighborFiber X Y true true)
    (htwo : 2 ≤ ((D.neighborFiber X Y true false).filter (D.Z.Adj Z₁)).card) :
    D.localDefect X Y Z₁ ≤ 2 ∧
      ((D.neighborFiber X Y true true).filter (D.Z.Adj Z₁)).card = D.localDefect X Y Z₁ ∧
      ((D.neighborFiber X Y false true).filter (D.Z.Adj Z₁)).card =
        4 - D.localDefect X Y Z₁ := by
  have hZ' : Z₁ ≠ Y ∧ Z₁ ≠ X ∧ D.Z.Adj X Z₁ ∧ D.Z.Adj Y Z₁ := by
    simpa [neighborFiber, and_assoc] using hZ
  have hfirst := D.common_part_neighbor_sum hXY hZ'.2.2.1 hZ'.2.2.2
  have hsecond := D.common_part_neighbor_sum hXY.symm hZ'.2.2.2 hZ'.2.2.1
  rw [D.neighborFiber_swap X Y true true, D.neighborFiber_swap X Y false true] at hsecond
  have hpart := D.localDefect_add_neighbors hXY Z₁
  omega

/-- There are no edges between the two selected subparts, `hcLocalNoCross`
(Hall–Connor Lemma 4.5 at `k = 5`; [CGSS], Remark 5.12). -/
theorem not_adj_local_parts {X Y Z₁ A B₁ : B} (hXY : D.Z.Adj X Y)
    (hZ : Z₁ ∈ D.neighborFiber X Y true true)
    (hA : A ∈ D.neighborFiber X Y true false) (hZA : ¬ D.Z.Adj Z₁ A)
    (hB : B₁ ∈ D.neighborFiber X Y false true) (hZB : D.Z.Adj Z₁ B₁) :
    ¬ D.Z.Adj A B₁ := by
  have hz : Z₁ ≠ Y ∧ Z₁ ≠ X ∧ D.Z.Adj X Z₁ ∧ D.Z.Adj Y Z₁ := by
    simpa [neighborFiber, and_assoc] using hZ
  have ha : A ≠ Y ∧ A ≠ X ∧ D.Z.Adj X A ∧ ¬ D.Z.Adj Y A := by
    simpa [neighborFiber, and_assoc] using hA
  have hb : B₁ ≠ Y ∧ B₁ ≠ X ∧ ¬ D.Z.Adj X B₁ ∧ D.Z.Adj Y B₁ := by
    simpa [neighborFiber, and_assoc] using hB
  have hAZ : A ≠ Z₁ := by rintro rfl; exact ha.2.2.2 hz.2.2.2
  have hAB : A ≠ B₁ := by rintro rfl; exact hb.2.2.1 ha.2.2.1
  have hi : Function.Injective (![X, Y, Z₁, A, B₁] : Fin 5 → B) := by
    have hXY' := hXY.ne
    have hZB' := hZB.ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact D.not_adj_of_five_block_pattern ⟨![X, Y, Z₁, A, B₁], hi⟩
    hXY hz.2.2.1 hz.2.2.2 ha.2.2.1.symm
    (fun h ↦ ha.2.2.2 h.symm) (fun h ↦ hZA h.symm)
    hb.2.2.2.symm hZB.symm (fun h ↦ hb.2.2.1 h.symm)

end Design
