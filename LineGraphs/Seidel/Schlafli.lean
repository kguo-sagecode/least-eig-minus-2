/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Isomorphisms
import LineGraphs.Graphs.TrianglePropertyIso
import LineGraphs.LineSystem.Section2Models
import LineGraphs.Computations.C9ModelIsos

/-!
# The triangle property and the Schläfli graph

Lemmas `lem:414-GQ1`, `lem:414-gq24iso`, and `lem:414-SE3` of the blueprint
for Remark 4.14 of [CGSS]. The isomorphism-from-order theorem of Section 2
identifies the double-six graph; the C9 certificate identifies its complement.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]

-- Lemma (the triangle property from the parameters, GQ1), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-GQ1`, Remark 4.14 of [CGSS]: strong regularity with adjacent
common-neighbour count one and `n + 3 = 3 * k` implies the triangle property. -/
theorem IsSRGWith.hasTriangleProperty {n k c : ℕ} (h : X.IsSRGWith n k 1 c)
    (hn : n + 3 = 3 * k) : X.HasTriangleProperty := by
  classical
  -- Step `s414gqone`: the adjacent common-neighbour count gives uniqueness.
  have hcommon {u v p q : V} (huv : X.Adj u v)
      (hup : X.Adj u p) (hvp : X.Adj v p) (huq : X.Adj u q) (hvq : X.Adj v q) :
      p = q := by
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp (h.of_adj u v huv)
    exact congrArg Subtype.val ((hw ⟨p, hup, hvp⟩).trans (hw ⟨q, huq, hvq⟩).symm)
  intro x y hxy
  obtain ⟨⟨z, hxz, hyz⟩⟩ := Fintype.card_pos_iff.mp
    (show 0 < Fintype.card (X.commonNeighbors x y) by rw [h.of_adj x y hxy]; omega)
  refine ⟨z, hxz, hyz, fun w hxw hyw ↦ hcommon hxy hxw hyw hxz hyz, ?_⟩
  have hinter : X.neighborFinset x ∩ X.neighborFinset y = {z} := by
    ext w
    simp only [Finset.mem_inter, mem_neighborFinset, Finset.mem_singleton]
    exact ⟨fun hw ↦ hcommon hxy hw.1 hw.2 hxz hyz, fun hw ↦ hw ▸ ⟨hxz, hyz⟩⟩
  have hinter' : (X.neighborFinset x ∪ X.neighborFinset y) ∩ X.neighborFinset z =
      {x, y} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_union, mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw | hw, hzw⟩
      · exact Or.inr (hcommon hxz hw hzw hxy hyz.symm)
      · exact Or.inl (hcommon hyz hw hzw hxy.symm hxz.symm)
    · rintro (rfl | rfl)
      · exact ⟨Or.inr hxy.symm, hxz.symm⟩
      · exact ⟨Or.inl hxy, hyz.symm⟩
  -- The three neighbourhoods have union of size `3k - 3 = n`.
  have hcard := Finset.card_union_add_card_inter (X.neighborFinset x) (X.neighborFinset y)
  rw [hinter, Finset.card_singleton, card_neighborFinset_eq_degree,
    card_neighborFinset_eq_degree, h.regular x, h.regular y] at hcard
  have hcard' := Finset.card_union_add_card_inter
    (X.neighborFinset x ∪ X.neighborFinset y) (X.neighborFinset z)
  rw [hinter', Finset.card_pair hxy.ne, card_neighborFinset_eq_degree,
    h.regular z] at hcard'
  have hcover : X.neighborFinset x ∪ X.neighborFinset y ∪ X.neighborFinset z =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h.card]
    omega
  intro w hwx hwy hwz
  -- Step `s414gqmost`: an outside vertex cannot meet two vertices of the triangle.
  have hnotxy : ¬ (X.Adj w x ∧ X.Adj w y) := fun hw ↦
    hwz (hcommon hxy hw.1.symm hw.2.symm hxz hyz)
  have hnotxz : ¬ (X.Adj w x ∧ X.Adj w z) := fun hw ↦
    hwy (hcommon hxz hw.1.symm hw.2.symm hxy hyz.symm)
  have hnotyz : ¬ (X.Adj w y ∧ X.Adj w z) := fun hw ↦
    hwx (hcommon hyz hw.1.symm hw.2.symm hxy.symm hxz.symm)
  have hseen : X.Adj w x ∨ X.Adj w y ∨ X.Adj w z := by
    have hw : w ∈ X.neighborFinset x ∪ X.neighborFinset y ∪ X.neighborFinset z := by
      rw [hcover]
      exact Finset.mem_univ _
    simpa only [Finset.mem_union, mem_neighborFinset, X.adj_comm w, or_assoc] using hw
  tauto

-- Lemma (the double-six graph from its parameters), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-gq24iso`, Remark 4.14 of [CGSS]: a strongly regular graph
with parameters `(27,10,1,5)` is isomorphic to the double-six graph. -/
theorem IsSRGWith.nonempty_iso_gq24 (h : X.IsSRGWith 27 10 1 5) :
    Nonempty (X ≃g gq24) := by
  classical
  have hQ := gq24_isSRGWith
  obtain ⟨he, hn⟩ := h.exists_edge_and_forall_exists_not_adj (by norm_num) (by norm_num)
  obtain ⟨heQ, hnQ⟩ := hQ.exists_edge_and_forall_exists_not_adj (by norm_num) (by norm_num)
  exact (h.hasTriangleProperty (by norm_num)).nonempty_iso_of_card_eq
    (hQ.hasTriangleProperty (by norm_num)) he heQ hn hnQ (h.card.trans hQ.card.symm)

-- Lemma (SE3: the Schläfli graph), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-SE3`, Remark 4.14 of [CGSS]: a strongly regular graph with
parameters `(27,16,10,8)` is isomorphic to the vector Schläfli graph of Example 4.6. -/
theorem IsSRGWith.nonempty_iso_schlafli (h : X.IsSRGWith 27 16 10 8) :
    Nonempty (X ≃g schlafli) := by
  classical
  have hc : Xᶜ.IsSRGWith 27 10 1 5 := by simpa using h.compl
  obtain ⟨e⟩ := hc.nonempty_iso_gq24
  have he : X ≃g gq24ᶜ := by simpa only [compl_compl] using e.compl
  exact ⟨he.trans schlafli.gq24ComplIso.symm⟩

end SimpleGraph
