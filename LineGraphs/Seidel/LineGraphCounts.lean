/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.LineGraphRegular
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Common neighbours in a line graph

The local counts in Lemma LG1 (`lem:4-LG1`), used in Theorem 4.13 and
Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {V : Type*} {Y : SimpleGraph V}

/-- The endpoint form of line-graph adjacency, used in Lemma LG1 of
Theorem 4.13 of [CGSS]. -/
theorem lineGraph_adj_mk_iff {u v w x : V} (huv : Y.Adj u v) (hwx : Y.Adj w x) :
    Y.lineGraph.Adj ⟨s(u, v), huv⟩ ⟨s(w, x), hwx⟩ ↔
      s(u, v) ≠ s(w, x) ∧ (u = w ∨ u = x ∨ v = w ∨ v = x) := by
  rw [lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, a, ha, hb⟩
    refine ⟨fun h ↦ hne (Subtype.ext h), ?_⟩
    have ha' := Sym2.mem_iff.mp ha
    have hb' := Sym2.mem_iff.mp hb
    grind only
  · rintro ⟨hne, h⟩
    refine ⟨fun he ↦ hne (congrArg Subtype.val he), ?_⟩
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨u, by simp, by simp⟩
    · exact ⟨u, by simp, by simp⟩
    · exact ⟨v, by simp, by simp⟩
    · exact ⟨v, by simp, by simp⟩

variable [Fintype V] [DecidableRel Y.Adj]

noncomputable local instance lineGraphCountsDecidableAdj : DecidableRel Y.lineGraph.Adj :=
  Classical.decRel _

/-- Step `s4lgcommon` of Lemma LG1, Theorem 4.13 of [CGSS]: two incident
edges have the other edges at their common endpoint as common neighbours,
together with the edge between their other endpoints when it exists. -/
theorem card_commonNeighbors_lineGraph_of_adj {i j k : V}
    (hij : Y.Adj i j) (hik : Y.Adj i k) (hjk : j ≠ k) :
    Fintype.card (Y.lineGraph.commonNeighbors ⟨s(i, j), hij⟩ ⟨s(i, k), hik⟩) =
      Y.degree i - 2 + if Y.Adj j k then 1 else 0 := by
  classical
  let S := (Y.incidenceFinset i).erase s(i, j) |>.erase s(i, k)
  let T : Finset (Sym2 V) := if Y.Adj j k then {s(j, k)} else ∅
  have hset :
      (Y.lineGraph.commonNeighbors ⟨s(i, j), hij⟩ ⟨s(i, k), hik⟩).toFinset.image
        Subtype.val = S ∪ T := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Finset.mem_image, Set.mem_toFinset, mem_commonNeighbors]
      constructor
      · rintro ⟨⟨e, he⟩, ⟨h₁, h₂⟩, rfl⟩
        have h₁' := lineGraph_adj_mk_iff hij he |>.mp h₁
        have h₂' := lineGraph_adj_mk_iff hik he |>.mp h₂
        simp only [S, T, Finset.mem_union, Finset.mem_erase, mem_incidenceFinset,
          incidenceSet, Set.mem_ofPred_eq, Sym2.mem_iff]
        split_ifs <;> simp only [Finset.mem_singleton, Finset.notMem_empty, or_false]
        all_goals grind [Sym2.eq_iff, mem_edgeSet, Adj.ne, Adj.symm]
      · intro he
        simp only [S, T, Finset.mem_union, Finset.mem_erase, mem_incidenceFinset,
          incidenceSet, Set.mem_ofPred_eq, Sym2.mem_iff] at he
        have hT : s(u, v) ∈ T ↔ Y.Adj j k ∧ s(u, v) = s(j, k) := by
          by_cases h : Y.Adj j k <;> simp [T, h]
        dsimp only [T] at hT
        rw [hT] at he
        have huv : Y.Adj u v := by
          rcases he with h | h
          · exact h.2.2.1
          · rcases Sym2.eq_iff.mp h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact h.1
            · exact h.1.symm
        refine ⟨⟨s(u, v), huv⟩, ⟨?_, ?_⟩, rfl⟩ <;>
          rw [lineGraph_adj_mk_iff] <;>
          grind [Sym2.eq_iff, Adj.ne, Adj.symm]
  have heq : s(i, j) ≠ s(i, k) := by simp [hjk, hik.ne]
  have hcardS : S.card = Y.degree i - 2 := by
    simp [S, Finset.card_erase_of_mem, heq.symm, hij, hik, Nat.sub_sub]
  have hcardT : T.card = if Y.Adj j k then 1 else 0 := by
    by_cases h : Y.Adj j k <;> simp [T, h]
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro e he hf
    have hi : i ∈ e := ((Y.mem_incidenceFinset i e).mp (Finset.mem_erase.mp
      (Finset.mem_erase.mp he).2).2).2
    by_cases h : Y.Adj j k
    · have heq : e = s(j, k) := by simpa [T, h] using hf
      rw [heq, Sym2.mem_iff] at hi
      exact hi.elim hij.ne hik.ne
    · simp [T, h] at hf
  have hcard := congrArg Finset.card hset
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Set.toFinset_card,
    Finset.card_union_of_disjoint hdisj, hcardS, hcardT] at hcard
  exact hcard

/-- Steps `s4lgdisj` and `s4lgc2` of Lemma LG1, Theorem 4.13 of [CGSS]:
the common neighbours of disjoint edges are precisely the edges joining their
endpoints. -/
theorem card_commonNeighbors_lineGraph_of_disjoint {i j k l : V}
    (hij : Y.Adj i j) (hkl : Y.Adj k l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Fintype.card (Y.lineGraph.commonNeighbors ⟨s(i, j), hij⟩ ⟨s(k, l), hkl⟩) =
      (if Y.Adj i k then 1 else 0) + (if Y.Adj i l then 1 else 0) +
      (if Y.Adj j k then 1 else 0) + (if Y.Adj j l then 1 else 0) := by
  classical
  let S : Finset (Sym2 V) := {s(i, k), s(i, l), s(j, k), s(j, l)}
  have hset :
      (Y.lineGraph.commonNeighbors ⟨s(i, j), hij⟩ ⟨s(k, l), hkl⟩).toFinset.image
        Subtype.val = S ∩ Y.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Finset.mem_image, Set.mem_toFinset, mem_commonNeighbors,
        Finset.mem_inter, S, Finset.mem_insert, Finset.mem_singleton, mem_edgeFinset]
      constructor
      · rintro ⟨⟨e, he⟩, ⟨h₁, h₂⟩, rfl⟩
        have h₁' := (lineGraph_adj_mk_iff hij he).mp h₁
        have h₂' := (lineGraph_adj_mk_iff hkl he).mp h₂
        refine ⟨?_, he⟩
        grind [Sym2.eq_iff]
      · rintro ⟨he, huv⟩
        refine ⟨⟨s(u, v), huv⟩, ⟨?_, ?_⟩, rfl⟩
        · apply (lineGraph_adj_mk_iff hij huv).mpr
          grind [Sym2.eq_iff, Adj.ne]
        · apply (lineGraph_adj_mk_iff hkl huv).mpr
          grind [Sym2.eq_iff, Adj.ne]
  have hcard := congrArg Finset.card hset
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Set.toFinset_card] at hcard
  rw [hcard, ← Finset.filter_mem_eq_inter]
  have he₁ : s(i, k) ≠ s(i, l) := by simp [hkl.ne, hil]
  have he₂ : s(i, k) ≠ s(j, k) := by simp [hij.ne, hik]
  have he₃ : s(i, k) ≠ s(j, l) := by simp [hij.ne, hil]
  have he₄ : s(i, l) ≠ s(j, k) := by simp [hij.ne, hik]
  have he₅ : s(i, l) ≠ s(j, l) := by simp [hij.ne, hil]
  have he₆ : s(j, k) ≠ s(j, l) := by simp [hkl.ne, hjl]
  simp only [S, Finset.filter_insert, Finset.filter_singleton, mem_edgeFinset, mem_edgeSet]
  split_ifs <;> simp_all [Finset.card_insert_of_notMem]

end SimpleGraph
