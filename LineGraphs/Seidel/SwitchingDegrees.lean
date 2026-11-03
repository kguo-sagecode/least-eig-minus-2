/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Switching
import LineGraphs.Seidel.LineGraphCounts
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Degrees in regular switchings

Lemmas `lem:414-degree` and `lem:414-constsum` of the blueprint for
Remark 4.14 of [CGSS]. All subtraction in the count formulas is in the integers.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {Y : SimpleGraph V}
  [DecidableRel Y.Adj]

/-- The vertices of the line graph corresponding to edges inside `M`, the set
`K` in Lemma `lem:414-degree`, Remark 4.14 of [CGSS]. -/
def edgeFinsetWithin (Y : SimpleGraph V) [DecidableRel Y.Adj] (M : Finset V) :
    Finset Y.edgeSet := Finset.univ.filter fun e ↦ e.val.toFinset ⊆ M

/-- Membership in the edge set `K` of Lemma `lem:414-degree`, Remark 4.14 of [CGSS]. -/
@[simp] theorem mem_edgeFinsetWithin {M : Finset V} {e : Y.edgeSet} :
    e ∈ Y.edgeFinsetWithin M ↔ e.val.toFinset ⊆ M := by simp [edgeFinsetWithin]

/-- The size of the complete edge set in step `s414degall`, Lemma
`lem:414-degree`, Remark 4.14 of [CGSS]. -/
theorem card_edgeFinsetWithin_of_isClique {M : Finset V} (hM : Y.IsClique (M : Set V)) :
    (Y.edgeFinsetWithin M).card = M.card.choose 2 := by
  have himage : (Y.edgeFinsetWithin M).image Subtype.val =
      Y.edgeFinset.filter (fun e ↦ e.toFinset ⊆ M) := by
    ext e
    simp only [Finset.mem_image, mem_edgeFinsetWithin, Finset.mem_filter, mem_edgeFinset]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f.property, hf⟩
    · rintro ⟨he, hsub⟩
      exact ⟨⟨e, he⟩, hsub, rfl⟩
  have hc := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ Subtype.val_injective,
    card_filter_edgeFinset_toFinset_subset] at hc
  let f : Y.induce (M : Set V) ≃g completeGraph (M : Set V) :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro u v
        change u ≠ v ↔ Y.Adj u v
        exact ⟨fun huv ↦ hM u.property v.property (fun he ↦ huv (Subtype.ext he)),
          fun huv he ↦ huv.ne (congrArg Subtype.val he)⟩ }
  rw [f.card_edgeFinset_eq, card_edgeFinset_top_eq_card_choose_two] at hc
  have hcard : Fintype.card (M : Set V) = M.card := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  rwa [hcard] at hc

/-- An endpoint has `m - 1` incident edges in the complete edge set, as used
in step `s414degall` of Lemma `lem:414-degree`, Remark 4.14 of [CGSS]. -/
theorem card_filter_edgeFinsetWithin_mem_of_isClique {M : Finset V}
    (hM : Y.IsClique (M : Set V)) {i : V} (hi : i ∈ M) :
    ((Y.edgeFinsetWithin M).filter fun e ↦ i ∈ e.val).card = M.card - 1 := by
  have himage : ((Y.edgeFinsetWithin M).filter fun e ↦ i ∈ e.val).image Subtype.val =
      (M.erase i).image (fun v ↦ s(i, v)) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Finset.mem_image, Finset.mem_filter, mem_edgeFinsetWithin]
      constructor
      · rintro ⟨⟨e, he⟩, ⟨hM', hi'⟩, rfl⟩
        have hu : u ∈ M := hM' (by simp)
        have hv : v ∈ M := hM' (by simp)
        rcases Sym2.mem_iff.mp hi' with rfl | rfl
        · exact ⟨v, Finset.mem_erase.mpr ⟨he.ne.symm, hv⟩, rfl⟩
        · exact ⟨u, Finset.mem_erase.mpr ⟨he.ne, hu⟩, Sym2.eq_swap⟩
      · rintro ⟨w, hw, he⟩
        obtain ⟨hwi, hwM⟩ := Finset.mem_erase.mp hw
        have hiw : Y.Adj i w := hM hi hwM hwi.symm
        refine ⟨⟨s(i, w), hiw⟩, ⟨?_, by simp⟩, he⟩
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hi hwM
  have hc := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ (fun _ _ ↦ Sym2.congr_right.mp),
    Finset.card_erase_of_mem hi] at hc
  exact hc

omit [Fintype V] in
/-- The cut-count identity behind steps `s414degin` and `s414degout`,
Lemma `lem:414-degree`, Remark 4.14 of [CGSS], for an arbitrary vertex subset. -/
theorem card_adj_switch (X : SimpleGraph V) [DecidableRel X.Adj]
    (K : Finset V) (H : Set V) [DecidablePred (· ∈ H)] (e : V) :
    ((K.filter fun f ↦ (X.switch H).Adj e f).card : ℤ) =
      if e ∈ H then
        (K.card : ℤ) - (K.filter fun f ↦ f ∈ H).card - (K.filter (X.Adj e)).card +
          2 * (K.filter fun f ↦ f ∈ H ∧ X.Adj e f).card
      else
        ((K.filter (X.Adj e)).card : ℤ) + (K.filter fun f ↦ f ∈ H).card -
          2 * (K.filter fun f ↦ f ∈ H ∧ X.Adj e f).card := by
  classical
  by_cases he : e ∈ H
  · simp only [he, ite_true]
    have hi (f : V) : (if (X.switch H).Adj e f then (1 : ℤ) else 0) =
        1 - (if f ∈ H then 1 else 0) - (if X.Adj e f then 1 else 0) +
          2 * (if f ∈ H ∧ X.Adj e f then 1 else 0) := by
      by_cases hef : e = f
      · subst f
        simp [he]
      · by_cases hf : f ∈ H <;> by_cases ha : X.Adj e f <;>
          simp [switch_adj, he, hef, hf, ha]
    have hs := Finset.sum_congr (s₁ := K) rfl (fun f _ ↦ hi f)
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.sum_boole, nsmul_one] using hs
  · simp only [he, ite_false]
    have hi (f : V) : (if (X.switch H).Adj e f then (1 : ℤ) else 0) =
        (if X.Adj e f then 1 else 0) + (if f ∈ H then 1 else 0) -
          2 * (if f ∈ H ∧ X.Adj e f then 1 else 0) := by
      by_cases hef : e = f
      · subst f
        simp [he]
      · by_cases hf : f ∈ H <;> by_cases ha : X.Adj e f <;>
          simp [switch_adj, he, hef, hf, ha]
    have hs := Finset.sum_congr (s₁ := K) rfl (fun f _ ↦ hi f)
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole] using hs

noncomputable local instance switchingDegreesDecidableAdj : DecidableRel Y.lineGraph.Adj :=
  Classical.decRel _

omit [Fintype V] [DecidableRel Y.Adj] in
/-- Step `s414degmeet` of Lemma `lem:414-degree`, Remark 4.14 of [CGSS]:
count the selected edges through either endpoint, removing the original edge
twice when it belongs to the selection. -/
theorem card_filter_adj_lineGraph (K : Finset Y.edgeSet) (H : Set Y.edgeSet)
    [DecidablePred (· ∈ H)] {i j : V} (hij : Y.Adj i j)
    (he : (⟨s(i, j), hij⟩ : Y.edgeSet) ∈ K) :
    ((K.filter fun f ↦ f ∈ H ∧ Y.lineGraph.Adj ⟨s(i, j), hij⟩ f).card : ℤ) =
      ((K.filter fun f ↦ f ∈ H ∧ i ∈ f.val).card : ℤ) +
        (K.filter fun f ↦ f ∈ H ∧ j ∈ f.val).card -
          if (⟨s(i, j), hij⟩ : Y.edgeSet) ∈ H then 2 else 0 := by
  classical
  let e : Y.edgeSet := ⟨s(i, j), hij⟩
  have hi (f : Y.edgeSet) :
      (if f ∈ H ∧ Y.lineGraph.Adj e f then (1 : ℤ) else 0) =
        (if f ∈ H ∧ i ∈ f.val then 1 else 0) +
          (if f ∈ H ∧ j ∈ f.val then 1 else 0) -
            if f = e then (if e ∈ H then 2 else 0) else 0 := by
    by_cases hfe : f = e
    · subst f
      by_cases hH : e ∈ H <;> simp [e, hH]
    have hboth : ¬(i ∈ f.val ∧ j ∈ f.val) := by
      rintro ⟨hi, hj⟩
      exact hfe (Subtype.ext (Sym2.eq_of_ne_mem hij.ne hi hj (by simp [e]) (by simp [e])))
    have ha : Y.lineGraph.Adj e f ↔ i ∈ f.val ∨ j ∈ f.val := by
      rw [lineGraph_adj_iff_exists]
      constructor
      · rintro ⟨_, v, hv, hvf⟩
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact Or.inl hvf
        · exact Or.inr hvf
      · intro hf
        refine ⟨Ne.symm hfe, ?_⟩
        exact hf.elim (fun hi ↦ ⟨i, by simp [e], hi⟩)
          (fun hj ↦ ⟨j, by simp [e], hj⟩)
    by_cases hH : f ∈ H <;> by_cases hi : i ∈ f.val <;> by_cases hj : j ∈ f.val <;>
      simp_all only [and_self, and_false, and_true, or_self, or_false, or_true,
        ite_true, ite_false] <;> norm_num
  have hs := Finset.sum_congr (s₁ := K) rfl (fun f _ ↦ hi f)
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_boole,
    Finset.sum_ite_eq', he, ite_true, e] using hs

-- Lemma (degrees in a switched line graph), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-degree`, Remark 4.14 of [CGSS]: count the neighbours
inside the complete edge set on `M` after switching by `H`. The two filtered
incidence counts defining `s` are the degrees in `H ∩ K`. -/
theorem card_adj_lineGraph_switch_of_complete {M : Finset V}
    (hM : Y.IsClique (M : Set V)) (H : Set Y.edgeSet) [DecidablePred (· ∈ H)]
    {i j : V} (hi : i ∈ M) (hj : j ∈ M) (hij : Y.Adj i j) :
    let K := Y.edgeFinsetWithin M
    let e : Y.edgeSet := ⟨s(i, j), hij⟩
    let h := (K.filter fun f ↦ f ∈ H).card
    let s := (K.filter fun f ↦ f ∈ H ∧ i ∈ f.val).card +
      (K.filter fun f ↦ f ∈ H ∧ j ∈ f.val).card
    ((K.filter fun f ↦ (Y.lineGraph.switch H).Adj e f).card : ℤ) =
      if e ∈ H then 2 * (s : ℤ) - h - 3 + (M.card - 2).choose 2
      else 2 * ((M.card : ℤ) - 2) + h - 2 * s := by
  classical
  let K := Y.edgeFinsetWithin M
  let e : Y.edgeSet := ⟨s(i, j), hij⟩
  have he : e ∈ K := by
    simp only [K, e, mem_edgeFinsetWithin, Sym2.toFinset_mk_eq,
      Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hi, hj⟩
  have hm : 2 ≤ M.card := by
    have hh := Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij.ne⟩
    omega
  have hcK := card_edgeFinsetWithin_of_isClique hM
  have hci := card_filter_edgeFinsetWithin_mem_of_isClique hM hi
  have hcj := card_filter_edgeFinsetWithin_mem_of_isClique hM hj
  have hd := card_filter_adj_lineGraph K Set.univ hij he
  simp only [Set.mem_univ, true_and, ite_true] at hd
  have hd' : ((K.filter (Y.lineGraph.Adj e)).card : ℤ) = 2 * ((M.card : ℤ) - 2) := by
    rw [hci, hcj, Nat.cast_sub (by omega : 1 ≤ M.card)] at hd
    calc
      _ = (M.card : ℤ) - 1 + ((M.card : ℤ) - 1) - 2 := by exact hd
      _ = _ := by ring
  have hs := card_filter_adj_lineGraph K H hij he
  have hsw := card_adj_switch Y.lineGraph K H e
  have hchoose : (M.card.choose 2 : ℤ) - 2 * M.card = ((M.card - 2).choose 2 : ℤ) - 3 := by
    obtain ⟨t, ht⟩ : ∃ t, M.card = t + 2 := ⟨M.card - 2, by omega⟩
    rw [ht]
    simp only [Nat.add_sub_cancel, Nat.choose_succ_succ, Nat.choose_one_right,
      Nat.choose_zero_right, Nat.cast_add, Nat.cast_one]
    ring
  dsimp only
  change ((K.filter fun f ↦ (Y.lineGraph.switch H).Adj e f).card : ℤ) = _
  rw [hd', hcK] at hsw
  simp only [Nat.cast_add]
  dsimp only [K, e] at hs hsw ⊢
  by_cases hH : (⟨s(i, j), hij⟩ : Y.edgeSet) ∈ H
  · simp only [hH, ite_true] at hsw hs ⊢
    linarith
  · simp only [hH, ite_false] at hsw hs ⊢
    linarith

end SimpleGraph

namespace Finset

-- Lemma (constant pair sums), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-constsum`, Remark 4.14 of [CGSS]: constant sums over
distinct pairs in a set of at least three elements force every doubled value
to equal the common sum. -/
theorem two_mul_eq_of_forall_add_eq {α : Type*} (M : Finset α) (hM : 3 ≤ M.card)
    (d : α → ℤ) (σ : ℤ) (h : ∀ i ∈ M, ∀ j ∈ M, i ≠ j → d i + d j = σ) :
    ∀ i ∈ M, 2 * d i = σ := by
  classical
  intro i hi
  obtain ⟨j, hj, hji⟩ := M.exists_mem_ne (by omega) i
  have hcard : 1 < (M.erase i).card := by rw [card_erase_of_mem hi]; omega
  obtain ⟨l, hl, hlj⟩ := (M.erase i).exists_mem_ne hcard j
  obtain ⟨hli, hlM⟩ := mem_erase.mp hl
  have hij := h i hi j hj hji.symm
  have hil := h i hi l hlM hli.symm
  have hjl := h j hj l hlM hlj.symm
  omega

end Finset
