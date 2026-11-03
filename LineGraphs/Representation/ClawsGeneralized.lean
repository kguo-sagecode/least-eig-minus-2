/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Claws
import LineGraphs.Computations.C10

/-!
# Claws in generalized line graphs

Lemma `lem:4-claws` preceding Remark 4.12 of [CGSS]. An independent set of neighbours
at one endpoint has at most two vertices. A singleton can be an edge or a petal;
if there are two vertices, they are opposite signed petals.
-/

namespace SimpleGraph

variable {V : Type*} (Y : SimpleGraph V) (a : V → ℕ)

-- Lemma (claws in a generalized line graph)
/-- The vertices attached at `i`, used in steps `s4clnbr` and `s4clside` of
`lem:4-claws`, Remark 4.12 of [CGSS]. -/
def generalizedLineGraphAt (i : V) : Set (GeneralizedLineGraphVertex Y a)
  | .inl e => i ∈ e.val
  | .inr p => p.1 = i

/-- Step `s4clside`, Remark 4.12 of [CGSS]: an edge is adjacent to every
other vertex attached at the same endpoint. -/
private theorem at_edge_eq_of_not_adj {i : V} (e : Y.edgeSet) (he : i ∈ e.val)
    {v : GeneralizedLineGraphVertex Y a} (hv : v ∈ generalizedLineGraphAt Y a i)
    (hn : ¬(generalizedLineGraph Y a).Adj (.inl e) v) : v = .inl e := by
  rcases v with f | ⟨j, k, b⟩
  · have hef : e = f := by
      by_contra h
      exact hn (lineGraph_adj_iff_exists.mpr ⟨h, i, he, hv⟩)
    exact congrArg Sum.inl hef.symm
  · change j = i at hv
    subst j
    exact (hn he).elim

/-- Step `s4clside`, Remark 4.12 of [CGSS]: nonadjacent petals at one
endpoint have the same index. -/
private theorem at_petal_eq_of_not_adj {i : V} (k : Fin (a i)) (b : Bool)
    {v : GeneralizedLineGraphVertex Y a} (hv : v ∈ generalizedLineGraphAt Y a i)
    (hn : ¬(generalizedLineGraph Y a).Adj (.inr ⟨i, k, b⟩) v) :
    ∃ c, v = .inr ⟨i, k, c⟩ := by
  rcases v with e | ⟨j, l, c⟩
  · exact (hn hv).elim
  · change j = i at hv
    subst j
    have hkl : k = l := by
      apply Fin.ext
      by_contra h
      exact hn ⟨rfl, h⟩
    subst l
    exact ⟨c, rfl⟩

-- Lemma (claws in a generalized line graph)
/-- Step `s4clside` of `lem:4-claws`, Remark 4.12 of [CGSS]: an independent
set at one endpoint has at most two members, and two members require a petal. -/
theorem generalizedLineGraph_independent_at_card_le (i : V)
    (T : Finset (GeneralizedLineGraphVertex Y a))
    (hat : ∀ v ∈ T, v ∈ generalizedLineGraphAt Y a i)
    (hind : ∀ v ∈ T, ∀ w ∈ T, ¬(generalizedLineGraph Y a).Adj v w) :
    T.card ≤ 2 ∧ (1 < T.card → 0 < a i) := by
  classical
  by_cases hT : T = ∅
  · simp [hT]
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  rcases v with e | ⟨j, k, b⟩
  · have hsub : T ⊆ {.inl e} := by
      intro w hw
      exact Finset.mem_singleton.mpr
        (at_edge_eq_of_not_adj Y a e (hat _ hv) (hat _ hw) (hind _ hv _ hw))
    have hc : T.card ≤ 1 := (Finset.card_le_card hsub).trans_eq (by simp)
    exact ⟨by omega, by omega⟩
  · have hji : j = i := hat _ hv
    subst j
    have hsub : T ⊆ {.inr ⟨i, k, false⟩, .inr ⟨i, k, true⟩} := by
      intro w hw
      obtain ⟨c, rfl⟩ := at_petal_eq_of_not_adj Y a k b (hat _ hw) (hind _ hv _ hw)
      cases c <;> simp
    exact ⟨(Finset.card_le_card hsub).trans Finset.card_le_two,
      fun _ ↦ Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt⟩

-- Lemma (claws in a generalized line graph)
/-- Assertion 1, step `s4clone`, of `lem:4-claws`, Remark 4.12 of [CGSS]:
a signed petal cannot be the centre of a three-claw. -/
theorem generalizedLineGraph_not_isClaw_petal (i : V) (k : Fin (a i)) (b : Bool)
    (T : Finset (GeneralizedLineGraphVertex Y a)) :
    ¬(generalizedLineGraph Y a).IsClaw (.inr ⟨i, k, b⟩) T := by
  intro h
  have hat : ∀ v ∈ T, v ∈ generalizedLineGraphAt Y a i := by
    rintro (e | ⟨j, l, c⟩) hv
    · exact h.adj _ hv
    · exact (h.adj _ hv).1.symm
  have hc := (generalizedLineGraph_independent_at_card_le Y a i T hat h.not_adj).1
  rw [h.card] at hc
  omega

/-- Step `s4clnbr`, Remark 4.12 of [CGSS]: every neighbour of an edge
is attached at one of its endpoints. -/
private theorem at_of_adj_edge {i j : V} (hij : Y.Adj i j)
    {v : GeneralizedLineGraphVertex Y a}
    (hv : (generalizedLineGraph Y a).Adj (.inl ⟨s(i, j), hij⟩) v) :
    v ∈ generalizedLineGraphAt Y a i ∨ v ∈ generalizedLineGraphAt Y a j := by
  rcases v with e | ⟨l, k, b⟩
  · obtain ⟨_, l, hl, he⟩ := lineGraph_adj_iff_exists.mp hv
    rcases Sym2.mem_iff.mp hl with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · exact Sym2.mem_iff.mp hv

/-- Step `s4clnbr`, Remark 4.12 of [CGSS]: a neighbour of an edge cannot
be attached at both of that edge's endpoints. -/
private theorem not_at_both_of_adj_edge {i j : V} (hij : Y.Adj i j)
    {v : GeneralizedLineGraphVertex Y a}
    (hv : (generalizedLineGraph Y a).Adj (.inl ⟨s(i, j), hij⟩) v)
    (hi : v ∈ generalizedLineGraphAt Y a i)
    (hj : v ∈ generalizedLineGraphAt Y a j) : False := by
  rcases v with e | ⟨l, k, b⟩
  · have he : e = ⟨s(i, j), hij⟩ := Subtype.ext
      (Sym2.eq_of_ne_mem hij.ne hi hj (by simp) (by simp))
    subst e
    exact (generalizedLineGraph Y a).loopless.irrefl _ hv
  · exact hij.ne (hi.symm.trans hj)

/-- Steps `s4cltwoonly` and `s4clthreeonly`, Remark 4.12 of [CGSS]: split
the leaves of a claw into the two endpoint classes. -/
private theorem independent_edge_parts {i j : V} (hij : Y.Adj i j)
    {k : ℕ} {T : Finset (GeneralizedLineGraphVertex Y a)}
    (h : (generalizedLineGraph Y a).IsClawOfSize k (.inl ⟨s(i, j), hij⟩) T) :
    ∃ A B : Finset (GeneralizedLineGraphVertex Y a),
      A.card + B.card = k ∧ A.card ≤ 2 ∧ B.card ≤ 2 ∧
      (1 < A.card → 0 < a i) ∧ (1 < B.card → 0 < a j) ∧
      (∀ v ∈ A, v ∈ generalizedLineGraphAt Y a i ∧ v ∈ T) ∧
      (∀ v ∈ B, v ∈ generalizedLineGraphAt Y a j ∧ v ∈ T) := by
  classical
  let A := T.filter (fun v ↦ v ∈ generalizedLineGraphAt Y a i)
  let B := T.filter (fun v ↦ v ∈ generalizedLineGraphAt Y a j)
  have hA : ∀ v ∈ A, v ∈ generalizedLineGraphAt Y a i ∧ v ∈ T := by
    intro v hv
    exact (Finset.mem_filter.mp hv).symm
  have hB : ∀ v ∈ B, v ∈ generalizedLineGraphAt Y a j ∧ v ∈ T := by
    intro v hv
    exact (Finset.mem_filter.mp hv).symm
  have hunion : A ∪ B = T := by
    ext v
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    exact ⟨fun hv ↦ hv.elim And.left And.left,
      fun hv ↦ (at_of_adj_edge Y a hij (h.adj v hv)).elim
        (fun hi ↦ Or.inl ⟨hv, hi⟩) (fun hj ↦ Or.inr ⟨hv, hj⟩)⟩
  have hdis : Disjoint A B := Finset.disjoint_left.mpr fun v hv hw ↦
    not_at_both_of_adj_edge Y a hij (h.adj v (hA v hv).2) (hA v hv).1 (hB v hw).1
  have hcA := generalizedLineGraph_independent_at_card_le Y a i A
    (fun v hv ↦ (hA v hv).1)
    (fun v hv w hw ↦ h.not_adj v (hA v hv).2 w (hA w hw).2)
  have hcB := generalizedLineGraph_independent_at_card_le Y a j B
    (fun v hv ↦ (hB v hv).1)
    (fun v hv w hw ↦ h.not_adj v (hB v hv).2 w (hB w hw).2)
  exact ⟨A, B, by rw [← Finset.card_union_of_disjoint hdis, hunion, h.card],
    hcA.1, hcB.1, hcA.2, hcB.2, hA, hB⟩

/-- Step `s4clcross`, Remark 4.12 of [CGSS]: a petal at one endpoint
is not adjacent to any neighbour of the edge at the other endpoint. -/
private theorem not_adj_petal_other_side {i j : V} (hij : Y.Adj i j)
    (k : Fin (a i)) (b : Bool) {v : GeneralizedLineGraphVertex Y a}
    (hv : (generalizedLineGraph Y a).Adj (.inl ⟨s(i, j), hij⟩) v)
    (hj : v ∈ generalizedLineGraphAt Y a j) :
    ¬(generalizedLineGraph Y a).Adj (.inr ⟨i, k, b⟩) v := by
  intro h
  have hi : v ∈ generalizedLineGraphAt Y a i := by
    cases v with
    | inl e => exact h
    | inr p => exact h.1.symm
  exact not_at_both_of_adj_edge Y a hij hv hi hj

/-- Step `s4cltwoif`, Remark 4.12 of [CGSS]: two opposite petals and
one neighbour at the other endpoint form a three-claw. -/
private theorem claw_of_opposite_petals {i j : V} (hij : Y.Adj i j)
    (hi : 0 < a i) {v : GeneralizedLineGraphVertex Y a}
    (hv : (generalizedLineGraph Y a).Adj (.inl ⟨s(i, j), hij⟩) v)
    (hj : v ∈ generalizedLineGraphAt Y a j) :
    ∃ T, (generalizedLineGraph Y a).IsClaw (.inl ⟨s(i, j), hij⟩) T := by
  classical
  let p : GeneralizedLineGraphVertex Y a := .inr ⟨i, ⟨0, hi⟩, false⟩
  let q : GeneralizedLineGraphVertex Y a := .inr ⟨i, ⟨0, hi⟩, true⟩
  have hpv : p ≠ v := by
    intro h
    subst v
    exact hij.ne hj
  have hqv : q ≠ v := by
    intro h
    subst v
    exact hij.ne hj
  have hpq : p ≠ q := by simp [p, q]
  have hnp := not_adj_petal_other_side Y a hij ⟨0, hi⟩ false hv hj
  have hnq := not_adj_petal_other_side Y a hij ⟨0, hi⟩ true hv hj
  have hnpq : ¬(generalizedLineGraph Y a).Adj p q := by simp [p, q, generalizedLineGraph]
  refine ⟨{p, q, v}, ?_, ?_, ?_⟩
  · simp [hpv, hqv, hpq]
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · change i ∈ s(i, j)
      simp
    · change i ∈ s(i, j)
      simp
    · exact hv
  · intro w hw z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
    rcases hw with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
      first | exact (generalizedLineGraph Y a).loopless.irrefl _
            | exact hnpq | exact hnp | exact hnq
            | exact fun h ↦ hnpq h.symm | exact fun h ↦ hnp h.symm
            | exact fun h ↦ hnq h.symm

variable [Fintype V] [DecidableRel Y.Adj]

/-- Step `s4clnbr`, Remark 4.12 of [CGSS]: the endpoint neighbour class
is nonempty exactly when the parameter-plus-degree bound is at least two. -/
private theorem at_neighbor_nonempty_iff {i j : V} (hij : Y.Adj i j) :
    (∃ v, (generalizedLineGraph Y a).Adj (.inl ⟨s(i, j), hij⟩) v ∧
      v ∈ generalizedLineGraphAt Y a j) ↔ 2 ≤ a j + Y.degree j := by
  classical
  let e : Y.edgeSet := ⟨s(i, j), hij⟩
  let ej : {f : Y.edgeSet // j ∈ f.val} := ⟨e, by simp [e]⟩
  constructor
  · rintro ⟨f | ⟨l, k, b⟩, hv, hat⟩
    · have hne : e ≠ f := (lineGraph_adj_iff_exists.mp hv).1
      have hc : 1 < (Finset.univ : Finset {f : Y.edgeSet // j ∈ f.val}).card :=
        Finset.one_lt_card.mpr ⟨ej, Finset.mem_univ _, ⟨f, hat⟩,
          Finset.mem_univ _, fun h ↦ hne (congrArg Subtype.val h)⟩
      rw [Finset.card_univ, Y.card_incident_edge_subtype] at hc
      omega
    · change l = j at hat
      subst l
      have hj := hij.symm.degree_pos_left
      have hk := k.isLt
      omega
  · intro h
    by_cases haj : a j = 0
    · have hc : 1 < (Finset.univ : Finset {f : Y.edgeSet // j ∈ f.val}).card := by
        rw [Finset.card_univ, Y.card_incident_edge_subtype]
        omega
      obtain ⟨f, _, hfe⟩ := Finset.univ.exists_mem_ne hc ej
      refine ⟨.inl f.val, ?_, f.property⟩
      exact lineGraph_adj_iff_exists.mpr
        ⟨fun h ↦ hfe (Subtype.ext h.symm), j, by simp, f.property⟩
    · exact ⟨.inr ⟨j, ⟨0, Nat.pos_of_ne_zero haj⟩, false⟩, by
        change j ∈ s(i, j)
        simp, rfl⟩

-- Lemma (claws in a generalized line graph)
/-- Assertion 2 of `lem:4-claws`, Remark 4.12 of [CGSS]: an edge centres a
three-claw exactly when one endpoint has petals and the other has another
neighbour. Steps `s4cltwoif` and `s4cltwoonly`. -/
theorem generalizedLineGraph_isClaw_edge_iff {i j : V} (hij : Y.Adj i j) :
    (∃ T, (generalizedLineGraph Y a).IsClaw (.inl ⟨s(i, j), hij⟩) T) ↔
      (0 < a i ∧ 2 ≤ a j + Y.degree j) ∨ (0 < a j ∧ 2 ≤ a i + Y.degree i) := by
  have he : (⟨s(j, i), hij.symm⟩ : Y.edgeSet) = ⟨s(i, j), hij⟩ :=
    Subtype.ext Sym2.eq_swap
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨A, B, hc, hA, hB, hi, hj, hAT, hBT⟩ := independent_edge_parts Y a hij hT
    have hAi : 2 ≤ a i + Y.degree i := by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      apply (at_neighbor_nonempty_iff Y a hij.symm).mp
      exact ⟨v, he ▸ hT.adj v (hAT v hv).2, (hAT v hv).1⟩
    have hBj : 2 ≤ a j + Y.degree j := by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
      exact (at_neighbor_nonempty_iff Y a hij).mp
        ⟨v, hT.adj v (hBT v hv).2, (hBT v hv).1⟩
    by_cases h : 1 < A.card
    · exact Or.inl ⟨hi h, hBj⟩
    · exact Or.inr ⟨hj (by omega), hAi⟩
  · rintro (⟨hi, hj⟩ | ⟨hj, hi⟩)
    · obtain ⟨v, hv, hat⟩ := (at_neighbor_nonempty_iff Y a hij).mpr hj
      exact claw_of_opposite_petals Y a hij hi hv hat
    · obtain ⟨v, hv, hat⟩ := (at_neighbor_nonempty_iff Y a hij.symm).mpr hi
      simpa only [he] using claw_of_opposite_petals Y a hij.symm hj hv hat

omit [Fintype V] [DecidableRel Y.Adj] in
-- Lemma (claws in a generalized line graph)
/-- Assertion 3 of `lem:4-claws`, Remark 4.12 of [CGSS]: an edge centres a
four-claw exactly when both endpoints have petals. Steps `s4clthreeif` and
`s4clthreeonly`. -/
theorem generalizedLineGraph_isFourClaw_edge_iff {i j : V} (hij : Y.Adj i j) :
    (∃ T, (generalizedLineGraph Y a).IsFourClaw (.inl ⟨s(i, j), hij⟩) T) ↔
      0 < a i ∧ 0 < a j := by
  classical
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨A, B, hc, hA, hB, hi, hj, _, _⟩ := independent_edge_parts Y a hij hT
    exact ⟨hi (by omega), hj (by omega)⟩
  · rintro ⟨hi, hj⟩
    let p : Bool → GeneralizedLineGraphVertex Y a := fun b ↦ .inr ⟨i, ⟨0, hi⟩, b⟩
    let q : Bool → GeneralizedLineGraphVertex Y a := fun b ↦ .inr ⟨j, ⟨0, hj⟩, b⟩
    refine ⟨{p false, p true, q false, q true}, ?_, ?_, ?_⟩
    · simp [p, q, hij.ne]
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;>
        simp [p, q, generalizedLineGraph]
    · intro v hv w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl | rfl | rfl <;>
        rcases hw with rfl | rfl | rfl | rfl <;>
        simp [p, q, generalizedLineGraph, hij.ne, hij.ne.symm]

end SimpleGraph
