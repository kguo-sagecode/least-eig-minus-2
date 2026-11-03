/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Graphs.Basic
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

/-!
# The triangle property in Section 2 of [CGSS]

The predicate in `def:triangle-property` includes both uniqueness of the triangle on an edge
and the condition on vertices outside that triangle. Step labels refer to `sec2-lines.tex`.
-/

namespace SimpleGraph


variable {U : Type*} {X : SimpleGraph U}

-- Lemma 2.8 (following definition)
/-- The triangle property (`def:triangle-property`, after Lemma 2.8 of [CGSS]): each edge has
one common neighbour, and each outside vertex sees exactly one vertex of its triangle. -/
def HasTriangleProperty (X : SimpleGraph U) : Prop :=
  ∀ ⦃x y⦄, X.Adj x y → ∃ z, X.Adj x z ∧ X.Adj y z ∧
    (∀ w, X.Adj x w → X.Adj y w → w = z) ∧
    ∀ w, w ≠ x → w ≠ y → w ≠ z →
      (X.Adj w x ∧ ¬X.Adj w y ∧ ¬X.Adj w z) ∨
      (¬X.Adj w x ∧ X.Adj w y ∧ ¬X.Adj w z) ∨
      (¬X.Adj w x ∧ ¬X.Adj w y ∧ X.Adj w z)

namespace HasTriangleProperty

variable (hX : X.HasTriangleProperty)

include hX

/-- The unique common neighbour in `def:triangle-property`, after Lemma 2.8 of [CGSS];
also steps 210triangles and 210third of `lem:triangle-normal-form`. -/
theorem existsUnique_common_neighbor {x y : U} (hxy : X.Adj x y) :
    ∃! z, X.Adj x z ∧ X.Adj y z := by
  obtain ⟨z, hxz, hyz, hz, _⟩ := hX hxy
  exact ⟨z, ⟨hxz, hyz⟩, fun w hw ↦ hz w hw.1 hw.2⟩

/-- Uniqueness in `def:triangle-property`, used in Lemmas 2.9 and 2.10 of [CGSS]. -/
theorem common_neighbor_unique {x y z w : U} (hxy : X.Adj x y)
    (hxz : X.Adj x z) (hyz : X.Adj y z) (hxw : X.Adj x w) (hyw : X.Adj y w) : z = w :=
  (hX.existsUnique_common_neighbor hxy).unique ⟨hxz, hyz⟩ ⟨hxw, hyw⟩

/-- The outside-vertex clause of `def:triangle-property`, used in Lemmas 2.9 and 2.10
of [CGSS], applies to any ordering of a triangle. -/
theorem outside {x y z w : U} (hxy : X.Adj x y) (hxz : X.Adj x z)
    (hyz : X.Adj y z) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    (X.Adj w x ∧ ¬X.Adj w y ∧ ¬X.Adj w z) ∨
    (¬X.Adj w x ∧ X.Adj w y ∧ ¬X.Adj w z) ∨
    (¬X.Adj w x ∧ ¬X.Adj w y ∧ X.Adj w z) := by
  obtain ⟨t, _, _, ht, hout⟩ := hX hxy
  obtain rfl := ht z hxz hyz
  exact hout w hwx hwy hwz

/-- The third vertex on an edge (`def:triangle-property`, Lemmas 2.9–2.10 of [CGSS]). -/
noncomputable def third {x y : U} (hxy : X.Adj x y) : U :=
  (hX.existsUnique_common_neighbor hxy).choose

/-- Step 29exists of Lemma 2.9 of [CGSS]: the third vertex sees the first endpoint. -/
theorem adj_third_left {x y : U} (hxy : X.Adj x y) : X.Adj x (hX.third hxy) :=
  (hX.existsUnique_common_neighbor hxy).choose_spec.1.1

/-- Step 29exists of Lemma 2.9 of [CGSS]: the third vertex sees the second endpoint. -/
theorem adj_third_right {x y : U} (hxy : X.Adj x y) : X.Adj y (hX.third hxy) :=
  (hX.existsUnique_common_neighbor hxy).choose_spec.1.2

/-- Step 29mate of Lemma 2.9 of [CGSS]: taking the partner twice returns the endpoint. -/
theorem third_third {x y : U} (hxy : X.Adj x y) :
    hX.third (hX.adj_third_left hxy) = y :=
  hX.common_neighbor_unique (hX.adj_third_left hxy)
    (hX.adj_third_left _) (hX.adj_third_right _) hxy (hX.adj_third_right hxy).symm

/-- Steps 29mate and 210involution of Lemmas 2.9–2.10 of [CGSS]: triangle partners
give an involution on a neighbourhood. -/
noncomputable def neighborPairing (x : U) : X.neighborSet x ≃ X.neighborSet x where
  toFun y := ⟨hX.third y.property, hX.adj_third_left y.property⟩
  invFun y := ⟨hX.third y.property, hX.adj_third_left y.property⟩
  left_inv y := Subtype.ext (hX.third_third y.property)
  right_inv y := Subtype.ext (hX.third_third y.property)

/-- Step 29mate of Lemma 2.9 of [CGSS]: the neighbourhood involution has no fixed points. -/
theorem neighborPairing_ne (x : U) (y : X.neighborSet x) : hX.neighborPairing x y ≠ y := by
  intro he
  exact (hX.adj_third_right y.property).ne (congrArg Subtype.val he).symm

/-- Steps 29edges and 210involution of Lemmas 2.9–2.10 of [CGSS]: the triangle pairs
are all the edges in a neighbourhood. -/
theorem adj_iff_neighborPairing (x : U) (y z : X.neighborSet x) :
    X.Adj y z ↔ hX.neighborPairing x y = z := by
  constructor
  · intro hyz
    exact Subtype.ext (hX.common_neighbor_unique y.property
      (hX.adj_third_left y.property) (hX.adj_third_right y.property) z.property hyz)
  · rintro rfl
    exact hX.adj_third_right y.property

/-- Step 29pairs of Lemma 2.9 of [CGSS]: a finite neighbourhood is a union of
disjoint labelled pairs, with precisely the matching edges. -/
theorem exists_neighbor_pair_labels [Finite U] (x : U) :
    ∃ m : ℕ, ∃ e : (Fin m × Bool) ≃ X.neighborSet x,
      ∀ p q, X.Adj (e p) (e q) ↔ p.1 = q.1 ∧ p.2 ≠ q.2 := by
  classical
  let : Fintype (X.neighborSet x) := Fintype.ofFinite _
  let f := hX.neighborPairing x
  let index := Fintype.equivFin (X.neighborSet x)
  let R := {y : X.neighborSet x // index y < index (f y)}
  have hf (y : X.neighborSet x) : f (f y) = y := f.left_inv y
  have hn (y : X.neighborSet x) : f y ≠ y := hX.neighborPairing_ne x y
  let g : R × Bool → X.neighborSet x := fun p ↦ if p.2 then f p.1.val else p.1.val
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨r, b⟩ ⟨s, c⟩ he
      cases b <;> cases c
      · have hrs : r = s := Subtype.ext he
        exact congrArg (fun t : R ↦ (t, false)) hrs
      · have hrs : r.val = f s.val := he
        have hr := r.property
        rw [hrs, hf] at hr
        exact False.elim ((not_lt_of_gt s.property) hr)
      · have hrs : f r.val = s.val := he
        have hs := s.property
        rw [← hrs, hf] at hs
        exact False.elim ((not_lt_of_gt r.property) hs)
      · have hrs : r = s := Subtype.ext (f.injective he)
        exact congrArg (fun t : R ↦ (t, true)) hrs
    · intro y
      by_cases hy : index y < index (f y)
      · exact ⟨(⟨y, hy⟩, false), rfl⟩
      · have hy' : index (f y) < index y :=
          lt_of_le_of_ne (le_of_not_gt hy) (fun he ↦ hn y (index.injective he))
        exact ⟨(⟨f y, by simpa only [hf] using hy'⟩, true), hf y⟩
  let e₀ := Equiv.ofBijective g hg
  let e₁ : (Fin (Fintype.card R) × Bool) ≃ R × Bool :=
    Equiv.prodCongr (Fintype.equivFin R).symm (Equiv.refl Bool)
  refine ⟨Fintype.card R, e₁.trans e₀, ?_⟩
  intro p q
  have hpair (r : R) (b : Bool) : f (g (r, b)) = g (r, !b) := by
    cases b <;> simp [g, hf]
  rw [hX.adj_iff_neighborPairing]
  change f (g (e₁ p)) = g (e₁ q) ↔ _
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, c⟩
  change f (g ((Fintype.equivFin R).symm i, b)) =
    g ((Fintype.equivFin R).symm j, c) ↔ _
  rw [hpair, hg.1.eq_iff, Prod.mk.injEq, (Fintype.equivFin R).symm.injective.eq_iff]
  cases b <;> cases c <;> simp

/-- Lemma 2.9 of [CGSS], in pure graph form: a universal vertex makes a finite graph
with the triangle property a friendship graph, including the zero-pair case. -/
theorem nonempty_iso_friendship_of_forall_adj [Finite U] (x : U)
    (hx : ∀ y, y ≠ x → X.Adj x y) : ∃ m, Nonempty (X ≃g friendship m) := by
  classical
  -- ⟨1⟩1–2 (29mate, 29pairs).
  obtain ⟨m, e, he⟩ := hX.exists_neighbor_pair_labels x
  let e' : X.neighborSet x ≃ {y // y ≠ x} :=
    Equiv.subtypeEquivRight (fun y ↦ ⟨fun hy ↦ hy.ne.symm, hx y⟩)
  let E : Option (Fin m × Bool) ≃ U :=
    (Equiv.optionCongr (e.trans e')).trans (Equiv.optionSubtypeNe x)
  refine ⟨m, ⟨(show friendship m ≃g X from { E with map_rel_iff' := ?_ }).symm⟩⟩
  -- ⟨1⟩3 (29edges): these exhaust the edges, including all edges at the centre.
  rintro (_ | p) (_ | q)
  · exact iff_of_false X.irrefl (by simp [friendship])
  · change X.Adj x (e q) ↔ True
    exact iff_true_intro (e q).property
  · change X.Adj (e p) x ↔ True
    exact iff_true_intro (e p).property.symm
  · exact he p q

/-- Step 210positive of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
if an edge exists, every vertex has a neighbour. -/
theorem exists_adj (hedge : ∃ x y, X.Adj x y) (w : U) : ∃ z, X.Adj w z := by
  obtain ⟨x, y, hxy⟩ := hedge
  obtain ⟨z, hxz, hyz, _, hout⟩ := hX hxy
  by_cases hwx : w = x
  · exact ⟨y, hwx ▸ hxy⟩
  by_cases hwy : w = y
  · exact ⟨x, hwy ▸ hxy.symm⟩
  by_cases hwz : w = z
  · exact ⟨x, hwz ▸ hxz.symm⟩
  rcases hout w hwx hwy hwz with h | h | h
  · exact ⟨x, h.1⟩
  · exact ⟨y, h.2.1⟩
  · exact ⟨z, h.2.2⟩

/-- Steps 210pairing and 210onto of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: a non-neighbour sees exactly one point of each triangle pair. -/
theorem adj_neighborPairing_iff {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (y : X.neighborSet u) : X.Adj v (hX.neighborPairing u y) ↔ ¬X.Adj v y := by
  have hvy : v ≠ y := fun he ↦ hnav (he ▸ y.property)
  have hvz : v ≠ hX.third y.property :=
    fun he ↦ hnav (he ▸ hX.adj_third_left y.property)
  have h := hX.outside y.property (hX.adj_third_left y.property)
    (hX.adj_third_right y.property) huv.symm hvy hvz
  change X.Adj v (hX.third y.property) ↔ ¬X.Adj v y
  have hvu : ¬X.Adj v u := fun h ↦ hnav h.symm
  tauto

/-- Steps 210labels and 210onto of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: triangle partners biject the common neighbours with `L`. -/
noncomputable def commonNeighborsEquiv (u v : U) (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    X.commonNeighbors u v ≃ ↥(X.neighborSet u \ X.neighborSet v) where
  toFun y := ⟨hX.third y.property.1, hX.adj_third_left y.property.1, by
    have h := hX.adj_neighborPairing_iff huv hnav ⟨y, y.property.1⟩
    exact fun hz ↦ h.mp hz y.property.2⟩
  invFun y := ⟨hX.third y.property.1, hX.adj_third_left y.property.1,
    (hX.adj_neighborPairing_iff huv hnav ⟨y, y.property.1⟩).mpr y.property.2⟩
  left_inv y := Subtype.ext (hX.third_third y.property.1)
  right_inv y := Subtype.ext (hX.third_third y.property.1)

/-- Step 210local of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the degree at either end of a nonedge is twice the number of common neighbours. -/
theorem degree_eq_two_mul_card_commonNeighbors [Fintype U] [DecidableRel X.Adj]
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    X.degree u = 2 * Fintype.card (X.commonNeighbors u v) := by
  classical
  let p : X.neighborSet u → Prop := fun y ↦ X.Adj v y
  let e : {y // p y} ≃ {y // ¬p y} :=
    (hX.neighborPairing u).subtypeEquiv (fun y ↦ by
      change X.Adj v y ↔ ¬X.Adj v (hX.neighborPairing u y)
      rw [hX.adj_neighborPairing_iff huv hnav, not_not])
  have hc := Fintype.card_congr e
  have hk : Fintype.card {y // p y} = Fintype.card (X.commonNeighbors u v) :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (X.Adj u) (X.Adj v))
  rw [Fintype.card_subtype_compl] at hc
  have hle := Fintype.card_subtype_le p
  rw [X.card_neighborSet_eq_degree] at hc hle
  omega

/-- Step 210nonadjdeg of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
distinct nonadjacent vertices have equal degrees. -/
theorem degree_eq_of_not_adj [Fintype U] [DecidableRel X.Adj] {u v : U}
    (huv : u ≠ v) (hnav : ¬X.Adj u v) : X.degree u = X.degree v := by
  rw [hX.degree_eq_two_mul_card_commonNeighbors huv hnav,
    hX.degree_eq_two_mul_card_commonNeighbors huv.symm (fun h ↦ hnav h.symm)]
  congr 1
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight (fun _ ↦ and_comm) :
      X.commonNeighbors u v ≃ X.commonNeighbors v u)

/-- Step 210regular (including 210adjdeg) of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]: absence of a universal vertex propagates equality of degrees. -/
theorem degree_eq_of_not_forall_adj [Fintype U] [DecidableRel X.Adj]
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y) (p q : U) : X.degree p = X.degree q := by
  classical
  by_cases hpq : p = q
  · rw [hpq]
  by_cases hapq : X.Adj p q
  · let r := hX.third hapq
    have hpr : X.Adj p r := hX.adj_third_left hapq
    have hqr : X.Adj q r := hX.adj_third_right hapq
    -- ⟨2⟩1 (210s), using 210nouniversal: `hn` supplies a distinct non-neighbour.
    obtain ⟨s, hsp, hps⟩ := hn p
    have hsq : s ≠ q := fun he ↦ hps (he ▸ hapq)
    have hsr : s ≠ r := fun he ↦ hps (he ▸ hpr)
    have hs := hX.outside hapq hpr hqr hsp hsq hsr
    have hds : X.degree p = X.degree s := hX.degree_eq_of_not_adj hsp.symm hps
    rcases hs with hs | hs | hs
    · exact False.elim (hps hs.1.symm)
    · -- ⟨2⟩3 (210seesq), ⟨3⟩1 (210prdeg).
      have hdr : X.degree p = X.degree r := hds.trans (hX.degree_eq_of_not_adj hsr hs.2.2)
      -- ⟨3⟩2–3 (210t, 210tdegrees).
      obtain ⟨t, htq, hqt⟩ := hn q
      have htp : t ≠ p := fun he ↦ hqt (he ▸ hapq.symm)
      have htr : t ≠ r := fun he ↦ hqt (he ▸ hqr)
      have ht := hX.outside hapq hpr hqr htp htq htr
      have hdt : X.degree q = X.degree t := hX.degree_eq_of_not_adj htq.symm hqt
      rcases ht with ht | ht | ht
      · exact hdr.trans (hdt.trans (hX.degree_eq_of_not_adj htr ht.2.2)).symm
      · exact False.elim (hqt ht.2.1.symm)
      · exact (hdt.trans (hX.degree_eq_of_not_adj htp ht.1)).symm
    · -- ⟨2⟩2 (210seesr).
      exact hds.trans (hX.degree_eq_of_not_adj hsq hs.2.1)
  · exact hX.degree_eq_of_not_adj hpq hapq

/-- Step 210labels of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
two neighbours of `u` seen in the same way by its non-neighbour `v` are nonadjacent. -/
theorem not_adj_of_same_adjacency {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (y z : X.neighborSet u) (hyz : X.Adj v y ↔ X.Adj v z) : ¬X.Adj y z := by
  intro ha
  have he := (hX.adj_iff_neighborPairing u y z).mp ha
  have hp := hX.adj_neighborPairing_iff huv hnav y
  rw [he] at hp
  tauto

/-- Step 210labels of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the common-neighbour part `K` is independent. -/
theorem isIndepSet_commonNeighbors {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    X.IsIndepSet (X.commonNeighbors u v) := by
  intro y hy z hz _
  exact hX.not_adj_of_same_adjacency huv hnav ⟨y, hy.1⟩ ⟨z, hz.1⟩
    (iff_of_true hy.2 hz.2)

/-- Step 210labels of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the part `L` is independent; exchanging `u,v` gives the same assertion for `M`. -/
theorem isIndepSet_neighborSet_diff {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    X.IsIndepSet (X.neighborSet u \ X.neighborSet v) := by
  intro y hy z hz _
  exact hX.not_adj_of_same_adjacency huv hnav ⟨y, hy.1⟩ ⟨z, hz.1⟩
    (iff_of_false hy.2 hz.2)

/-- Step 210labels of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the only edges from `K` to `L` are the labelled matching pairs. -/
theorem adj_commonNeighborsEquiv_iff {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (x y : X.commonNeighbors u v) :
    X.Adj x (hX.commonNeighborsEquiv u v huv hnav y) ↔ x = y := by
  have h := hX.adj_iff_neighborPairing u ⟨x, x.property.1⟩
    (hX.neighborPairing u ⟨y, y.property.1⟩)
  rw [(hX.neighborPairing u).injective.eq_iff, Subtype.mk.injEq, Subtype.val_inj] at h
  exact h

/-- Steps 210lm, 210same and 210different of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: the edges from `L` to `M` join different labels. -/
theorem adj_commonNeighborsEquiv_comm_iff {u v : U} (huv : u ≠ v)
    (hnav : ¬X.Adj u v) (x y : X.commonNeighbors u v) :
    X.Adj (hX.commonNeighborsEquiv u v huv hnav x)
      (hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
        ⟨y, y.property.2, y.property.1⟩) ↔ x ≠ y := by
  let l := hX.commonNeighborsEquiv u v huv hnav
  let m := hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
  let y' : X.commonNeighbors v u := ⟨y, y.property.2, y.property.1⟩
  change X.Adj (l x) (m y') ↔ x ≠ y
  have hlx : X.Adj x (l x) := hX.adj_third_right x.property.1
  have hmy : X.Adj y (m y') := hX.adj_third_right y.property.2
  constructor
  · -- ⟨3⟩1 (210same).
    intro hlm hexy
    subst y
    have he : u = (m y' : U) := hX.common_neighbor_unique hlx
      x.property.1.symm (l x).property.1.symm hmy hlm
    exact hnav (he ▸ (m y').property.1.symm)
  · -- ⟨3⟩2 (210different).
    intro hxy
    have hlv : (l x : U) ≠ v := fun he ↦ hnav (he ▸ (l x).property.1)
    have hly : (l x : U) ≠ y := fun he ↦ (l x).property.2 (he ▸ y.property.2)
    have hlm : (l x : U) ≠ m y' := fun he ↦ (l x).property.2 (he ▸ (m y').property.1)
    have h := hX.outside y.property.2 (m y').property.1 hmy hlv hly hlm
    have hnly : ¬X.Adj (l x) y := fun ha ↦
      hxy ((hX.adj_commonNeighborsEquiv_iff huv hnav y x).mp ha.symm).symm
    have hnlv : ¬X.Adj (l x) v := fun ha ↦ (l x).property.2 ha.symm
    tauto

/-- Step 210signature of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
a vertex in `N` sees a label in `L` exactly when it misses that label in `K`. -/
theorem adj_commonNeighborsEquiv_iff_not_adj {u v w : U} (huv : u ≠ v)
    (hnav : ¬X.Adj u v) (hwu : w ≠ u) (hnuw : ¬X.Adj u w)
    (x : X.commonNeighbors u v) :
    X.Adj w (hX.commonNeighborsEquiv u v huv hnav x) ↔ ¬X.Adj w x :=
  hX.adj_neighborPairing_iff hwu.symm hnuw ⟨x, x.property.1⟩

/-- Steps 210Nthird and 210NtoK of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]:
an edge in `N` has its third vertex in `K`. Here `N` is the common-neighbour set in
the complement, so the two endpoints `u,v` are excluded. -/
theorem third_mem_commonNeighbors {u v w z : U}
    (hw : w ∈ Xᶜ.commonNeighbors u v) (hz : z ∈ Xᶜ.commonNeighbors u v)
    (hwz : X.Adj w z) : hX.third hwz ∈ X.commonNeighbors u v := by
  -- ⟨3⟩1 (210Noutside), ⟨3⟩2: neither endpoint sees the edge in `N`.
  have hu := hX.adj_neighborPairing_iff hw.1.1.symm
    (fun ha ↦ hw.1.2 ha.symm) ⟨z, hwz⟩
  have hv := hX.adj_neighborPairing_iff hw.2.1.symm
    (fun ha ↦ hw.2.2 ha.symm) ⟨z, hwz⟩
  exact ⟨hu.mpr hz.1.2, hv.mpr hz.2.2⟩

/-- Step 210KtoN of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the triangle partner at a vertex of `N` takes its `K` neighbours into `N`. -/
theorem third_mem_compl_commonNeighbors {u v w x : U}
    (hw : w ∈ Xᶜ.commonNeighbors u v) (hx : x ∈ X.commonNeighbors u v)
    (hwx : X.Adj w x) : hX.third hwx ∈ Xᶜ.commonNeighbors u v := by
  have hu := hX.adj_neighborPairing_iff hw.1.1.symm
    (fun ha ↦ hw.1.2 ha.symm) ⟨x, hwx⟩
  have hv := hX.adj_neighborPairing_iff hw.2.1.symm
    (fun ha ↦ hw.2.2 ha.symm) ⟨x, hwx⟩
  refine ⟨⟨?_, fun ha ↦ hu.mp ha hx.1⟩, ⟨?_, fun ha ↦ hv.mp ha hx.2⟩⟩
  · intro he
    exact hw.1.2 (he ▸ (hX.adj_third_left hwx).symm)
  · intro he
    exact hw.2.2 (he ▸ (hX.adj_third_left hwx).symm)

/-- Step 210KNpairing of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
triangle partners biject the `K` and `N` neighbours of a vertex in `N`. -/
noncomputable def commonNeighborsPairing {u v w : U}
    (hw : w ∈ Xᶜ.commonNeighbors u v) :
    ↥(X.commonNeighbors u v ∩ X.neighborSet w) ≃
      ↥(Xᶜ.commonNeighbors u v ∩ X.neighborSet w) where
  toFun x := ⟨hX.third x.property.2,
    hX.third_mem_compl_commonNeighbors hw x.property.1 x.property.2,
    hX.adj_third_left x.property.2⟩
  invFun z := ⟨hX.third z.property.2,
    hX.third_mem_commonNeighbors hw z.property.1 z.property.2,
    hX.adj_third_left z.property.2⟩
  left_inv x := Subtype.ext (hX.third_third x.property.2)
  right_inv z := Subtype.ext (hX.third_third z.property.2)

/-- Steps 210LMclosed and 210KNpairing of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]: at a vertex of `N`, the partner of a neighbour in `L` lies in `M`. -/
theorem third_mem_neighborSet_diff {u v w y : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hw : w ∈ Xᶜ.commonNeighbors u v) (hy : y ∈ X.neighborSet u \ X.neighborSet v)
    (hwy : X.Adj w y) : hX.third hwy ∈ X.neighborSet v \ X.neighborSet u := by
  let z := hX.third hwy
  have hwz : X.Adj w z := hX.adj_third_left hwy
  have hyz : X.Adj y z := hX.adj_third_right hwy
  -- 210partnerback: uniqueness makes the triangle pairing involutive.
  have hzback : hX.third hwz = y := hX.third_third hwy
  -- 210partnernotUV: both distinguished vertices miss `w`.
  have huz : u ≠ z := fun he ↦ hw.1.2 (he ▸ hwz.symm)
  have hvz : v ≠ z := fun he ↦ hw.2.2 (he ▸ hwz.symm)
  -- ⟨4⟩3 (210partnernotK), ⟨4⟩4 (210partnernotN).
  have hnK : z ∉ X.commonNeighbors u v := by
    intro hz
    have h := hX.third_mem_compl_commonNeighbors hw hz hwz
    rw [hzback] at h
    exact h.1.2 hy.1
  have hnN : z ∉ Xᶜ.commonNeighbors u v := by
    intro hz
    have h := hX.third_mem_commonNeighbors hw hz hwz
    rw [hzback] at h
    exact hy.2 h.2
  -- The partition leaves `L ∪ M`; independence excludes `L`.
  by_cases huz' : X.Adj u z
  · have hvz' : ¬X.Adj v z := fun ha ↦ hnK ⟨huz', ha⟩
    exact False.elim (hX.isIndepSet_neighborSet_diff huv hnav hy
      ⟨huz', hvz'⟩ hyz.ne hyz)
  · have hvz' : X.Adj v z := by
      by_contra hn
      exact hnN ⟨⟨huz, huz'⟩, ⟨hvz, hn⟩⟩
    exact ⟨hvz', huz'⟩

/-- Steps 210common and 210Asize of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: if `w ∈ N` misses a point `x ∈ K`, it misses exactly one other point. -/
theorem existsUnique_other_non_neighbor {u v w : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hw : w ∈ Xᶜ.commonNeighbors u v) (x : X.commonNeighbors u v) (hwx : ¬X.Adj w x) :
    ∃! y : X.commonNeighbors u v, y ≠ x ∧ ¬X.Adj w y := by
  let l := hX.commonNeighborsEquiv u v huv hnav
  let m := hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
  have hwl : X.Adj w (l x) :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv hnav hw.1.1.symm hw.1.2 x).mpr hwx
  let z : ↥(X.neighborSet v \ X.neighborSet u) :=
    ⟨hX.third hwl, hX.third_mem_neighborSet_diff huv hnav hw (l x).property hwl⟩
  let y' := m.symm z
  let y : X.commonNeighbors u v := ⟨y', y'.property.2, y'.property.1⟩
  have hmy : m ⟨y, y.property.2, y.property.1⟩ = z := m.apply_symm_apply z
  have hxy : x ≠ y := (hX.adj_commonNeighborsEquiv_comm_iff huv hnav x y).mp
    (show X.Adj (l x) (m ⟨y, y.property.2, y.property.1⟩) from
      hmy.symm ▸ hX.adj_third_right hwl)
  have hwv : w ∈ Xᶜ.commonNeighbors v u := ⟨hw.2, hw.1⟩
  have hnwy : ¬X.Adj w y :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv.symm (fun h ↦ hnav h.symm)
      hwv.1.1.symm hwv.1.2 ⟨y, y.property.2, y.property.1⟩).mp
        (hmy.symm ▸ hX.adj_third_left hwl)
  refine ⟨y, ⟨hxy.symm, hnwy⟩, ?_⟩
  intro t ht
  have hwt : X.Adj w (m ⟨t, t.property.2, t.property.1⟩) :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv.symm (fun h ↦ hnav h.symm)
      hwv.1.1.symm hwv.1.2 ⟨t, t.property.2, t.property.1⟩).mpr ht.2
  have hlt : X.Adj (l x) (m ⟨t, t.property.2, t.property.1⟩) :=
    (hX.adj_commonNeighborsEquiv_comm_iff huv hnav x t).mpr ht.1.symm
  have he : (m ⟨t, t.property.2, t.property.1⟩ : U) = z :=
    hX.common_neighbor_unique hwl hwt hlt
      (hX.adj_third_left hwl) (hX.adj_third_right hwl)
  have he' := m.injective ((Subtype.ext he).trans hmy.symm)
  exact Subtype.ext (congrArg (fun t : X.commonNeighbors v u ↦ (t : U)) he')

/-- Step 210dK of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the missed set `A(w)` has cardinality zero or two. -/
theorem card_non_neighbors_eq_zero_or_two [Fintype U] [DecidableRel X.Adj]
    {u v w : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hw : w ∈ Xᶜ.commonNeighbors u v) :
    Fintype.card {x : X.commonNeighbors u v // ¬X.Adj w x} = 0 ∨
      Fintype.card {x : X.commonNeighbors u v // ¬X.Adj w x} = 2 := by
  classical
  by_cases ha : ∃ x : X.commonNeighbors u v, ¬X.Adj w x
  · obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy, hunique⟩ := hX.existsUnique_other_non_neighbor huv hnav hw x hx
    right
    have hmem (z : X.commonNeighbors u v) : ¬X.Adj w z ↔ z ∈ ({x, y} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hz
        by_cases hzx : z = x
        · exact Or.inl hzx
        · exact Or.inr (hunique z ⟨hzx, hz⟩)
      · rintro (rfl | rfl)
        · exact hx
        · exact hy.2
    rw [Fintype.card_of_subtype {x, y} (fun z ↦ (hmem z).symm)]
    simp [hy.1.symm]
  · left
    exact Fintype.card_eq_zero_iff.mpr ⟨fun x ↦ ha ⟨x, x.property⟩⟩

/-- Step 210kone of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
in a graph of degree two, a triangle already contains every vertex. -/
theorem eq_or_eq_or_eq_of_degree_two [Fintype U] [DecidableRel X.Adj]
    (hreg : X.IsRegularOfDegree 2) {x y z : U} (hxy : X.Adj x y) (hxz : X.Adj x z)
    (hyz : X.Adj y z) (w : U) : w = x ∨ w = y ∨ w = z := by
  classical
  by_contra hn
  have hwx : w ≠ x := fun he ↦ hn (Or.inl he)
  have hwy : w ≠ y := fun he ↦ hn (Or.inr (Or.inl he))
  have hwz : w ≠ z := fun he ↦ hn (Or.inr (Or.inr he))
  have hfull (a b c : U) (hab : X.Adj a b) (hac : X.Adj a c)
      (hbc : b ≠ c) (hwb : w ≠ b) (hwc : w ≠ c) : ¬X.Adj w a := by
    intro hwa
    have hsub : ({b, c, w} : Finset U) ⊆ X.neighborFinset a := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact (X.mem_neighborFinset _ _).mpr hab
      · exact (X.mem_neighborFinset _ _).mpr hac
      · exact (X.mem_neighborFinset _ _).mpr hwa.symm
    have hc : ({b, c, w} : Finset U).card = 3 := by simp [hbc, hwb.symm, hwc.symm]
    have hle := Finset.card_le_card hsub
    rw [hc, X.card_neighborFinset_eq_degree, hreg a] at hle
    omega
  rcases hX.outside hxy hxz hyz hwx hwy hwz with h | h | h
  · exact hfull x y z hxy hxz hyz.ne hwy hwz h.1
  · exact hfull y x z hxy.symm hyz hxz.ne hwx hwz h.2.1
  · exact hfull z x y hxz.symm hyz.symm hxy.ne hwx hwy h.2.2

/-- Step 210kge of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the common-neighbour parameter of a nonedge is at least two. -/
theorem two_le_card_commonNeighbors [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    2 ≤ Fintype.card (X.commonNeighbors u v) := by
  have hdu := hX.degree_eq_two_mul_card_commonNeighbors huv hnav
  have hpos := (X.degree_pos_iff_exists_adj u).mpr (hX.exists_adj hedge u)
  by_contra hlt
  -- 210negative: the right side is negative when `k > 5`.
  have hk : Fintype.card (X.commonNeighbors u v) = 1 := by omega
  have hreg : X.IsRegularOfDegree 2 := fun w ↦ by
    rw [hX.degree_eq_of_not_forall_adj hn w u, hdu, hk]
  obtain ⟨x, y, hxy⟩ := hedge
  obtain ⟨w, hwx, hxw⟩ := hn x
  rcases hX.eq_or_eq_or_eq_of_degree_two hreg hxy (hX.adj_third_left hxy)
    (hX.adj_third_right hxy) w with he | he | he
  · exact hwx he
  · exact hxw (he ▸ hxy)
  · exact hxw (he ▸ hX.adj_third_left hxy)

/-- Step 210degreesintoN of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: a vertex of `K` has precisely four neighbours outside `N`. -/
theorem neighborSet_diff_compl_commonNeighbors {u v : U} (huv : u ≠ v)
    (hnav : ¬X.Adj u v) (x : X.commonNeighbors u v) :
    X.neighborSet x \ Xᶜ.commonNeighbors u v =
      {u, v, hX.third x.property.1, hX.third x.property.2} := by
  let l := hX.commonNeighborsEquiv u v huv hnav x
  let m := hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
    ⟨x, x.property.2, x.property.1⟩
  ext y
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hxy, hnN⟩
    by_cases hyu : y = u
    · exact Or.inl hyu
    by_cases hyv : y = v
    · exact Or.inr (Or.inl hyv)
    by_cases huy : X.Adj u y
    · exact Or.inr (Or.inr (Or.inl (hX.common_neighbor_unique x.property.1 huy hxy
        (hX.adj_third_left x.property.1) (hX.adj_third_right x.property.1))))
    by_cases hvy : X.Adj v y
    · exact Or.inr (Or.inr (Or.inr (hX.common_neighbor_unique x.property.2 hvy hxy
        (hX.adj_third_left x.property.2) (hX.adj_third_right x.property.2))))
    exact False.elim (hnN ⟨⟨Ne.symm hyu, huy⟩, ⟨Ne.symm hyv, hvy⟩⟩)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨x.property.1.symm, fun h ↦ h.1.1 rfl⟩
    · exact ⟨x.property.2.symm, fun h ↦ h.2.1 rfl⟩
    · exact ⟨hX.adj_third_right x.property.1,
        fun h ↦ h.1.2 (hX.adj_third_left x.property.1)⟩
    · exact ⟨hX.adj_third_right x.property.2,
        fun h ↦ h.2.2 (hX.adj_third_left x.property.2)⟩

/-- Step 210degreesintoN of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: the number of `N` neighbours of `x ∈ K`, plus four, is its degree. -/
theorem ncard_neighbors_in_compl_commonNeighbors_add_four [Fintype U] [DecidableRel X.Adj]
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) (x : X.commonNeighbors u v) :
    (Xᶜ.commonNeighbors u v ∩ X.neighborSet x).ncard + 4 = X.degree x := by
  let l := hX.commonNeighborsEquiv u v huv hnav x
  let m := hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
    ⟨x, x.property.2, x.property.1⟩
  have hul : u ≠ (l : U) := l.property.1.ne
  have hvm : v ≠ (m : U) := m.property.1.ne
  have hum : u ≠ (m : U) := fun he ↦ hnav (he ▸ m.property.1.symm)
  have hvl : v ≠ (l : U) := fun he ↦ hnav (he ▸ l.property.1)
  have hlm : (l : U) ≠ m := fun he ↦ m.property.2 (he ▸ l.property.1)
  have hc : ({u, v, (l : U), (m : U)} : Set U).ncard = 4 := by
    simp [huv, hul, hum, hvl, hvm, hlm]
  change ({u, v, hX.third x.property.1, hX.third x.property.2} : Set U).ncard = 4 at hc
  have hd := Set.ncard_inter_add_ncard_sdiff_eq_ncard (X.neighborSet x)
    (Xᶜ.commonNeighbors u v)
  rw [hX.neighborSet_diff_compl_commonNeighbors huv hnav x, hc,
    ← Set.fintypeCard_eq_ncard (X.neighborSet x), X.card_neighborSet_eq_degree] at hd
  simpa only [Set.inter_comm] using hd

/-- Step 210degreesintoN of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: the neighbours of `y ∈ L` outside `N` are `u` and the common
neighbours of `y,v`. The local edge rules identify the latter with `x` and the `k-1`
vertices of `M` having a different label. -/
theorem neighborSet_diff_compl_commonNeighbors_of_mem_diff {u v y : U}
    (huv : u ≠ v) (hnav : ¬X.Adj u v) (hy : y ∈ X.neighborSet u \ X.neighborSet v) :
    X.neighborSet y \ Xᶜ.commonNeighbors u v = insert u (X.commonNeighbors y v) := by
  have hvthird : X.Adj v (hX.third hy.1) :=
    (hX.adj_neighborPairing_iff huv hnav ⟨y, hy.1⟩).mpr hy.2
  ext z
  simp only [Set.mem_sdiff, Set.mem_insert_iff]
  constructor
  · rintro ⟨hyz, hnN⟩
    by_cases hzu : z = u
    · exact Or.inl hzu
    by_cases hzv : z = v
    · exact False.elim (hy.2 (hzv ▸ hyz.symm))
    right
    refine ⟨hyz, ?_⟩
    by_cases hvz : X.Adj v z
    · exact hvz
    have huz : X.Adj u z := by
      by_contra hnuz
      exact hnN ⟨⟨Ne.symm hzu, hnuz⟩, ⟨Ne.symm hzv, hvz⟩⟩
    have he := hX.common_neighbor_unique hy.1 huz hyz
      (hX.adj_third_left hy.1) (hX.adj_third_right hy.1)
    exact he ▸ hvthird
  · rintro (rfl | hz)
    · exact ⟨hy.1.symm, fun h ↦ h.1.1 rfl⟩
    · exact ⟨hz.1, fun h ↦ h.2.2 hz.2⟩

/-- Step 210degreesintoN of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: a vertex in `L` has `k+1` neighbours outside `N`; the analogous
statement for `M` follows by exchanging the chosen nonadjacent vertices. -/
theorem ncard_neighbors_in_compl_commonNeighbors_add_card [Fintype U] [DecidableRel X.Adj]
    {u v y : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hy : y ∈ X.neighborSet u \ X.neighborSet v) :
    (Xᶜ.commonNeighbors u v ∩ X.neighborSet y).ncard +
      (X.commonNeighbors u v).ncard + 1 = X.degree y := by
  have hvy : v ≠ y := fun he ↦ hnav (he ▸ hy.1)
  have hc₁ := hX.degree_eq_two_mul_card_commonNeighbors huv.symm (fun h ↦ hnav h.symm)
  have hc₂ := hX.degree_eq_two_mul_card_commonNeighbors hvy hy.2
  simp only [Set.fintypeCard_eq_ncard, X.commonNeighbors_symm v u,
    X.commonNeighbors_symm v y] at hc₁ hc₂
  have hc : (X.commonNeighbors y v).ncard = (X.commonNeighbors u v).ncard := by omega
  have hd := Set.ncard_inter_add_ncard_sdiff_eq_ncard (X.neighborSet y)
    (Xᶜ.commonNeighbors u v)
  rw [hX.neighborSet_diff_compl_commonNeighbors_of_mem_diff huv hnav hy,
    Set.ncard_insert_of_notMem (fun h ↦ hnav h.2.symm), hc,
    ← Set.fintypeCard_eq_ncard (X.neighborSet y), X.card_neighborSet_eq_degree] at hd
  simpa only [Set.inter_comm, Nat.add_assoc] using hd

end HasTriangleProperty

/-- The missed-label set `A(w)` in the triangle-property normal-form lemma for
[CGSS, Lemma 2.10], as a finite set of common-neighbour labels. -/
def missedCommonNeighbors [Fintype U] (X : SimpleGraph U) [DecidableRel X.Adj]
    (u v w : U) : Finset (X.commonNeighbors u v) :=
  Finset.univ.filter (fun x ↦ ¬X.Adj w x)

/-- Membership in the missed set of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]. -/
@[simp] theorem mem_missedCommonNeighbors [Fintype U] [DecidableRel X.Adj]
    {u v w : U} (x : X.commonNeighbors u v) :
    x ∈ X.missedCommonNeighbors u v w ↔ ¬X.Adj w x := by
  simp [missedCommonNeighbors]

/-- Degrees in an induced graph, used in steps 210Nedges and 210KNpairing of the
triangle-property normal-form lemma for [CGSS, Lemma 2.10]. -/
theorem degree_induce_eq_ncard (X : SimpleGraph U) [DecidableRel X.Adj]
    (s : Set U) [Fintype s] (w : s) :
    (X.induce s).degree w = (s ∩ X.neighborSet w).ncard := by
  classical
  rw [← card_neighborSet_eq_degree]
  let e : (X.induce s).neighborSet w ≃ ↥(s ∩ X.neighborSet w) :=
    Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (X.Adj w)
  rw [Fintype.card_congr e, Set.fintypeCard_eq_ncard]

/-- Double counting the incidences of two vertex sets, as in steps 210cross and
210degreeSum of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]. -/
theorem sum_ncard_neighbors_inter (X : SimpleGraph U) (s t : Set U)
    [Fintype s] [Fintype t] :
    ∑ x : s, (t ∩ X.neighborSet x).ncard = ∑ y : t, (s ∩ X.neighborSet y).ncard := by
  classical
  have hc (s : Set U) [Fintype s] (v : U) :
      (s ∩ X.neighborSet v).ncard = ∑ y : s, if X.Adj v y then 1 else 0 := by
    rw [← Set.fintypeCard_eq_ncard]
    have he : ↥(s ∩ X.neighborSet v) ≃ {y : s // X.Adj v y} :=
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (X.Adj v)).symm
    rw [Fintype.card_congr he, Fintype.card_subtype]
    simp
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp only [X.adj_comm]

namespace HasTriangleProperty

variable (hX : X.HasTriangleProperty)

include hX

/-- Step 210degreeSum of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: count the edges between `K` and `N` from their `K` ends. -/
theorem sum_ncard_commonNeighbors [Fintype U] [DecidableEq U] [DecidableRel X.Adj]
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y) {u v : U}
    (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    ∑ w : Xᶜ.commonNeighbors u v, (X.commonNeighbors u v ∩ X.neighborSet w).ncard =
      (X.commonNeighbors u v).ncard * (2 * (X.commonNeighbors u v).ncard - 4) := by
  classical
  rw [X.sum_ncard_neighbors_inter (Xᶜ.commonNeighbors u v) (X.commonNeighbors u v)]
  have hc (x : X.commonNeighbors u v) :
      (Xᶜ.commonNeighbors u v ∩ X.neighborSet x).ncard =
        2 * (X.commonNeighbors u v).ncard - 4 := by
    have h := hX.ncard_neighbors_in_compl_commonNeighbors_add_four huv hnav x
    rw [hX.degree_eq_of_not_forall_adj hn x u,
      hX.degree_eq_two_mul_card_commonNeighbors huv hnav, Set.fintypeCard_eq_ncard] at h
    omega
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Set.fintypeCard_eq_ncard]

/-- Step 210signature of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10], in counting form: a vertex of `N` has a total of `k` neighbours
in `K ∪ L`, one in each labelled pair. -/
theorem ncard_neighbors_common_add_diff [Finite U] {u v w : U}
    (huv : u ≠ v) (hnav : ¬X.Adj u v) (hw : w ∈ Xᶜ.commonNeighbors u v) :
    (X.commonNeighbors u v ∩ X.neighborSet w).ncard +
      ((X.neighborSet u \ X.neighborSet v) ∩ X.neighborSet w).ncard =
        (X.commonNeighbors u v).ncard := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let e := hX.commonNeighborsEquiv u v huv hnav
  let e' : ↥(X.commonNeighbors u v \ X.neighborSet w) ≃
      ↥((X.neighborSet u \ X.neighborSet v) ∩ X.neighborSet w) :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X.commonNeighbors u v)
      (fun x ↦ ¬X.Adj w x)).symm |>.trans
        (e.subtypeEquiv (fun x ↦
          (hX.adj_commonNeighborsEquiv_iff_not_adj huv hnav hw.1.1.symm hw.1.2 x).symm))
      |>.trans (Equiv.subtypeSubtypeEquivSubtypeInter
        (· ∈ X.neighborSet u \ X.neighborSet v) (X.Adj w))
  rw [← Set.ncard_congr' e']
  exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _

/-- Steps 210cross and 210cardN of the triangle-property normal-form lemma for
[CGSS, Lemma 2.10]: the complement common-neighbour part has size `3k-5`.
The counting equation is written with addition to avoid truncated subtraction. -/
theorem ncard_compl_commonNeighbors_add_five [Finite U]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    (Xᶜ.commonNeighbors u v).ncard + 5 = 3 * (X.commonNeighbors u v).ncard := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let k := (X.commonNeighbors u v).ncard
  have hk : 2 ≤ k := by
    simpa only [Set.fintypeCard_eq_ncard] using
      hX.two_le_card_commonNeighbors hedge hn huv hnav
  have hL : (X.neighborSet u \ X.neighborSet v).ncard = k :=
    (Set.ncard_congr' (hX.commonNeighborsEquiv u v huv hnav)).symm
  have hsumL :
      ∑ w : Xᶜ.commonNeighbors u v,
        ((X.neighborSet u \ X.neighborSet v) ∩ X.neighborSet w).ncard = k * (k - 1) := by
    rw [X.sum_ncard_neighbors_inter (Xᶜ.commonNeighbors u v)
      (X.neighborSet u \ X.neighborSet v)]
    have hc (y : ↥(X.neighborSet u \ X.neighborSet v)) :
        (Xᶜ.commonNeighbors u v ∩ X.neighborSet y).ncard = k - 1 := by
      have h := hX.ncard_neighbors_in_compl_commonNeighbors_add_card huv hnav y.property
      rw [hX.degree_eq_of_not_forall_adj hn y u,
        hX.degree_eq_two_mul_card_commonNeighbors huv hnav, Set.fintypeCard_eq_ncard] at h
      dsimp [k]
      omega
    simp_rw [hc]
    simp [Set.fintypeCard_eq_ncard, hL]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (w : Xᶜ.commonNeighbors u v) _ ↦ hX.ncard_neighbors_common_add_diff huv hnav w.property)
  rw [Finset.sum_add_distrib, hX.sum_ncard_commonNeighbors hn huv hnav, hsumL] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Set.fintypeCard_eq_ncard] at hs
  change k * (2 * k - 4) + k * (k - 1) = (Xᶜ.commonNeighbors u v).ncard * k at hs
  rw [← Nat.mul_add] at hs
  have he := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) (hs.trans (Nat.mul_comm _ _))
  omega

/-- The partition count in step 210cardN of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]: the six parts give `|V| = 2 + 3k + |N|`. -/
theorem card_eq_two_add_three_mul_add_compl_commonNeighbors [Fintype U]
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    Fintype.card U = 2 + 3 * (X.commonNeighbors u v).ncard +
      (Xᶜ.commonNeighbors u v).ncard := by
  classical
  let D := X.neighborSet u ∪ X.neighborSet v
  have hu : u ∉ D := by
    rintro (ha | ha)
    · exact X.irrefl ha
    · exact hnav ha.symm
  have hv : v ∉ D := by
    rintro (ha | ha)
    · exact hnav ha
    · exact X.irrefl ha
  have hN : (insert u (insert v D))ᶜ = Xᶜ.commonNeighbors u v := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, D, Set.mem_union, mem_neighborSet,
      mem_commonNeighbors, compl_adj]
    tauto
  have hc := Set.ncard_add_ncard_compl (insert u (insert v D))
  rw [Set.ncard_insert_of_notMem (by simpa only [Set.mem_insert_iff, not_or] using ⟨huv, hu⟩),
    Set.ncard_insert_of_notMem hv, hN, Nat.card_eq_fintype_card] at hc
  have hd := Set.ncard_union_add_ncard_inter (X.neighborSet u) (X.neighborSet v)
  change D.ncard + (X.commonNeighbors u v).ncard = _ at hd
  rw [← Set.fintypeCard_eq_ncard (X.neighborSet u),
    ← Set.fintypeCard_eq_ncard (X.neighborSet v), X.card_neighborSet_eq_degree,
    X.card_neighborSet_eq_degree, hX.degree_eq_two_mul_card_commonNeighbors huv hnav,
    hX.degree_eq_two_mul_card_commonNeighbors huv.symm (fun ha ↦ hnav ha.symm)] at hd
  simp only [Set.fintypeCard_eq_ncard, X.commonNeighbors_symm v u] at hd
  omega

/-- Step 210cardN of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the order is `6k-3`, written without natural-number subtraction. -/
theorem card_add_three_eq_six_mul [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    Fintype.card U + 3 = 6 * Fintype.card (X.commonNeighbors u v) := by
  have h₁ := hX.card_eq_two_add_three_mul_add_compl_commonNeighbors huv hnav
  have h₂ := hX.ncard_compl_commonNeighbors_add_five hedge hn huv hnav
  rw [Set.fintypeCard_eq_ncard]
  omega

/-- Step 210counts of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
all four strongly regular parameters, with `k` the common-neighbour count of any nonedge. -/
theorem isSRGWith_of_not_forall_adj [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    X.IsSRGWith (6 * Fintype.card (X.commonNeighbors u v) - 3)
      (2 * Fintype.card (X.commonNeighbors u v)) 1 (Fintype.card (X.commonNeighbors u v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hX.card_add_three_eq_six_mul hedge hn huv hnav
    omega
  · intro w
    rw [hX.degree_eq_of_not_forall_adj hn w u,
      hX.degree_eq_two_mul_card_commonNeighbors huv hnav]
  · intro x y hxy
    obtain ⟨z, hz, huniq⟩ := hX.existsUnique_common_neighbor hxy
    have he : X.commonNeighbors x y = {z} := by
      ext w
      exact ⟨fun hw ↦ huniq w hw, fun hw ↦ hw ▸ hz⟩
    simp only [Set.fintypeCard_eq_ncard, he, Set.ncard_singleton]
  · intro x y hxy hna
    have h₁ := hX.degree_eq_two_mul_card_commonNeighbors hxy hna
    have h₂ := hX.degree_eq_two_mul_card_commonNeighbors huv hnav
    have h₃ := hX.degree_eq_of_not_forall_adj hn x u
    omega

/-- Step 210dK of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
`d_K(w)` is `k` or `k-2`, with the second case written using addition. -/
theorem ncard_commonNeighbors_inter_eq_or_add_two [Finite U]
    {u v w : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hw : w ∈ Xᶜ.commonNeighbors u v) :
    (X.commonNeighbors u v ∩ X.neighborSet w).ncard = (X.commonNeighbors u v).ncard ∨
      (X.commonNeighbors u v ∩ X.neighborSet w).ncard + 2 =
        (X.commonNeighbors u v).ncard := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have ha := hX.card_non_neighbors_eq_zero_or_two huv hnav hw
  let e : {x : X.commonNeighbors u v // ¬X.Adj w x} ≃
      ↥(X.commonNeighbors u v \ X.neighborSet w) :=
    Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X.commonNeighbors u v) (fun x ↦ ¬X.Adj w x)
  rw [Fintype.card_congr e, Set.fintypeCard_eq_ncard] at ha
  have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard (X.commonNeighbors u v) (X.neighborSet w)
  omega

/-- Step 210KNpairing of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the degree within `N` is exactly `d_K(w)`. -/
theorem ncard_compl_commonNeighbors_inter_eq [Finite U] {u v w : U}
    (hw : w ∈ Xᶜ.commonNeighbors u v) :
    (Xᶜ.commonNeighbors u v ∩ X.neighborSet w).ncard =
      (X.commonNeighbors u v ∩ X.neighborSet w).ncard :=
  (Set.ncard_congr' (hX.commonNeighborsPairing hw)).symm

/-- Step 210highcount of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
twice the number of vertices with `d_K = k` is `(k-2)(5-k)` in the integers. -/
theorem two_mul_card_high_commonNeighbors [Fintype U] [DecidableEq U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    (2 : ℤ) * Fintype.card {w : Xᶜ.commonNeighbors u v //
        (X.commonNeighbors u v ∩ X.neighborSet w).ncard = (X.commonNeighbors u v).ncard} =
      ((X.commonNeighbors u v).ncard - 2 : ℤ) * (5 - (X.commonNeighbors u v).ncard) := by
  classical
  let k := (X.commonNeighbors u v).ncard
  let d (w : Xᶜ.commonNeighbors u v) := (X.commonNeighbors u v ∩ X.neighborSet w).ncard
  have hk : 2 ≤ k := by
    simpa only [Set.fintypeCard_eq_ncard] using
      hX.two_le_card_commonNeighbors hedge hn huv hnav
  have hpoint (w : Xᶜ.commonNeighbors u v) : d w + 2 = k + if d w = k then 2 else 0 := by
    have h := hX.ncard_commonNeighbors_inter_eq_or_add_two huv hnav w.property
    change d w = k ∨ d w + 2 = k at h
    split_ifs <;> omega
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun w _ ↦ hpoint w)
  have hsum := hX.sum_ncard_commonNeighbors hn huv hnav
  have hN := hX.ncard_compl_commonNeighbors_add_five hedge hn huv hnav
  have hh : (∑ w : Xᶜ.commonNeighbors u v, if d w = k then 2 else 0) =
      2 * Fintype.card {w : Xᶜ.commonNeighbors u v // d w = k} := by
    rw [Fintype.card_subtype]
    simp [Finset.sum_ite, Nat.mul_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  rw [hh] at hs
  change (∑ w : Xᶜ.commonNeighbors u v, d w) = k * (2 * k - 4) at hsum
  rw [hsum] at hs
  simp only [Set.fintypeCard_eq_ncard] at hs
  have hsub' : 2 * k - 4 + 4 = 2 * k := by omega
  have hs' := congrArg (fun n : ℕ ↦ (n : ℤ)) hs
  have hN' := congrArg (fun n : ℕ ↦ (n : ℤ)) hN
  have hsub'' := congrArg (fun n : ℕ ↦ (n : ℤ)) hsub'
  push_cast at hs' hN' hsub''
  change (2 : ℤ) * Fintype.card {w : Xᶜ.commonNeighbors u v // d w = k} =
    (k - 2 : ℤ) * (5 - k)
  dsimp only [k] at *
  nlinarith

/-- Step 210combbound of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
nonnegativity of the high-degree count gives the purely combinatorial upper bound `k ≤ 5`. -/
theorem card_commonNeighbors_le_five [Finite U]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    (X.commonNeighbors u v).ncard ≤ 5 := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have hh := hX.two_mul_card_high_commonNeighbors hedge hn huv hnav
  by_contra hlt
  have hp : (0 : ℤ) < (X.commonNeighbors u v).ncard - 2 := by omega
  have hm : (5 : ℤ) - (X.commonNeighbors u v).ncard < 0 := by omega
  have hnegative := mul_neg_of_pos_of_neg hp hm
  omega

/-- Step 210highforces of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
if one vertex of `N` sees all of `K`, then `k = 3`. -/
theorem ncard_commonNeighbors_eq_three_of_high [Finite U]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v w : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hw : w ∈ Xᶜ.commonNeighbors u v)
    (hd : (X.commonNeighbors u v ∩ X.neighborSet w).ncard = (X.commonNeighbors u v).ncard) :
    (X.commonNeighbors u v).ncard = 3 := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have hk : 2 ≤ (X.commonNeighbors u v).ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using
      hX.two_le_card_commonNeighbors hedge hn huv hnav
  have hall : ∀ x ∈ X.commonNeighbors u v, X.Adj w x := by
    have he : X.commonNeighbors u v ∩ X.neighborSet w = X.commonNeighbors u v :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left hd.ge
    intro x hx
    have hx' : x ∈ X.commonNeighbors u v ∩ X.neighborSet w := by rw [he]; exact hx
    exact hx'.2
  -- ⟨3⟩1 (210choosez).
  have hpos : 0 < (Xᶜ.commonNeighbors u v ∩ X.neighborSet w).ncard := by
    rw [hX.ncard_compl_commonNeighbors_inter_eq hw, hd]
    omega
  obtain ⟨z, hz, hwz⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  let t := hX.third hwz
  have ht : t ∈ X.commonNeighbors u v := hX.third_mem_commonNeighbors hw hz hwz
  -- ⟨3⟩2 (210zone).
  have he : X.commonNeighbors u v ∩ X.neighborSet z = {t} := by
    ext x
    constructor
    · rintro ⟨hxK, hzx⟩
      exact hX.common_neighbor_unique hwz (hall x hxK) hzx
        (hX.adj_third_left hwz) (hX.adj_third_right hwz)
    · intro hx
      exact hx ▸ ⟨ht, hX.adj_third_right hwz⟩
  have hd' := hX.ncard_commonNeighbors_inter_eq_or_add_two huv hnav hz
  rw [he, Set.ncard_singleton] at hd'
  omega

/-- Step 210exclude of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the only possible common-neighbour counts of a nonedge are `2`, `3` and `5`. -/
theorem card_commonNeighbors_mem [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    Fintype.card (X.commonNeighbors u v) ∈ ({2, 3, 5} : Set ℕ) := by
  classical
  have hlo := hX.two_le_card_commonNeighbors hedge hn huv hnav
  have hhi := hX.card_commonNeighbors_le_five hedge hn huv hnav
  rw [Set.fintypeCard_eq_ncard] at hlo ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hout
  have hk : (X.commonNeighbors u v).ncard = 4 := by omega
  have hh := hX.two_mul_card_high_commonNeighbors hedge hn huv hnav
  have hp : 0 < Fintype.card {w : Xᶜ.commonNeighbors u v //
      (X.commonNeighbors u v ∩ X.neighborSet w).ncard = (X.commonNeighbors u v).ncard} := by
    have he : ((X.commonNeighbors u v).ncard - 2 : ℤ) *
        (5 - (X.commonNeighbors u v).ncard) = 2 := by norm_num [hk]
    rw [he] at hh
    omega
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp hp
  have hk' := hX.ncard_commonNeighbors_eq_three_of_high hedge hn huv hnav w.property hw
  omega

/-- Step 210edgeLM of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the third vertex on an edge between different labels of `L,M` lies in `N`. -/
theorem third_commonNeighborsEquiv_mem_compl_commonNeighbors {u v : U}
    (huv : u ≠ v) (hnav : ¬X.Adj u v) (x y : X.commonNeighbors u v) (hxy : x ≠ y) :
    hX.third ((hX.adj_commonNeighborsEquiv_comm_iff huv hnav x y).mpr hxy) ∈
      Xᶜ.commonNeighbors u v := by
  let l := hX.commonNeighborsEquiv u v huv hnav x
  let m := hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
    ⟨y, y.property.2, y.property.1⟩
  have hlm : X.Adj l m := (hX.adj_commonNeighborsEquiv_comm_iff huv hnav x y).mpr hxy
  let w := hX.third hlm
  have hlw : X.Adj l w := hX.adj_third_left hlm
  have hmw : X.Adj m w := hX.adj_third_right hlm
  have hum : u ≠ (m : U) := fun he ↦ hnav (he ▸ m.property.1.symm)
  have hvl : v ≠ (l : U) := fun he ↦ hnav (he ▸ l.property.1)
  have huw : u ≠ w := fun he ↦
    m.property.2 (Eq.mpr (congrArg (fun t ↦ X.Adj t (m : U)) he) hmw.symm)
  have hvw : v ≠ w := fun he ↦
    l.property.2 (Eq.mpr (congrArg (fun t ↦ X.Adj t (l : U)) he) hlw.symm)
  -- 210noCore: the outside-vertex rule excludes adjacency to both `u` and `v`.
  have hu := hX.outside hlm hlw hmw l.property.1.ne hum huw
  have hv := hX.outside hlm hlw hmw hvl m.property.1.ne hvw
  have hul : X.Adj u l := l.property.1
  have hvm : X.Adj v m := m.property.1
  have hnuw : ¬X.Adj u w := by rcases hu with h | h | h <;> tauto
  have hnvw : ¬X.Adj v w := by rcases hv with h | h | h <;> tauto
  exact ⟨⟨huw, hnuw⟩, ⟨hvw, hnvw⟩⟩

/-- Steps 210pairlabel, 210labelvalue and 210labelunique of the triangle-property
normal-form lemma for [CGSS, Lemma 2.10]: each pair of labels is missed by exactly one
vertex of `N`. This part does not require the restriction `k = 5`. -/
theorem existsUnique_pair_label {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (x y : X.commonNeighbors u v) (hxy : x ≠ y) :
    ∃! w : Xᶜ.commonNeighbors u v, ∀ t : X.commonNeighbors u v,
      ¬X.Adj w t ↔ t = x ∨ t = y := by
  let l := hX.commonNeighborsEquiv u v huv hnav x
  let m := hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm)
    ⟨y, y.property.2, y.property.1⟩
  have hlm : X.Adj l m := (hX.adj_commonNeighborsEquiv_comm_iff huv hnav x y).mpr hxy
  let w : Xᶜ.commonNeighbors u v :=
    ⟨hX.third hlm, hX.third_commonNeighborsEquiv_mem_compl_commonNeighbors huv hnav x y hxy⟩
  have hx : ¬X.Adj w x :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv hnav w.property.1.1.symm
      w.property.1.2 x).mp (hX.adj_third_left hlm).symm
  have hy : ¬X.Adj w y :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv.symm (fun h ↦ hnav h.symm)
      w.property.2.1.symm w.property.2.2 ⟨y, y.property.2, y.property.1⟩).mp
        (hX.adj_third_right hlm).symm
  have hall : ∀ t : X.commonNeighbors u v, ¬X.Adj w t ↔ t = x ∨ t = y := by
    obtain ⟨z, _, hz⟩ := hX.existsUnique_other_non_neighbor huv hnav w.property x hx
    intro t
    constructor
    · intro ht
      by_cases htx : t = x
      · exact Or.inl htx
      · exact Or.inr ((hz t ⟨htx, ht⟩).trans (hz y ⟨hxy.symm, hy⟩).symm)
    · rintro (rfl | rfl)
      · exact hx
      · exact hy
  refine ⟨w, hall, ?_⟩
  intro z hz
  have hzl : X.Adj z l :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv hnav z.property.1.1.symm
      z.property.1.2 x).mpr ((hz x).mpr (Or.inl rfl))
  have hzm : X.Adj z m :=
    (hX.adj_commonNeighborsEquiv_iff_not_adj huv.symm (fun h ↦ hnav h.symm)
      z.property.2.1.symm z.property.2.2 ⟨y, y.property.2, y.property.1⟩).mpr
        ((hz y).mpr (Or.inr rfl))
  exact Subtype.ext (hX.common_neighbor_unique hlm hzl.symm hzm.symm
    (hX.adj_third_left hlm) (hX.adj_third_right hlm))

/-- Step 210Kpairs of `lem:triangle-normal-form` ([CGSS, Lemma 2.10]): for each
`x ∈ K`, exactly `k-2` edges in `N` have third vertex `x`. Their endpoints are precisely
the `N` neighbours of `x`, and triangle partners pair all these neighbours. -/
theorem card_edgeFinset_induce_common_neighbor_compl [Fintype U] [DecidableEq U]
    [DecidableRel X.Adj]
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y) {u v : U} (huv : u ≠ v)
    (hnav : ¬X.Adj u v) (x : X.commonNeighbors u v) :
    (X.induce (Xᶜ.commonNeighbors u v ∩ X.neighborSet x)).edgeFinset.card =
      (X.commonNeighbors u v).ncard - 2 := by
  let T := Xᶜ.commonNeighbors u v ∩ X.neighborSet x
  have hdeg (w : T) : (X.induce T).degree w = 1 := by
    rw [X.degree_induce_eq_ncard]
    have hzN := hX.third_mem_compl_commonNeighbors w.property.1 x.property w.property.2.symm
    have hz : hX.third w.property.2.symm = hX.third w.property.2 :=
      hX.common_neighbor_unique w.property.2.symm
        (hX.adj_third_left _) (hX.adj_third_right _)
        (hX.adj_third_right _) (hX.adj_third_left _)
    rw [hz] at hzN
    apply Set.ncard_eq_one.mpr
    refine ⟨hX.third w.property.2, ?_⟩
    ext z
    constructor
    · intro hz
      exact Set.mem_singleton_iff.mpr (hX.common_neighbor_unique w.property.2
        hz.1.2 hz.2 (hX.adj_third_left _) (hX.adj_third_right _))
    · rintro rfl
      exact ⟨⟨hzN, hX.adj_third_left _⟩, hX.adj_third_right _⟩
  have he := (X.induce T).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at he
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Set.fintypeCard_eq_ncard] at he
  have hd := hX.ncard_neighbors_in_compl_commonNeighbors_add_four huv hnav x
  rw [hX.degree_eq_of_not_forall_adj hn x u,
    hX.degree_eq_two_mul_card_commonNeighbors huv hnav, Set.fintypeCard_eq_ncard] at hd
  change T.ncard + 4 = 2 * (X.commonNeighbors u v).ncard at hd
  change (X.induce T).edgeFinset.card = _
  omega

/-- Step 210Nedges of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
the induced graph on `N` has `k(k-2)` edges. Its third-vertex assertion is
`third_mem_commonNeighbors`; `commonNeighborsPairing` supplies the triangle pairs. -/
theorem card_edgeFinset_induce_compl_commonNeighbors [Fintype U] [DecidableEq U]
    [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    (X.induce (Xᶜ.commonNeighbors u v)).edgeFinset.card =
      (X.commonNeighbors u v).ncard * ((X.commonNeighbors u v).ncard - 2) := by
  have hk : 2 ≤ (X.commonNeighbors u v).ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using
      hX.two_le_card_commonNeighbors hedge hn huv hnav
  have h := (X.induce (Xᶜ.commonNeighbors u v)).sum_degrees_eq_twice_card_edges
  simp_rw [X.degree_induce_eq_ncard] at h
  have hdeg (w : Xᶜ.commonNeighbors u v) := hX.ncard_compl_commonNeighbors_inter_eq w.property
  simp_rw [hdeg] at h
  rw [hX.sum_ncard_commonNeighbors hn huv hnav] at h
  have he : 2 * (X.commonNeighbors u v).ncard - 4 =
      2 * ((X.commonNeighbors u v).ncard - 2) := by omega
  rw [he, ← Nat.mul_assoc, Nat.mul_comm (X.commonNeighbors u v).ncard 2,
    Nat.mul_assoc] at h
  omega

/-- Step 210pairsizes of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
unless `k = 3`, every vertex of `N` misses exactly two labels. -/
theorem card_missedCommonNeighbors_eq_two [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hk : (X.commonNeighbors u v).ncard ≠ 3) (w : Xᶜ.commonNeighbors u v) :
    (X.missedCommonNeighbors u v w).card = 2 := by
  have ha := hX.card_non_neighbors_eq_zero_or_two huv hnav w.property
  rw [Fintype.card_subtype] at ha
  change (X.missedCommonNeighbors u v w).card = 0 ∨
    (X.missedCommonNeighbors u v w).card = 2 at ha
  rcases ha with ha | ha
  · have hall : X.commonNeighbors u v ∩ X.neighborSet w = X.commonNeighbors u v := by
      ext x
      constructor
      · exact And.left
      · intro hx
        refine ⟨hx, ?_⟩
        by_contra hnwx
        have hmem := (X.mem_missedCommonNeighbors ⟨x, hx⟩).mpr hnwx
        rw [Finset.card_eq_zero.mp ha] at hmem
        exact Finset.notMem_empty _ hmem
    exact False.elim (hk (hX.ncard_commonNeighbors_eq_three_of_high hedge hn huv hnav
      w.property (congrArg Set.ncard hall)))
  · exact ha

/-- Steps 210pairlabel and 210labelunique of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]: for `k ≠ 3`, the missed sets biject `N` with the two-subsets of `K`. -/
theorem exists_pair_label_equiv [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) (hk : (X.commonNeighbors u v).ncard ≠ 3) :
    ∃ e : Xᶜ.commonNeighbors u v ≃ {s : Finset (X.commonNeighbors u v) // s.card = 2},
      ∀ w, (e w).val = X.missedCommonNeighbors u v w := by
  classical
  let f (w : Xᶜ.commonNeighbors u v) : {s : Finset (X.commonNeighbors u v) // s.card = 2} :=
    ⟨X.missedCommonNeighbors u v w,
      hX.card_missedCommonNeighbors_eq_two hedge hn huv hnav hk w⟩
  have hf : Function.Bijective f := by
    constructor
    · intro w z he
      obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp (f w).property
      change X.missedCommonNeighbors u v w = {x, y} at hpair
      have he' : X.missedCommonNeighbors u v w = X.missedCommonNeighbors u v z :=
        congrArg Subtype.val he
      apply (hX.existsUnique_pair_label huv hnav x y hxy).unique
      · intro t
        rw [← X.mem_missedCommonNeighbors, hpair]
        simp
      · intro t
        rw [← X.mem_missedCommonNeighbors, ← he', hpair]
        simp
    · intro s
      obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp s.property
      obtain ⟨w, hw, _⟩ := hX.existsUnique_pair_label huv hnav x y hxy
      refine ⟨w, Subtype.ext ?_⟩
      change X.missedCommonNeighbors u v w = s.val
      rw [hs]
      ext t
      simpa only [mem_missedCommonNeighbors, Finset.mem_insert, Finset.mem_singleton] using hw t
  exact ⟨Equiv.ofBijective f hf, fun _ ↦ rfl⟩

/-- Step 210adjdisjoint of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
adjacent vertices of `N` have disjoint missed sets. -/
theorem disjoint_missedCommonNeighbors_of_adj [Fintype U] [DecidableRel X.Adj]
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) (w z : Xᶜ.commonNeighbors u v)
    (hwz : X.Adj w z) :
    Disjoint (X.missedCommonNeighbors u v w) (X.missedCommonNeighbors u v z) := by
  rw [Finset.disjoint_left]
  intro x hxw hxz
  rw [X.mem_missedCommonNeighbors] at hxw hxz
  have hwx : (w : U) ≠ x := fun he ↦
    w.property.1.2 (Eq.mpr (congrArg (X.Adj u) he) x.property.1)
  have hxt : X.Adj x (hX.third hwz) :=
    (hX.adj_neighborPairing_iff hwx hxw ⟨z, hwz⟩).mpr (fun ha ↦ hxz ha.symm)
  have ht := hX.third_mem_commonNeighbors w.property z.property hwz
  exact hX.not_adj_of_same_adjacency huv hnav ⟨x, x.property.1⟩
    ⟨hX.third hwz, ht.1⟩ (iff_of_true x.property.2 ht.2) hxt

/-- Steps 210threechoices and 210disjoint of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]: when `k = 5`, adjacency in `N` is disjointness of the pair labels. -/
theorem adj_iff_disjoint_missedCommonNeighbors_of_five [Fintype U] [DecidableRel X.Adj]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v)
    (hk : (X.commonNeighbors u v).ncard = 5) (w z : Xᶜ.commonNeighbors u v) :
    X.Adj w z ↔ Disjoint (X.missedCommonNeighbors u v w) (X.missedCommonNeighbors u v z) := by
  classical
  have hkne : (X.commonNeighbors u v).ncard ≠ 3 := by omega
  obtain ⟨e, he⟩ := hX.exists_pair_label_equiv hedge hn huv hnav hkne
  let A := X.missedCommonNeighbors u v w
  have hA : A.card = 2 := hX.card_missedCommonNeighbors_eq_two hedge hn huv hnav hkne w
  have hcount : Fintype.card {t : Xᶜ.commonNeighbors u v //
      Disjoint A (X.missedCommonNeighbors u v t)} = 3 := by
    let e₁ : {t : Xᶜ.commonNeighbors u v // Disjoint A (X.missedCommonNeighbors u v t)} ≃
        {s : {s : Finset (X.commonNeighbors u v) // s.card = 2} // Disjoint A s.val} :=
      e.subtypeEquiv (fun t ↦ by rw [he t])
    let e₂ : {s : {s : Finset (X.commonNeighbors u v) // s.card = 2} // Disjoint A s.val} ≃
        ↥((Finset.univ \ A).powersetCard 2) :=
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun s : Finset (X.commonNeighbors u v) ↦ s.card = 2)
        (Disjoint A)).trans (Equiv.subtypeEquivRight (fun s ↦ by
          simp only [Finset.mem_powersetCard, Finset.subset_sdiff,
            Finset.subset_univ, true_and]
          exact ⟨fun h ↦ ⟨h.2.symm, h.1⟩, fun h ↦ ⟨h.2, h.1.symm⟩⟩))
    rw [Fintype.card_congr (e₁.trans e₂), Fintype.card_coe, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Set.fintypeCard_eq_ncard, hk, hA]
    decide
  have hdegree : (X.induce (Xᶜ.commonNeighbors u v)).degree w = 3 := by
    rw [X.degree_induce_eq_ncard, hX.ncard_compl_commonNeighbors_inter_eq w.property]
    rcases hX.ncard_commonNeighbors_inter_eq_or_add_two huv hnav w.property with hd | hd
    · exact False.elim (hkne (hX.ncard_commonNeighbors_eq_three_of_high hedge hn huv hnav
        w.property hd))
    · omega
  have hsub : (X.induce (Xᶜ.commonNeighbors u v)).neighborSet w ⊆
      {t : Xᶜ.commonNeighbors u v | Disjoint A (X.missedCommonNeighbors u v t)} :=
    fun t ht ↦ hX.disjoint_missedCommonNeighbors_of_adj huv hnav w t ht
  have hcount' : {t : Xᶜ.commonNeighbors u v |
      Disjoint A (X.missedCommonNeighbors u v t)}.ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard]
    exact (Fintype.card_congr (Equiv.refl _)).trans hcount
  have hEq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [hcount', ← Set.fintypeCard_eq_ncard, card_neighborSet_eq_degree, hdegree])
  exact Set.ext_iff.mp hEq z

/-- Steps 210two and 210twoN of the triangle-property normal-form lemma for [CGSS, Lemma 2.10]:
when `k = 2`, `N` is a singleton, whose vertex misses all of `K`. -/
theorem singleton_compl_commonNeighbors_of_two [Finite U]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) (hk : (X.commonNeighbors u v).ncard = 2) :
    ∃ w : Xᶜ.commonNeighbors u v,
      (∀ z : Xᶜ.commonNeighbors u v, z = w) ∧ ∀ x : X.commonNeighbors u v, ¬X.Adj w x := by
  classical
  let : Fintype U := Fintype.ofFinite U
  have hN := hX.ncard_compl_commonNeighbors_add_five hedge hn huv hnav
  have hc : (Xᶜ.commonNeighbors u v).ncard = 1 := by omega
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hc
  have hwmem : w ∈ Xᶜ.commonNeighbors u v := by rw [hw]; exact Set.mem_singleton _
  refine ⟨⟨w, hwmem⟩, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    simpa only [hw, Set.mem_singleton_iff] using z.property
  · intro x hx
    have hp := hX.third_mem_compl_commonNeighbors hwmem x.property hx
    rw [hw, Set.mem_singleton_iff] at hp
    exact (hX.adj_third_left hx).ne hp.symm

/-- Steps 210centre, 210claw and 210leaflabels of the triangle-property normal-form lemma
for [CGSS, Lemma 2.10]: when `k = 3`, `N` is a claw. Its centre sees all of `K`, and its
leaves are bijectively labelled by their unique neighbour in `K`. -/
theorem claw_compl_commonNeighbors_of_three [Finite U]
    (hedge : ∃ x y, X.Adj x y) (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y)
    {u v : U} (huv : u ≠ v) (hnav : ¬X.Adj u v) (hk : (X.commonNeighbors u v).ncard = 3) :
    ∃ w₀ : Xᶜ.commonNeighbors u v,
      ∃ e : X.commonNeighbors u v ≃ {w : Xᶜ.commonNeighbors u v // w ≠ w₀},
        (∀ x : X.commonNeighbors u v, X.Adj w₀ x) ∧
        (∀ x y : X.commonNeighbors u v, X.Adj (e x).val y ↔ x = y) ∧
        ∀ w z : Xᶜ.commonNeighbors u v, X.Adj w z ↔ w ≠ z ∧ (w = w₀ ∨ z = w₀) := by
  classical
  let : Fintype U := Fintype.ofFinite U
  -- ⟨2⟩1 (210centre).
  have hh := hX.two_mul_card_high_commonNeighbors hedge hn huv hnav
  have he : ((X.commonNeighbors u v).ncard - 2 : ℤ) *
      (5 - (X.commonNeighbors u v).ncard) = 2 := by norm_num [hk]
  rw [he] at hh
  have hp : 0 < Fintype.card {w : Xᶜ.commonNeighbors u v //
      (X.commonNeighbors u v ∩ X.neighborSet w).ncard = (X.commonNeighbors u v).ncard} := by omega
  obtain ⟨⟨w₀, hw₀⟩⟩ := Fintype.card_pos_iff.mp hp
  have hall (x : X.commonNeighbors u v) : X.Adj w₀ x := by
    have heq : X.commonNeighbors u v ∩ X.neighborSet w₀ = X.commonNeighbors u v :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left hw₀.ge
    have hx : (x : U) ∈ X.commonNeighbors u v ∩ X.neighborSet w₀ := by
      rw [heq]
      exact x.property
    exact hx.2
  have hN := hX.ncard_compl_commonNeighbors_add_five hedge hn huv hnav
  have hNcard : Fintype.card (Xᶜ.commonNeighbors u v) = 4 := by
    rw [Set.fintypeCard_eq_ncard]
    omega
  -- ⟨2⟩2 (210claw).
  have huniv : (X.induce (Xᶜ.commonNeighbors u v)).IsUniversal w₀ := by
    apply (degree_eq_card_sub_one _ w₀).mp
    rw [X.degree_induce_eq_ncard, hX.ncard_compl_commonNeighbors_inter_eq w₀.property,
      hw₀, hk, hNcard]
  -- ⟨2⟩3 (210leaflabels): triangle partners give the leaf bijection.
  let e : X.commonNeighbors u v ≃ {w : Xᶜ.commonNeighbors u v // w ≠ w₀} :=
    { toFun := fun x ↦ ⟨⟨hX.third (hall x),
        hX.third_mem_compl_commonNeighbors w₀.property x.property (hall x)⟩,
        fun heq ↦ (hX.adj_third_left (hall x)).ne
          (congrArg (fun t : Xᶜ.commonNeighbors u v ↦ (t : U)) heq).symm⟩
      invFun := fun z ↦ ⟨hX.third (huniv z.property.symm),
        hX.third_mem_commonNeighbors w₀.property z.val.property (huniv z.property.symm)⟩
      left_inv := fun x ↦ Subtype.ext (hX.third_third (hall x))
      right_inv := fun z ↦ Subtype.ext (Subtype.ext (hX.third_third (huniv z.property.symm))) }
  refine ⟨w₀, e, hall, ?_, ?_⟩
  · intro x y
    constructor
    · intro h
      exact Subtype.ext (hX.common_neighbor_unique (hX.adj_third_left (hall x))
        (hall x) (hX.adj_third_right (hall x)).symm (hall y) h)
    · rintro rfl
      exact (hX.adj_third_right (hall x)).symm
  · intro w z
    constructor
    · intro hwz
      refine ⟨fun heq ↦ hwz.ne (congrArg Subtype.val heq), ?_⟩
      by_contra hncenter
      have hw : w₀ ≠ w := fun heq ↦ hncenter (Or.inl heq.symm)
      have hz : w₀ ≠ z := fun heq ↦ hncenter (Or.inr heq.symm)
      have ht := hX.third_mem_commonNeighbors w.property z.property hwz
      have heq : (w₀ : U) = hX.third hwz := hX.common_neighbor_unique hwz
        (huniv hw).symm (huniv hz).symm (hX.adj_third_left hwz) (hX.adj_third_right hwz)
      exact w₀.property.1.2 (Eq.mpr (congrArg (X.Adj u) heq) ht.1)
    · rintro ⟨hneq, rfl | rfl⟩
      · exact huniv hneq
      · exact (huniv hneq.symm).symm

section NormalForm

variable [Fintype U] [DecidableEq U] [DecidableRel X.Adj] (u v : U)

local notation "K" => X.commonNeighbors u v
local notation "L" => X.neighborSet u \ X.neighborSet v
local notation "M" => X.neighborSet v \ X.neighborSet u
local notation "N" => commonNeighbors (Xᶜ) u v

/-- The complete conclusion of `lem:triangle-normal-form`, the graph lemma used in
[CGSS, Lemma 2.10]. The labels of `L,M` are `commonNeighborsEquiv` (with the endpoints
exchanged for `M`); by definition they are the third vertices on the corresponding edges.
The four Mathlib sets `K,L,M,N` in the blueprint are expanded in the fields below. -/
structure NormalForm : Prop where
  /-- The distinguished vertices are distinct. -/
  ne : u ≠ v
  /-- The distinguished vertices are nonadjacent. -/
  not_adj : ¬X.Adj u v
  /-- Part 1: the three possible common-neighbour parameters. -/
  card_common : Fintype.card K ∈ ({2, 3, 5} : Set ℕ)
  /-- Part 1: order, regularity, and all four strongly regular parameters (errata Error 12). -/
  isSRGWith : X.IsSRGWith (6 * Fintype.card K - 3) (2 * Fintype.card K) 1 (Fintype.card K)
  /-- Part 2: disjointness of the six parts. -/
  disjoint : List.Pairwise Disjoint ([{u}, {v}, K, L, M, N] : List (Set U))
  /-- Part 2: the parts cover all vertices. -/
  cover : {u, v} ∪ K ∪ L ∪ M ∪ N = Set.univ
  /-- Part 2: `|L| = k`. -/
  card_left : (L).ncard = (K).ncard
  /-- Part 2: `|M| = k`. -/
  card_right : (M).ncard = (K).ncard
  /-- Part 2: `|N| = 3k-5`. -/
  card_remainder : (N).ncard = 3 * (K).ncard - 5
  /-- Part 3: the three core parts are independent. -/
  independent : X.IsIndepSet K ∧ X.IsIndepSet L ∧ X.IsIndepSet M
  /-- Part 3: the matching from `K` to `L`. -/
  common_left : ∀ x y : K,
    X.Adj x (hX.commonNeighborsEquiv u v ne not_adj y) ↔ x = y
  /-- Part 3: the matching from `K` to `M`. -/
  common_right : ∀ x y : K,
    X.Adj x (hX.commonNeighborsEquiv v u ne.symm (fun h ↦ not_adj h.symm)
      ⟨y, y.property.2, y.property.1⟩) ↔ x = y
  /-- Part 3: the edges between `L` and `M` join unequal labels. -/
  left_right : ∀ x y : K,
    X.Adj (hX.commonNeighborsEquiv u v ne not_adj x)
      (hX.commonNeighborsEquiv v u ne.symm (fun h ↦ not_adj h.symm)
        ⟨y, y.property.2, y.property.1⟩) ↔ x ≠ y
  /-- Part 4: a missed set has zero or two elements. -/
  missed_card : ∀ w : N,
    (X.missedCommonNeighbors u v w).card = 0 ∨ (X.missedCommonNeighbors u v w).card = 2
  /-- Part 4: both degrees equal `d_K`, whose two values are `k` and `k-2`. -/
  degrees : ∀ w : N,
    ((K ∩ X.neighborSet w).ncard = (K).ncard ∨
      (K ∩ X.neighborSet w).ncard = (K).ncard - 2) ∧
    (N ∩ X.neighborSet w).ncard = (K ∩ X.neighborSet w).ncard
  /-- Part 4: incidence from `N` to `L` is membership in the missed set. -/
  remainder_left : ∀ (w : N) (x : K),
    X.Adj w (hX.commonNeighborsEquiv u v ne not_adj x) ↔
      x ∈ X.missedCommonNeighbors u v w
  /-- Part 4: incidence from `N` to `M` is membership in the missed set. -/
  remainder_right : ∀ (w : N) (x : K),
    X.Adj w (hX.commonNeighborsEquiv v u ne.symm (fun h ↦ not_adj h.symm)
      ⟨x, x.property.2, x.property.1⟩) ↔ x ∈ X.missedCommonNeighbors u v w
  /-- Part 5: the edge count in `N`. -/
  remainder_edges : (X.induce N).edgeFinset.card = (K).ncard * ((K).ncard - 2)
  /-- Part 5: each edge in `N` has its third vertex in `K`. -/
  remainder_third : ∀ (w z : N) (hwz : X.Adj w z), hX.third hwz ∈ K
  /-- Part 5: the degree sum from `N` to `K`. -/
  degree_sum : ∑ w : N, (K ∩ X.neighborSet w).ncard = (K).ncard * (2 * (K).ncard - 4)
  /-- Part 5: the integer identity for the number of high-degree vertices. -/
  high_count : (2 : ℤ) * Fintype.card {w : N // (K ∩ X.neighborSet w).ncard = (K).ncard} =
    ((K).ncard - 2 : ℤ) * (5 - (K).ncard)
  /-- Part 6: the singleton form when `k = 2`. -/
  two : (K).ncard = 2 → ∃ w : N, (∀ z : N, z = w) ∧ ∀ x : K, ¬X.Adj w x
  /-- Part 7: the labelled claw when `k = 3`. -/
  three : (K).ncard = 3 → ∃ w₀ : N, ∃ e : K ≃ {w : N // w ≠ w₀},
    (∀ x : K, X.Adj w₀ x) ∧ (∀ x y : K, X.Adj (e x).val y ↔ x = y) ∧
    ∀ w z : N, X.Adj w z ↔ w ≠ z ∧ (w = w₀ ∨ z = w₀)
  /-- Part 8 (210five): the two-subset form when `k = 5`. -/
  five : (K).ncard = 5 → ∃ e : N ≃ {s : Finset K // s.card = 2},
    (∀ w, (e w).val = X.missedCommonNeighbors u v w) ∧
    ∀ w z : N, X.Adj w z ↔ Disjoint (e w).val (e z).val

variable {u v}

-- Lemma 2.10 (triangle-property normal form)
/-- The triangle-property normal-form lemma (`lem:triangle-normal-form`, used in
[CGSS, Lemma 2.10]): every nonedge has the partition, counts, edge rules, and one of the
three labelled normal forms recorded in `NormalForm`. -/
theorem normal_form_of_not_forall_adj (hedge : ∃ x y, X.Adj x y)
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬X.Adj x y) (huv : u ≠ v) (hnav : ¬X.Adj u v) :
    hX.NormalForm u v := by
  refine
    { ne := huv
      not_adj := hnav
      card_common := hX.card_commonNeighbors_mem hedge hn huv hnav
      isSRGWith := hX.isSRGWith_of_not_forall_adj hedge hn huv hnav
      disjoint := ?_
      cover := ?_
      card_left := (Set.ncard_congr' (hX.commonNeighborsEquiv u v huv hnav)).symm
      card_right := ?_
      card_remainder := ?_
      independent := ⟨hX.isIndepSet_commonNeighbors huv hnav,
        hX.isIndepSet_neighborSet_diff huv hnav,
        hX.isIndepSet_neighborSet_diff huv.symm (fun h ↦ hnav h.symm)⟩
      common_left := hX.adj_commonNeighborsEquiv_iff huv hnav
      common_right := ?_
      left_right := hX.adj_commonNeighborsEquiv_comm_iff huv hnav
      missed_card := ?_
      degrees := ?_
      remainder_left := ?_
      remainder_right := ?_
      remainder_edges := hX.card_edgeFinset_induce_compl_commonNeighbors hedge hn huv hnav
      remainder_third := fun w z h ↦ hX.third_mem_commonNeighbors w.property z.property h
      degree_sum := hX.sum_ncard_commonNeighbors hn huv hnav
      high_count := hX.two_mul_card_high_commonNeighbors hedge hn huv hnav
      two := hX.singleton_compl_commonNeighbors_of_two hedge hn huv hnav
      three := hX.claw_compl_commonNeighbors_of_three hedge hn huv hnav
      five := ?_ }
  · -- ⟨1⟩2 (210local): disjointness by the two adjacency indicators.
    have hnav' : ¬X.Adj v u := fun h ↦ hnav h.symm
    simp [List.pairwise_cons, Set.disjoint_left, mem_commonNeighbors, mem_neighborSet,
      compl_adj, huv, huv.symm, hnav, hnav']
    tauto
  · -- ⟨1⟩2 (210local): the same indicators exhaust the vertices.
    ext w
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_sdiff, mem_commonNeighbors, mem_neighborSet, compl_adj, Set.mem_univ, iff_true]
    by_cases hwu : w = u
    · tauto
    by_cases hwv : w = v
    · tauto
    have huw := Ne.symm hwu
    have hvw := Ne.symm hwv
    tauto
  · have h := (Set.ncard_congr'
      (hX.commonNeighborsEquiv v u huv.symm (fun h ↦ hnav h.symm))).symm
    simpa only [X.commonNeighbors_symm v u] using h
  · have h := hX.ncard_compl_commonNeighbors_add_five hedge hn huv hnav
    omega
  · intro x y
    have h := hX.adj_commonNeighborsEquiv_iff huv.symm (fun h ↦ hnav h.symm)
      ⟨x, x.property.2, x.property.1⟩ ⟨y, y.property.2, y.property.1⟩
    exact h.trans ⟨fun he ↦ Subtype.ext
      (congrArg (fun t : X.commonNeighbors v u ↦ (t : U)) he), fun he ↦ by cases he; rfl⟩
  · intro w
    have h := hX.card_non_neighbors_eq_zero_or_two huv hnav w.property
    simpa only [Fintype.card_subtype, missedCommonNeighbors] using h
  · intro w
    refine ⟨?_, hX.ncard_compl_commonNeighbors_inter_eq w.property⟩
    have h := hX.ncard_commonNeighbors_inter_eq_or_add_two huv hnav w.property
    omega
  · intro w x
    rw [mem_missedCommonNeighbors]
    exact hX.adj_commonNeighborsEquiv_iff_not_adj huv hnav w.property.1.1.symm w.property.1.2 x
  · intro w x
    rw [mem_missedCommonNeighbors]
    exact hX.adj_commonNeighborsEquiv_iff_not_adj huv.symm (fun h ↦ hnav h.symm)
      w.property.2.1.symm w.property.2.2 ⟨x, x.property.2, x.property.1⟩
  · intro hk
    obtain ⟨e, he⟩ := hX.exists_pair_label_equiv hedge hn huv hnav (by omega)
    refine ⟨e, he, ?_⟩
    intro w z
    rw [he w, he z]
    exact hX.adj_iff_disjoint_missedCommonNeighbors_of_five hedge hn huv hnav hk w z

end NormalForm

end HasTriangleProperty
end SimpleGraph
