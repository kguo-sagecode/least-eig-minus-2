/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.LabelledGraphs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Recognition and orientation of paths

The longest-path proof of `lem:path-labelling` in the Remark 3.11 blueprint.
-/

namespace SimpleGraph

open Walk

variable {V : Type*} [Fintype V] {X : SimpleGraph V}
  [DecidableRel X.Adj]

private theorem degree_ge_three_of_neighbors {v a b c : V}
    (ha : X.Adj v a) (hb : X.Adj v b) (hc : X.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ X.degree v := by
  classical
  have hs : ({a, b, c} : Finset V) ⊆ X.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp_all
  calc
    3 = ({a, b, c} : Finset V).card := by simp [hab, hac, hbc]
    _ ≤ X.degree v := Finset.card_le_card hs

private theorem longest_path_support_closed {u v : V} {p : X.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ u' v' (q : X.Walk u' v'), q.IsPath → q.length ≤ p.length)
    (hdeg : ∀ w, X.degree w ≤ 2) {x y : V} (hx : x ∈ p.support) (hxy : X.Adj x y) :
    y ∈ p.support := by
  classical
  by_contra hy
  obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  subst x
  by_cases hi0 : i = 0
  · subst i
    have h := hmax _ _ (p.cons (by simpa using hxy.symm)) (hp.cons hy)
    simp only [Walk.length_cons] at h
    omega
  by_cases hil : i = p.length
  · subst i
    have h := hmax _ _ (p.concat (by simpa using hxy)) (hp.concat hy _)
    simp only [Walk.length_concat] at h
    omega
  have hprev : i - 1 + 1 = i := by omega
  have ha : X.Adj (p.getVert i) (p.getVert (i - 1)) := by
    simpa only [hprev] using (p.adj_getVert_succ (i := i - 1) (by omega)).symm
  have hb := p.adj_getVert_succ (i := i) (by omega)
  have hab : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have he := hp.getVert_injOn (by change i - 1 ≤ p.length; omega)
      (by change i + 1 ≤ p.length; omega) h
    omega
  have hac : p.getVert (i - 1) ≠ y := by
    intro h
    exact hy (h ▸ p.getVert_mem_support (i - 1))
  have hbc : p.getVert (i + 1) ≠ y := by
    intro h
    exact hy (h ▸ p.getVert_mem_support (i + 1))
  have hthree := degree_ge_three_of_neighbors ha hb hxy hab hac hbc
  have htwo := hdeg (p.getVert i)
  omega

/-- `lem:path-labelling`, Remark 3.11 of [CGSS]: a finite connected acyclic graph
of maximum degree two is isomorphic to a path. -/
theorem nonempty_iso_pathGraph (hconn : X.Connected) (hacyc : X.IsAcyclic)
    (hdeg : ∀ w, X.degree w ≤ 2) :
    Nonempty (pathGraph (Fintype.card V) ≃g X) := by
  classical
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length X
  have hclosed {x y : V} := longest_path_support_closed hp hmax hdeg (x := x) (y := y)
  have hall (w : V) : w ∈ p.support := by
    have heq := hconn.constant_of_edge_eq (f := fun z => z ∈ p.support)
      (fun {x y} hxy => propext ⟨fun hx => hclosed hx hxy,
        fun hy => hclosed hy hxy.symm⟩) u w
    exact heq ▸ p.start_mem_support
  let e : Fin (p.length + 1) ≃ V := Equiv.ofBijective (fun i => p.getVert i.val) (by
    constructor
    · intro i j hij
      exact Fin.ext (hp.getVert_injOn (by change i.val ≤ p.length; omega)
        (by change j.val ≤ p.length; omega) hij)
    · intro w
      obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp (hall w)
      exact ⟨⟨i, by omega⟩, hi⟩)
  have hle : pathGraph (p.length + 1) ≤ X.comap e := by
    intro i j hij
    change X.Adj (p.getVert i.val) (p.getVert j.val)
    rcases pathGraph_adj.mp hij with hij | hji
    · simpa only [hij] using p.adj_getVert_succ (i := i.val) (by omega)
    · simpa only [hji] using (p.adj_getVert_succ (i := j.val) (by omega)).symm
  have htree : (X.comap e).IsTree := (Iso.comap e X).isTree_iff.mpr ⟨hconn, hacyc⟩
  have heq : pathGraph (p.length + 1) = X.comap e :=
    le_antisymm hle ((isTree_iff_minimal_connected.mp htree).2
      (pathGraph_connected _) hle)
  have hn : p.length + 1 = Fintype.card V := by simpa using Fintype.card_congr e
  let e' : Fin (Fintype.card V) ≃ V := (finCongr hn.symm).trans e
  refine ⟨{ e' with map_rel_iff' := ?_ }⟩
  intro i j
  change (X.comap e).Adj (finCongr hn.symm i) (finCongr hn.symm j) ↔ _
  rw [← heq, pathGraph_adj, pathGraph_adj]
  rfl

omit [Fintype V] [DecidableRel X.Adj] in
/-- Reversing the indices of any path labelling gives another path labelling. -/
theorem path_labelling_reverse {m : ℕ} (e : pathGraph m ≃g X) :
    ∃ e' : pathGraph m ≃g X, ∀ i, e' i = e i.rev := by
  refine ⟨{ (Fin.revPerm.trans e.toEquiv) with map_rel_iff' := ?_ }, fun _ => rfl⟩
  intro i j
  change X.Adj (e i.rev) (e j.rev) ↔ _
  rw [e.map_rel_iff, pathGraph_adj, pathGraph_adj]
  simp only [Fin.val_rev]
  omega

private theorem degree_ge_two_of_neighbors {v a b : V}
    (ha : X.Adj v a) (hb : X.Adj v b) (hab : a ≠ b) : 2 ≤ X.degree v := by
  classical
  have hs : ({a, b} : Finset V) ⊆ X.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp_all
  calc
    2 = ({a, b} : Finset V).card := by simp [hab]
    _ ≤ X.degree v := Finset.card_le_card hs

/-- A path labelling can start at any specified vertex of degree at most one. -/
theorem exists_path_labelling_from (hconn : X.Connected) (hacyc : X.IsAcyclic)
    (hdeg : ∀ w, X.degree w ≤ 2) (w : V) (hw : X.degree w ≤ 1) :
    ∃ e : pathGraph (Fintype.card V) ≃g X,
      e ⟨0, Fintype.card_pos_iff.mpr hconn.nonempty⟩ = w := by
  classical
  obtain ⟨e⟩ := nonempty_iso_pathGraph hconn hacyc hdeg
  let i := e.symm w
  have hiw : e i = w := e.apply_symm_apply w
  have hi : i.val = 0 ∨ i.val + 1 = Fintype.card V := by
    by_contra hn
    have hi0 : i.val ≠ 0 := fun h => hn (Or.inl h)
    have hin : i.val + 1 ≠ Fintype.card V := fun h => hn (Or.inr h)
    let a : Fin (Fintype.card V) := ⟨i.val - 1, by omega⟩
    let b : Fin (Fintype.card V) := ⟨i.val + 1, by omega⟩
    have ha : X.Adj w (e a) := by
      rw [← hiw, e.map_rel_iff, pathGraph_adj]
      exact Or.inr (by dsimp [a]; omega)
    have hb : X.Adj w (e b) := by
      rw [← hiw, e.map_rel_iff, pathGraph_adj]
      exact Or.inl rfl
    have hab : e a ≠ e b := by
      intro h
      have hh := congrArg Fin.val (e.injective h)
      dsimp [a, b] at hh
      omega
    have := degree_ge_two_of_neighbors ha hb hab
    omega
  rcases hi with hi | hi
  · refine ⟨e, ?_⟩
    have hi' : (⟨0, Fintype.card_pos_iff.mpr hconn.nonempty⟩ : Fin (Fintype.card V)) = i :=
      Fin.ext hi.symm
    rw [hi', hiw]
  · obtain ⟨e', he'⟩ := path_labelling_reverse e
    refine ⟨e', ?_⟩
    rw [he']
    have hi' : (⟨0, Fintype.card_pos_iff.mpr hconn.nonempty⟩ : Fin (Fintype.card V)).rev = i := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hi', hiw]

end SimpleGraph
