/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.CocktailParty
import LineGraphs.Spectral.LineGraphRegular
import LineGraphs.Graphs.Basic

/-! # Orders and degrees of the excluded families in Proposition `prop:414-seven` -/

namespace SimpleGraph

/-- The triangular graph order in step `s414sevpar` of Proposition `prop:414-seven`. -/
theorem card_completeGraph_edgeSet (m : ℕ) :
    Fintype.card (⊤ : SimpleGraph (Fin m)).edgeSet = m.choose 2 := by
  rw [card_edgeSet, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

open Classical in
/-- The lattice graph order in step `s414sevpar` of Proposition `prop:414-seven`. -/
theorem card_completeBipartiteGraph_edgeSet (m : ℕ) :
    Fintype.card (completeBipartiteGraph (Fin m) (Fin m)).edgeSet = m * m := by
  rw [← Fintype.card_congr (completeBipartiteEdgeEquiv (Fin m) (Fin m))]
  simp

open Classical in
/-- The triangular graph valency in step `s414sevpar` of Proposition `prop:414-seven`. -/
theorem lineGraph_completeGraph_isRegularOfDegree (m : ℕ) :
    (⊤ : SimpleGraph (Fin m)).lineGraph.IsRegularOfDegree (2 * (m - 2)) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := by simpa using he
    have hm : 2 ≤ m := by
      have h := Fintype.one_lt_card_iff.mpr ⟨u, v, huv⟩
      simp only [Fintype.card_fin] at h
      omega
    rw [degree_lineGraph he]
    simp only [complete_graph_degree, Fintype.card_fin]
    omega

open Classical in
/-- A vertex of a balanced complete bipartite graph has one part as its neighbourhood
(step `s414sevpar`, Proposition `prop:414-seven`). -/
theorem completeBipartiteGraph_isRegularOfDegree (m : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin m)).IsRegularOfDegree m := by
  intro u
  rw [← card_neighborSet_eq_degree]
  cases u with
  | inl u =>
    let e : (completeBipartiteGraph (Fin m) (Fin m)).neighborSet (Sum.inl u) ≃ Fin m :=
      { toFun := fun v ↦ match v with
          | ⟨Sum.inl _, h⟩ => False.elim (by simp at h)
          | ⟨Sum.inr v, _⟩ => v
        invFun := fun v ↦ ⟨Sum.inr v, by simp⟩
        left_inv := by
          rintro ⟨v | v, h⟩
          · simp at h
          · rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]
  | inr u =>
    let e : (completeBipartiteGraph (Fin m) (Fin m)).neighborSet (Sum.inr u) ≃ Fin m :=
      { toFun := fun v ↦ match v with
          | ⟨Sum.inl v, _⟩ => v
          | ⟨Sum.inr _, h⟩ => False.elim (by simp at h)
        invFun := fun v ↦ ⟨Sum.inl v, by simp⟩
        left_inv := by
          rintro ⟨v | v, h⟩
          · rfl
          · simp at h
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]

open Classical in
/-- The lattice graph valency in step `s414sevpar` of Proposition `prop:414-seven`. -/
theorem lineGraph_completeBipartiteGraph_isRegularOfDegree (m : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin m)).lineGraph.IsRegularOfDegree (2 * m - 2) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    rw [degree_lineGraph he, completeBipartiteGraph_isRegularOfDegree m u,
      completeBipartiteGraph_isRegularOfDegree m v]
    omega

/-- The cocktail party valency in step `s414sevpar` of Proposition `prop:414-seven`. -/
theorem cocktailParty_isRegularOfDegree (m : ℕ) :
    (cocktailParty m).IsRegularOfDegree (2 * m - 2) := by
  intro u
  let e : (cocktailParty m).neighborSet u ≃ {i : Fin m // i ≠ u.1} × Bool :=
    { toFun := fun v ↦ (⟨v.val.1, Ne.symm v.property⟩, v.val.2)
      invFun := fun v ↦ ⟨(v.1.val, v.2), v.1.property.symm⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← card_neighborSet_eq_degree, Fintype.card_congr e, Fintype.card_prod]
  have hc : Fintype.card {i : Fin m // i ≠ u.1} = m - 1 := by
    simp
  rw [hc, Fintype.card_bool]
  have hm := u.1.isLt
  omega

/-- Isomorphic nonempty regular graphs have the same valency (`prop:414-seven`). -/
theorem Iso.regular_degree_eq {V W : Type*} [Fintype V] [Nonempty V] [Fintype W]
    {X : SimpleGraph V} {Y : SimpleGraph W} [DecidableRel X.Adj] [DecidableRel Y.Adj]
    {k l : ℕ} (e : X ≃g Y) (hX : X.IsRegularOfDegree k) (hY : Y.IsRegularOfDegree l) :
    k = l := by
  obtain ⟨u⟩ := ‹Nonempty V›
  exact (hX u).symm.trans ((e.degree_eq u).symm.trans (hY _))

end SimpleGraph
