/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.GeneralizedLineGraph
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cocktail party parameters

Lemma `lem:414-CP` of the blueprint for Remark 4.14 of [CGSS]. The complement
of a graph with these parameters is a perfect matching.
-/

namespace SimpleGraph

-- Lemma (cocktail party parameters), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-CP`, Remark 4.14 of [CGSS]: a `(2m - 2)`-regular graph on
`2m` vertices, for `m ≥ 1`, is isomorphic to the cocktail party graph. -/
theorem IsRegularOfDegree.nonempty_iso_cocktailParty {V : Type*} [Fintype V]
    {X : SimpleGraph V} [DecidableRel X.Adj] {m : ℕ}
    (h : X.IsRegularOfDegree (2 * m - 2)) (hm : 1 ≤ m)
    (hn : Fintype.card V = 2 * m) : Nonempty (X ≃g cocktailParty m) := by
  classical
  -- Step `s414cpcompl`: the complement has degree one.
  let Y := Xᶜ
  have hY : Y.IsRegularOfDegree 1 := by
    have hh := h.compl
    simpa only [hn, show 2 * m - 1 - (2 * m - 2) = 1 by omega] using hh
  have hu : ∀ v, ∃! w, Y.Adj v w := fun v ↦
    degree_eq_one_iff_existsUnique_adj.mp (hY v)
  choose p hp huniq using hu
  have hinv : Function.Involutive p := fun v ↦ (huniq (p v) v (hp v).symm).symm
  have hne : ∀ v, p v ≠ v := fun v ↦ (hp v).ne.symm
  -- Step `s414cpmatch`: select the smaller endpoint of each matched pair.
  let r := Fintype.equivFin V
  let P := {v : V // r v < r (p v)}
  let f : P × Bool → V := fun x ↦ if x.2 then p x.1 else x.1
  have hfi : Function.Injective f := by
    rintro ⟨⟨u, hu⟩, b⟩ ⟨⟨v, hv⟩, c⟩ he
    cases b <;> cases c
    · simp only [f, Bool.false_eq_true, ite_false] at he
      subst v
      rfl
    · simp only [f, Bool.false_eq_true, ite_false, ite_true] at he
      have hlt : r (p v) < r v := by simpa only [he, hinv v] using hu
      exact (lt_asymm hlt hv).elim
    · simp only [f, Bool.false_eq_true, ite_false, ite_true] at he
      have hlt : r (p u) < r u := by simpa only [← he, hinv u] using hv
      exact (lt_asymm hlt hu).elim
    · simp only [f, ite_true] at he
      have huv := hinv.injective he
      subst v
      rfl
  have hfs : Function.Surjective f := by
    intro v
    by_cases hv : r v < r (p v)
    · exact ⟨(⟨v, hv⟩, false), rfl⟩
    · have hlt : r (p v) < r v := lt_of_le_of_ne (le_of_not_gt hv)
        (fun he ↦ hne v (r.injective he))
      exact ⟨(⟨p v, by simpa only [hinv v] using hlt⟩, true), hinv v⟩
  let e : P × Bool ≃ V := Equiv.ofBijective f ⟨hfi, hfs⟩
  have hflip (x : P × Bool) : f (x.1, !x.2) = p (f x) := by
    rcases x with ⟨v, b⟩
    cases b <;> simp [f, hinv (v : V)]
  have hadj (x y : P × Bool) : Y.Adj (e x) (e y) ↔ x.1 = y.1 ∧ x.2 ≠ y.2 := by
    change Y.Adj (f x) (f y) ↔ _
    have hh : Y.Adj (f x) (f y) ↔ f y = p (f x) :=
      ⟨fun ha ↦ huniq (f x) (f y) ha, fun he ↦ he ▸ hp (f x)⟩
    rw [hh, ← hflip x, hfi.eq_iff]
    rcases x with ⟨u, b⟩
    rcases y with ⟨v, c⟩
    cases b <;> cases c <;> simp [eq_comm]
  have hP : Fintype.card P = m := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_prod, Fintype.card_bool, hn] at hh
    omega
  let i : Fin m ≃ P := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hP])
  let q : Fin m × Bool ≃ V := (i.prodCongr (Equiv.refl Bool)).trans e
  have hq (u v : Fin m × Bool) : Y.Adj (q u) (q v) ↔ u.1 = v.1 ∧ u.2 ≠ v.2 := by
    change Y.Adj (e (i u.1, u.2)) (e (i v.1, v.2)) ↔ _
    rw [hadj, i.injective.eq_iff]
  -- Distinct vertices are adjacent in `X` exactly when they belong to different pairs.
  refine ⟨(show cocktailParty m ≃g X from
    { toEquiv := q
      map_rel_iff' := ?_ }).symm⟩
  intro u v
  change X.Adj (q u) (q v) ↔ u.1 ≠ v.1
  rw [← show Yᶜ = X from compl_compl X, compl_adj, q.injective.ne_iff, hq]
  rcases u with ⟨i, b⟩
  rcases v with ⟨j, c⟩
  cases b <;> cases c <;> simp

end SimpleGraph
