/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.TwoRegular
import LineGraphs.Seidel.EightVertexModels

/-!
# The cases of valency at most two in SE4

Section 2 of `cgss/proofs/reg8/reg8.tex`, prerequisite `res:414-SE4` for
Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]

-- Theorem SE4 (Remark 4.14), valency zero
/-- The zero-valency case of `res:414-SE4`, Remark 4.14 of [CGSS]. -/
theorem IsRegularOfDegree.eq_bot_of_zero (hr : X.IsRegularOfDegree 0) : X = ⊥ := by
  apply eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have hh := (X.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  rw [hr u] at hh
  omega

-- Theorem SE4 (Remark 4.14), valency one
/-- The one-valency case of `res:414-SE4`, Remark 4.14 of [CGSS]: the
perfect matching on eight vertices is `fourK2`. -/
theorem IsRegularOfDegree.nonempty_iso_fourK2 (hr : X.IsRegularOfDegree 1)
    (hn : Fintype.card V = 8) : Nonempty (X ≃g fourK2) := by
  classical
  have hcompl : Xᶜ.IsRegularOfDegree (2 * 4 - 2) := by
    have hh := hr.compl
    simpa only [hn] using hh
  obtain ⟨e⟩ := hcompl.nonempty_iso_cocktailParty (by omega) hn
  have f : Nonempty (X ≃g (cocktailParty 4)ᶜ) := by
    rw [← compl_compl X]
    exact ⟨e.compl⟩
  exact ⟨f.some.trans fourK2.cocktailPartyComplIso.symm⟩

-- Theorem SE4 (Remark 4.14), valency two
/-- The two-valency case of `res:414-SE4`, Remark 4.14 of [CGSS]: the
partitions of eight into cycle lengths at least three are `8`, `3 + 5`, and
`4 + 4`. The named models use the fixed labels required by C22. -/
theorem IsRegularOfDegree.nonempty_iso_of_two_of_card_eq_eight
    (hr : X.IsRegularOfDegree 2) (hn : Fintype.card V = 8) :
    Nonempty (X ≃g cycleGraph 8) ∨ Nonempty (X ≃g cycleThreeFive) ∨
      Nonempty (X ≃g twoC4) := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_cases hc : X.Connected
  · apply Or.inl
    rw [← hn]
    exact hr.nonempty_iso_cycle hc
  obtain ⟨p, q, hp, hq, hpq, ⟨e⟩⟩ :=
    hr.nonempty_iso_sum_cycles_of_not_connected (by omega) hc
  have hp_cases : p = 3 ∨ p = 4 ∨ p = 5 := by omega
  rcases hp_cases with rfl | rfl | rfl
  · have hq5 : q = 5 := by omega
    subst q
    exact Or.inr (Or.inl ⟨e.trans cycleThreeFive.sumIso⟩)
  · have hq4 : q = 4 := by omega
    subst q
    exact Or.inr (Or.inr ⟨e.trans twoC4.sumIso⟩)
  · have hq3 : q = 3 := by omega
    subst q
    exact Or.inr (Or.inl ⟨e.trans (Iso.sumComm.trans cycleThreeFive.sumIso)⟩)

end SimpleGraph
