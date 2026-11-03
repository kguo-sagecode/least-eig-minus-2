/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.Computations.C20E8

/-!
# Valencies of represented graphs

Lemma `lem:4-valency` (Gap 14) and assertion 2 of Theorem 4.3 of [CGSS].
-/

open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj]

/-- Lemma `lem:4-valency`, Section 4 of [CGSS] (Gap 14): a represented
neighbourhood takes at most one vector from each pair `{z, r-z}` in `Nᵣ`.
Doubling it gives an injection into `Nᵣ`, so a bound of `2b` there gives `b`
as the valency bound. -/
theorem IsRepresentedIn.degree_le_of_card_N_le {S : LineSystem E}
    (hX : X.IsRepresentedIn S) (hS : S.IsStarClosed) {b : ℕ}
    (hN : ∀ r ∈ S.Φ, (S.N r).ncard ≤ 2 * b) (u : V) : X.degree u ≤ b := by
  classical
  obtain ⟨x, hx, hm⟩ := hX
  let := (S.finite_N (x u)).fintype
  let f : X.neighborSet u → S.N (x u) := fun v ↦
    ⟨x v, hm v, hx.inner_of_adj v.property.symm⟩
  let e := S.pairInv (x u) hS (hm u)
  have hf : Function.Injective f := fun v w h ↦
    Subtype.ext (hx.injective (congrArg Subtype.val h))
  have hcross (v w : X.neighborSet u) : f v ≠ e (f w) := by
    intro h
    have he : x v = x u - x w := congrArg Subtype.val h
    have hp := hx.inner_nonneg v w
    rw [he, inner_sub_left, hx.inner_of_adj w.property, hx.inner_self] at hp
    norm_num at hp
  let g : X.neighborSet u ⊕ X.neighborSet u → S.N (x u) := Sum.elim f (e ∘ f)
  have hg : Function.Injective g := by
    rintro (v | v) (w | w) h
    · exact congrArg Sum.inl (hf h)
    · exact (hcross v w h).elim
    · exact (hcross w v h.symm).elim
    · exact congrArg Sum.inr (hf (e.injective h))
  have hcard := Fintype.card_le_of_injective g hg
  have hbound := hN (x u) (hm u)
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hbound
  simp only [Fintype.card_sum, X.card_neighborSet_eq_degree] at hcard
  omega

/-- Theorem 4.3, assertion 2, of [CGSS]: every vertex of a graph represented
in `E₈` has at most 28 neighbours, by C20 and the pairing argument. -/
theorem IsRepresentedIn.degree_le_28 (hX : X.IsRepresentedIn LineSystem.E₈) (u : V) :
    X.degree u ≤ 28 := by
  apply hX.degree_le_of_card_N_le LineSystem.isStarClosed_E₈ (b := 28) ?_ u
  intro r hr
  rw [LineSystem.E₈.card_N hr]

end SimpleGraph
