/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Hoffman
import LineGraphs.Representation.Theorem44Unconditional
import LineGraphs.Computations.C10

/-!
# The regular case of Hoffman's theorem

Theorem 4.11 of [CGSS], `thm:4.11`, and its prerequisite `lem:4-regglg`.
The proof uses connectedness of the generalized line graph, without assuming
connectedness of its root graph (errata Gap 18).
-/

namespace SimpleGraph

variable {V W : Type*}

-- Lemma (regular connected generalized line graphs)
/-- Step `s4rgzero` of `lem:4-regglg`, Theorem 4.11 of [CGSS]: zero parameters
give the ordinary line graph. -/
noncomputable def generalizedLineGraphZeroIso (Y : SimpleGraph W) :
    generalizedLineGraph Y (fun _ ↦ 0) ≃g Y.lineGraph where
  toEquiv := Equiv.sumEmpty _ _
  map_rel_iff' := by
    rintro (e | ⟨i, k, b⟩) (f | ⟨j, l, c⟩)
    · rfl
    all_goals exact Fin.elim0 (by assumption)

-- Lemma (regular connected generalized line graphs)
/-- Step `s4rgiso` of `lem:4-regglg`, Theorem 4.11 of [CGSS]: a nonempty set
closed under adjacency exhausts a connected graph. This is also step `s412all`
of Remark 4.12. -/
theorem Connected.forall_of_adj_closed {X : SimpleGraph V} (hc : X.Connected)
    {P : V → Prop} {u : V} (hu : P u)
    (hclosed : ∀ ⦃v w⦄, P v → X.Adj v w → P w) : ∀ v, P v := by
  intro v
  obtain ⟨p⟩ := hc.preconnected u v
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hclosed hu h)

-- Lemma (regular connected generalized line graphs)
/-- Step `s4rgiso` of `lem:4-regglg`, Theorem 4.11 of [CGSS]: a positive
parameter at an isolated root vertex, together with connectedness of the
generalized line graph, forces a cocktail party graph. -/
theorem nonempty_iso_cocktailParty_of_isolated
    (Y : SimpleGraph W) (a : W → ℕ) (hc : (generalizedLineGraph Y a).Connected)
    (i : W) (hi : 0 < a i) (hiso : ∀ j, ¬Y.Adj i j) :
    Nonempty (generalizedLineGraph Y a ≃g cocktailParty (a i)) := by
  classical
  let f : Fin (a i) × Bool → GeneralizedLineGraphVertex Y a :=
    fun p ↦ .inr ⟨i, p⟩
  have hf : Function.Injective f := by
    intro p q hpq
    simpa [f] using hpq
  have hclosed : ∀ ⦃v w⦄, v ∈ Set.range f →
      (generalizedLineGraph Y a).Adj v w → w ∈ Set.range f := by
    rintro _ (e | ⟨j, k, b⟩) ⟨p, rfl⟩ hvw
    · rcases e with ⟨⟨j, l⟩, hjl⟩
      change i ∈ s(j, l) at hvw
      rcases Sym2.mem_iff.mp hvw with rfl | rfl
      · exact (hiso l hjl).elim
      · exact (hiso j hjl.symm).elim
    · change i = j ∧ _ at hvw
      rcases hvw with ⟨rfl, _⟩
      exact ⟨(k, b), rfl⟩
  have hs : Function.Surjective f :=
    hc.forall_of_adj_closed (Set.mem_range_self (⟨0, hi⟩, false)) hclosed
  let e : cocktailParty (a i) ≃g generalizedLineGraph Y a :=
    { toEquiv := Equiv.ofBijective f ⟨hf, hs⟩
      map_rel_iff' := by
        intro p q
        change (i = i ∧ p.1.val ≠ q.1.val) ↔ p.1 ≠ q.1
        simp only [true_and, ne_eq, Fin.val_inj] }
  exact ⟨e.symm⟩

variable [Fintype V] [DecidableEq V] {X : SimpleGraph V}
  [DecidableRel X.Adj] {d : ℕ}

omit [DecidableEq V] in
-- Lemma (regular connected generalized line graphs)
/-- Lemma `lem:4-regglg`, Theorem 4.11 of [CGSS]: a connected regular
generalized line graph is a line graph or a cocktail party graph. The split on
positive parameters repairs errata Gap 18. -/
theorem IsGeneralizedLineGraph.lineGraph_or_cocktailParty
    (hX : X.IsGeneralizedLineGraph) (hc : X.Connected) (hr : X.IsRegularOfDegree d) :
    (∃ (m : ℕ) (Y : SimpleGraph (Fin m)), Nonempty (X ≃g Y.lineGraph)) ∨
      ∃ m, Nonempty (X ≃g cocktailParty m) := by
  classical
  obtain ⟨m, Y, a, ⟨e⟩⟩ := hX
  have hr' : (generalizedLineGraph Y a).IsRegularOfDegree d := by
    intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [e.degree_eq, hr u]
  by_cases hz : ∀ i, a i = 0
  · -- Step `s4rgzero`.
    have ha : a = fun _ ↦ 0 := funext hz
    subst a
    exact Or.inl ⟨m, Y, ⟨e.trans (generalizedLineGraphZeroIso Y)⟩⟩
  · obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
      push Not at hz
      exact hz.imp fun _ h ↦ Nat.pos_of_ne_zero h
    have hiso : ∀ j, ¬Y.Adj i j := by
      -- Step `s4rgedge`: the degree of an incident edge exceeds that of a petal.
      intro j hij
      have hp := generalizedLineGraph_degree_petal Y a i ⟨0, hi⟩ false
      have he := generalizedLineGraph_degree_edge Y a hij
      rw [hr' _] at hp he
      have hj := hij.symm.degree_pos_left
      omega
    -- Step `s4rgiso`: the isolated root vertex gives the entire component.
    obtain ⟨f⟩ := nonempty_iso_cocktailParty_of_isolated Y a
      (e.connected_iff.mp hc) i hi hiso
    exact Or.inr ⟨a i, ⟨e.trans f⟩⟩

-- Theorem 4.11
/-- Theorem 4.11 of [CGSS], `thm:4.11`: a connected regular graph with least
eigenvalue at least minus two is a line graph, a cocktail party graph, or is
represented in E₈. -/
theorem hoffman_rayChaudhuri (hc : X.Connected) (hr : X.IsRegularOfDegree d)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    (∃ (m : ℕ) (Y : SimpleGraph (Fin m)), Nonempty (X ≃g Y.lineGraph)) ∨
      (∃ m, Nonempty (X ≃g cocktailParty m)) ∨ X.IsRepresentedIn LineSystem.E₈ := by
  -- Steps `s411hoff` and `s411glg`.
  rcases hoffman hc hp with h | h
  · exact (h.lineGraph_or_cocktailParty hc hr).imp_right Or.inl
  · exact Or.inr (Or.inr h)

-- Remark after the examples in Section 4
/-- The remark after the examples in Section 4 of [CGSS] (blueprint `rem:4-large`,
assertion 2), step `s4lrtwo`: the bounds of
Theorem 4.4 exclude E₈ when the order exceeds 28 or the degree exceeds 16.
The unconditional bounds incorporate the correction in errata Error 15. -/
theorem hoffman_rayChaudhuri_of_large (hc : X.Connected) (hr : X.IsRegularOfDegree d)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hlarge : 28 < Fintype.card V ∨ 16 < d) :
    (∃ (m : ℕ) (Y : SimpleGraph (Fin m)), Nonempty (X ≃g Y.lineGraph)) ∨
      ∃ m, Nonempty (X ≃g cocktailParty m) := by
  let : Nonempty V := hc.nonempty
  rcases hoffman_rayChaudhuri hc hr hp with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hn := h.card_le_28_of_regular hr
    have hd := h.degree_le_16_of_regular hr
    omega

end SimpleGraph
