/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.RootTypeClassified
import LineGraphs.Representation.TypeDNormalForm
import LineGraphs.Representation.SymmetricSquare
import LineGraphs.Representation.Valency

/-!
# Hoffman's theorem

Theorem 4.10 of [CGSS], `thm:4.10` in the Section 4 blueprint, with connectedness
made explicit as required by errata Implicit hypothesis 1.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj]

omit [Fintype V] in
-- Theorem 4.10
/-- Theorem 4.10 of [CGSS], `thm:4.10`: a connected graph with least eigenvalue
at least minus two is a generalized line graph or is represented in E₈.
Connectedness is errata Implicit hypothesis 1. -/
theorem hoffman [Finite V] (hc : X.Connected)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    X.IsGeneralizedLineGraph ∨ X.IsRepresentedIn LineSystem.E₈ := by
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := X.exists_representation_iff_posSemidef.mpr hp
  -- Step `s410rep`: place the representation in a classified root system.
  obtain ⟨t, ht, _⟩ := hx.exists_isRepresentedIn_rootType hc
  cases t with
  | A n hn =>
    -- Step `s410A`: Aₙ is a subset of Dₙ₊₁, including the small ranks.
    exact Or.inl ((ht.mono (LineSystem.An_Φ_subset_Dn n)).isGeneralizedLineGraph_of_Dn
      (by omega))
  | D n hn =>
    -- Step `s410D`: Theorem 4.2 recognizes the generalized line graph.
    exact Or.inl (ht.isGeneralizedLineGraph_of_Dn (by omega))
  | E₆ =>
    exact Or.inr (ht.mono (LineSystem.E₆_Φ_subset_E₇.trans LineSystem.E₇_Φ_subset_E₈))
  | E₇ => exact Or.inr (ht.mono LineSystem.E₇_Φ_subset_E₈)
  | E₈ => exact Or.inr ht

-- Remark after the examples in Section 4
/-- The remark after the examples in Section 4 of [CGSS] (blueprint `rem:4-large`,
assertion 1), step `s4lrone`: the order and
degree bounds of Theorem 4.3 exclude the exceptional alternative in Theorem 4.10. -/
theorem hoffman_of_large (hc : X.Connected)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hlarge : 36 < Fintype.card V ∨ ∃ u, 28 < X.degree u) :
    X.IsGeneralizedLineGraph := by
  rcases hoffman hc hp with h | h
  · exact h
  · rcases hlarge with hn | ⟨u, hu⟩
    · exact (Nat.not_lt_of_ge h.card_le_36 hn).elim
    · exact (Nat.not_lt_of_ge (h.degree_le_28 u) hu).elim

end SimpleGraph
