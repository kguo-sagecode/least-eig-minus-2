/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Parameters
import LineGraphs.Seidel.LineGraph
import LineGraphs.Seidel.LatticeRoots
import LineGraphs.Computations.C18
import LineGraphs.Representation.Theorem44Unconditional
import LineGraphs.Representation.TypeA
import LineGraphs.Representation.TypeDNormalForm
import LineGraphs.Representation.HoffmanRegular

/-! # Parameters and root types for the proof of Remark 4.14

Steps `s414mdet`--`s414mE` of `rem:414-proof`.
-/

open Submodule Module

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {n k a c : ℕ}

/-- Steps `s414mbounds`--`s414mCeighteen` of Remark 4.14: the graph hypotheses
verify every bound and arithmetic condition of C18. -/
theorem IsSRGWith.parameters_mem_small_list (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0)
    (hE : X.IsRepresentedIn LineSystem.E₈) :
    ((n : ℤ), (k : ℤ), (a : ℤ), (c : ℤ),
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank : ℤ)) ∈
        Computations.C18.parameters := by
  let := hc.nonempty
  have hn : 0 < n := h.card ▸ Fintype.card_pos
  have hn28 : n ≤ 28 := h.card ▸ hE.card_le_28_of_regular h.regular
  have hk16 := hE.degree_le_16_of_regular h.regular
  obtain ⟨hk, hkn, ha, hcpos, hck, hbound, hlin⟩ :=
    h.params_of_det_two_add_adjMatrix_eq_zero hc hdet
  have hp := h.param_eq X hn
  have ha' : a ≤ k := by omega
  have ha1 : 1 ≤ k - a := by omega
  have hk' : k ≤ n := by omega
  have hk1 : 1 ≤ n - k := by omega
  zify [ha', ha1, hk', hk1] at hp
  have hc2 : c ≤ 2 * k := by omega
  have hn2 : 2 ≤ n := by omega
  zify [hc2, hn2] at hbound
  have hρ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ 8 := by
    obtain ⟨x, hx, _⟩ := hE
    rw [hx.rank_two_add_adjMatrix X]
    have hle := Submodule.finrank_le (span ℝ (Set.range x))
    simpa using hle
  exact Computations.C18.srg_parameters (by omega) (by omega) (by omega) (by omega)
    (by positivity) (by omega) (by omega) (by omega) (by positivity) (by omega)
    (by nlinarith only [hp]) hlin hbound (h.rank_two_add_adjMatrix_of_det_eq_zero hc hdet)

/-- Steps `s414mR`--`s414mAD` of Remark 4.14: classify the lattice roots and exclude
the classical types by Theorems 4.1, 4.2 and the regular generalized-line-graph dichotomy. -/
theorem IsRepresentation.nonempty_iso_exceptional_of_latticeRoots
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : V → E}
    (hx : X.IsRepresentation x) (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0)
    (hex : ∀ m, ¬ Nonempty (X ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) ∧
      ¬ Nonempty (X ≃g cocktailParty m)) :
    Nonempty (hx.latticeRoots.Iso LineSystem.E₆) ∨
      Nonempty (hx.latticeRoots.Iso LineSystem.E₇) ∨
      Nonempty (hx.latticeRoots.Iso LineSystem.E₈) := by
  have hnotL {W : Type} (Y : SimpleGraph W) (g : X ≃g Y.lineGraph) : False := by
    obtain ⟨m, _, hm⟩ := h.nonempty_iso_lineGraph_complete_or_completeBipartite hc hdet g
    exact hm.elim (hex m).1 (hex m).2.1
  obtain ⟨t, ⟨e⟩⟩ := hx.latticeRoots.exists_iso_rootType (hx.latticeRoots_nonempty hc)
    (hx.isIndecomposable_latticeRoots hc) hx.isStarClosed_latticeRoots
  have hrep := hx.isRepresentedIn_latticeRoots.of_iso e
  cases t with
  | A ℓ hℓ =>
    obtain ⟨Y, _, ⟨g⟩⟩ := hrep.nonempty_iso_lineGraph_of_An
    exact (hnotL Y g).elim
  | D ℓ hℓ =>
    have hGL := hrep.isGeneralizedLineGraph_of_Dn (by omega)
    rcases hGL.lineGraph_or_cocktailParty hc h.regular with hline | hcp
    · obtain ⟨m, Y, ⟨g⟩⟩ := hline
      exact (hnotL Y g).elim
    · obtain ⟨m, hm⟩ := hcp
      exact ((hex m).2.2 hm).elim
  | E₆ => exact Or.inl ⟨e⟩
  | E₇ => exact Or.inr (Or.inl ⟨e⟩)
  | E₈ => exact Or.inr (Or.inr ⟨e⟩)

end SimpleGraph
