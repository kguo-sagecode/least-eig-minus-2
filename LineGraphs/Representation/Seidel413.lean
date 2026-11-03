/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.HoffmanRegular
import LineGraphs.Seidel.LineGraph

/-!
# Seidel's theorem

Theorem 4.13 of [CGSS], `thm:4.13` in the Section 4 blueprint, and assertion 3
of `rem:4-large`. The explicit eigenvalue hypothesis retains the literal printed
statement; errata Implicit hypothesis 2 discusses this reading.
The imported line-graph recognition includes the repairs of Gap 9 and Error 7;
the regular E₈ bounds used in the large-graph corollary incorporate Error 15.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {n k a c : ℕ}

-- Theorem 4.13
/-- Theorem 4.13 of [CGSS], `thm:4.13`: a connected strongly regular graph
with least eigenvalue minus two is a complete-graph line graph, a balanced
complete-bipartite line graph, a cocktail party graph, or is represented in E₈.
The hypotheses `hp` and `hneg` express the literal printed condition, equivalently
`X.leastEigenvalue = -2` by `leastEigenvalue_eq_neg_two_iff` and
`neg_two_mem_spectrumMultiset_iff_det_eq_zero`. Unlike the strengthened lower-bound
forms of Theorems 4.10 and 4.11, this statement requires the eigenvalue to occur
(errata, Implicit hypothesis 2 is a note on the reading, not a repair to the paper). -/
theorem seidel (hc : X.Connected) (h : X.IsSRGWith n k a c)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hneg : (-2 : ℝ) ∈ X.spectrumMultiset) :
    (∃ m, Nonempty (X ≃g (completeGraph (Fin m)).lineGraph)) ∨
      (∃ m, Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph)) ∨
      (∃ m, Nonempty (X ≃g cocktailParty m)) ∨ X.IsRepresentedIn LineSystem.E₈ := by
  classical
  -- Step `s413hrc`: apply Theorem 4.11 to the regular graph.
  rcases hoffman_rayChaudhuri hc h.regular hp with ⟨m, Y, ⟨e⟩⟩ | hCP | hE
  · -- Steps `s413Y` and `s413Kn`: remove isolated root vertices and apply LG1.
    -- The cycle case uses the SRG relation k - 2a + c = 4 to force c = 2.
    have hdet := X.neg_two_mem_spectrumMultiset_iff_det_eq_zero.mp hneg
    obtain ⟨l, _, hl⟩ :=
      h.nonempty_iso_lineGraph_complete_or_completeBipartite hc hdet e
    rcases hl with hl | hl
    · exact Or.inl ⟨l, hl⟩
    · exact Or.inr (Or.inl ⟨l, hl⟩)
  · exact Or.inr (Or.inr (Or.inl hCP))
  · exact Or.inr (Or.inr (Or.inr hE))

-- Remark after the examples in Section 4
/-- The remark after the examples in Section 4 of [CGSS] (blueprint `rem:4-large`,
assertion 3), step `s4lrthree`: in
Theorem 4.13 the exceptional alternative is excluded when the order exceeds
28 or the valency exceeds 16. Theorem 4.4 is used with errata Error 15 repaired. -/
theorem seidel_of_large (hc : X.Connected) (h : X.IsSRGWith n k a c)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hneg : (-2 : ℝ) ∈ X.spectrumMultiset)
    (hlarge : 28 < Fintype.card V ∨ 16 < k) :
    (∃ m, Nonempty (X ≃g (completeGraph (Fin m)).lineGraph)) ∨
      (∃ m, Nonempty (X ≃g (completeBipartiteGraph (Fin m) (Fin m)).lineGraph)) ∨
      ∃ m, Nonempty (X ≃g cocktailParty m) := by
  let : Nonempty V := hc.nonempty
  rcases seidel hc h hp hneg with hK | hB | hCP | hE
  · exact Or.inl hK
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr hCP)
  · have hn := hE.card_le_28_of_regular h.regular
    have hd := hE.degree_le_16_of_regular h.regular
    omega

end SimpleGraph
