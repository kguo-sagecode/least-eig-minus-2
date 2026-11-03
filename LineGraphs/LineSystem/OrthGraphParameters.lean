/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.TriangleProperty
import LineGraphs.Graphs.TrianglePropertyIso

/-! # The orthogonality-graph parameters in [CGSS, Lemma 2.10] -/

namespace LineSystem.Hyp24

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] (H : Hyp24 V)

-- Lemma 2.10
/-- Step 210apply of `lem:2.10` ([CGSS, Lemma 2.10]): the strongly regular parameters
are `(6k-3,2k,1,k)`, for `k ∈ {2,3,5}`. Giving all four parameters repairs errata Error 12.
The redundant noncompleteness hypothesis is retained to match the paper; it follows
from `hedge` and `hn`. -/
theorem orthGraph_isSRGWith
    (hedge : ∃ x y, H.orthGraph.Adj x y) (_hnc : H.orthGraph ≠ ⊤)
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬H.orthGraph.Adj x y) :
    ∃ k ∈ ({2, 3, 5} : Set ℕ), H.orthGraph.IsSRGWith (6 * k - 3) (2 * k) 1 k := by
  classical
  obtain ⟨u, v, huv⟩ := hedge
  obtain ⟨w, hwu, hnuw⟩ := hn u
  have F := H.orthGraph_hasTriangleProperty.normal_form_of_not_forall_adj
    ⟨u, v, huv⟩ hn hwu.symm hnuw
  exact ⟨_, F.card_common, F.isSRGWith⟩

-- Lemma 2.10
/-- Step 210apply of `lem:2.10` ([CGSS, Lemma 2.10]): outside the friendship family,
the order of the orthogonality graph is one of `9,15,27`. -/
theorem card_Γa_mem
    (hedge : ∃ x y, H.orthGraph.Adj x y) (hnc : H.orthGraph ≠ ⊤)
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬H.orthGraph.Adj x y) :
    H.Γa.ncard ∈ ({9, 15, 27} : Set ℕ) := by
  obtain ⟨k, hk, hreg⟩ := H.orthGraph_isSRGWith hedge hnc hn
  have hcard := hreg.card
  rw [Set.fintypeCard_eq_ncard] at hcard
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk ⊢
  rcases hk with rfl | rfl | rfl <;> omega

-- Lemma 2.10
/-- Step 210unique of `lem:2.10` ([CGSS, Lemma 2.10]): two instances outside the
friendship family with equal `|Γa|` have isomorphic orthogonality graphs.
The noncompleteness hypotheses are retained to match the paper; the edge and
nonadjacency hypotheses already imply them. -/
theorem orthGraph_iso_of_card_Γa_eq
    (H' : Hyp24 W) (hedge : ∃ x y, H.orthGraph.Adj x y)
    (hedge' : ∃ x y, H'.orthGraph.Adj x y)
    (_hnc : H.orthGraph ≠ ⊤) (_hnc' : H'.orthGraph ≠ ⊤)
    (hn : ∀ x, ∃ y, y ≠ x ∧ ¬H.orthGraph.Adj x y)
    (hn' : ∀ x, ∃ y, y ≠ x ∧ ¬H'.orthGraph.Adj x y)
    (hcard : H.Γa.ncard = H'.Γa.ncard) :
    Nonempty (H.orthGraph ≃g H'.orthGraph) :=
  H.orthGraph_hasTriangleProperty.nonempty_iso_of_card_eq
    H'.orthGraph_hasTriangleProperty hedge hedge' hn hn'
      (by simpa only [Set.fintypeCard_eq_ncard] using hcard)

end LineSystem.Hyp24
