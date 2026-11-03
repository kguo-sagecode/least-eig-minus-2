/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.LineGraphRecognition
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Small graphs of degree two

Lemma `lem:414-tworeg` of the blueprint for Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]

/-- The component-size bound used in step `s414twocomp`, Lemma
`lem:414-tworeg`, Remark 4.14 of [CGSS]: two components of a regular graph
each need at least `d + 1` vertices. -/
theorem IsRegularOfDegree.connected_of_card_lt_two_mul [Nonempty V] {d : ℕ}
    (hr : X.IsRegularOfDegree d) (hn : Fintype.card V < 2 * (d + 1)) : X.Connected := by
  classical
  refine { preconnected := ?_, nonempty := inferInstance }
  intro u v
  by_contra huv
  let S := insert u (X.neighborFinset u)
  let T := insert v (X.neighborFinset v)
  have hcardS : S.card = d + 1 := by simp [S, hr u]
  have hcardT : T.card = d + 1 := by simp [T, hr v]
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro w hwS hwT
    have hu : X.Reachable u w := by
      rcases Finset.mem_insert.mp hwS with rfl | hw
      · exact .refl _
      · exact ((X.mem_neighborFinset u w).mp hw).reachable
    have hv : X.Reachable v w := by
      rcases Finset.mem_insert.mp hwT with rfl | hw
      · exact .refl _
      · exact ((X.mem_neighborFinset v w).mp hw).reachable
    exact huv (hu.trans hv.symm)
  have hle := Finset.card_le_univ (S ∪ T)
  rw [Finset.card_union_of_disjoint hdisj, hcardS, hcardT] at hle
  omega

/-- Steps `s414twocomp` and `s414twocyc` of Lemma `lem:414-tworeg`,
Remark 4.14 of [CGSS]: a nonempty graph of degree two with fewer than six
vertices consists of a single cycle. -/
theorem IsRegularOfDegree.nonempty_iso_cycle_of_card_lt_six [Nonempty V]
    (hr : X.IsRegularOfDegree 2) (hn : Fintype.card V < 6) :
    Nonempty (X ≃g cycleGraph (Fintype.card V)) :=
  hr.nonempty_iso_cycle (hr.connected_of_card_lt_two_mul hn)

-- Lemma (2-regular graphs on five and six vertices), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-tworeg`, the five-vertex case, Remark 4.14 of [CGSS]. -/
theorem IsRegularOfDegree.nonempty_iso_cycle_of_two_of_card_eq_five
    (hr : X.IsRegularOfDegree 2) (hn : Fintype.card V = 5) :
    Nonempty (X ≃g cycleGraph 5) := by
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [← hn]
  exact hr.nonempty_iso_cycle_of_card_lt_six (by omega)

/-- The component argument shared by `lem:414-tworeg` and SE4, Remark 4.14
of [CGSS]: a disconnected graph of degree two on at most eight vertices
consists of exactly two cycles, each of length at least three. -/
theorem IsRegularOfDegree.nonempty_iso_sum_cycles_of_not_connected [Nonempty V]
    (hr : X.IsRegularOfDegree 2) (hn : Fintype.card V ≤ 8) (hc : ¬X.Connected) :
    ∃ p q, 3 ≤ p ∧ 3 ≤ q ∧ p + q = Fintype.card V ∧
      Nonempty (X ≃g (cycleGraph p) ⊕g (cycleGraph q)) := by
  classical
  have hpre : ¬X.Preconnected := fun hp ↦ hc { preconnected := hp, nonempty := inferInstance }
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬X.Reachable u v := by
    simpa only [Preconnected, not_forall] using hpre
  let P : Set V := {w | X.Reachable u w}
  have hPclosed {w z : V} (hw : w ∈ P) (hwz : X.Adj w z) : z ∈ P :=
    hw.trans hwz.reachable
  have hQclosed {w z : V} (hw : w ∈ Pᶜ) (hwz : X.Adj w z) : z ∈ Pᶜ :=
    fun hz ↦ hw (hPclosed hz hwz.symm)
  have hrP : (X.induce P).IsRegularOfDegree 2 := by
    intro w
    rw [degree_induce_of_neighborSet_subset (fun z hz ↦ hPclosed w.property hz), hr w]
  have hrQ : (X.induce Pᶜ).IsRegularOfDegree 2 := by
    intro w
    rw [degree_induce_of_neighborSet_subset (fun z hz ↦ hQclosed w.property hz), hr w]
  let : Nonempty P := ⟨⟨u, Reachable.refl _⟩⟩
  let : Nonempty (Pᶜ : Set V) := ⟨⟨v, huv⟩⟩
  have hPge : 3 ≤ Fintype.card P := by
    have hh := (X.induce P).degree_lt_card_verts ⟨u, Reachable.refl _⟩
    rw [hrP] at hh
    omega
  have hQge : 3 ≤ Fintype.card (Pᶜ : Set V) := by
    have hh := (X.induce Pᶜ).degree_lt_card_verts ⟨v, huv⟩
    rw [hrQ] at hh
    omega
  have hsum : Fintype.card P + Fintype.card (Pᶜ : Set V) = Fintype.card V := by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.Set.sumCompl P)]
  obtain ⟨ep⟩ := hrP.nonempty_iso_cycle_of_card_lt_six (by omega)
  obtain ⟨eq⟩ := hrQ.nonempty_iso_cycle_of_card_lt_six (by omega)
  let f : (X.induce P) ⊕g (X.induce Pᶜ) ≃g X :=
    { toEquiv := Equiv.Set.sumCompl P
      map_rel_iff' := by
        rintro (w | w) (z | z)
        · rfl
        · simpa [SimpleGraph.sum] using
            (iff_false_intro (fun hwz ↦ z.property (hPclosed w.property hwz)) : X.Adj w z ↔ False)
        · simpa [SimpleGraph.sum] using
            (iff_false_intro (fun hwz ↦ w.property (hPclosed z.property hwz.symm)) :
              X.Adj w z ↔ False)
        · rfl }
  exact ⟨_, _, hPge, hQge, hsum, ⟨f.symm.trans (Iso.sumCongr ep eq)⟩⟩

-- Lemma (2-regular graphs on five and six vertices), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-tworeg`, the six-vertex case, Remark 4.14 of [CGSS]:
the graph is a six-cycle or the disjoint union of two triangles. -/
theorem IsRegularOfDegree.nonempty_iso_of_two_of_card_eq_six
    (hr : X.IsRegularOfDegree 2) (hn : Fintype.card V = 6) :
    Nonempty (X ≃g cycleGraph 6) ∨ Nonempty (X ≃g (cycleGraph 3) ⊕g (cycleGraph 3)) := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_cases hc : X.Connected
  · apply Or.inl
    rw [← hn]
    exact hr.nonempty_iso_cycle hc
  obtain ⟨p, q, hp, hq, hpq, he⟩ := hr.nonempty_iso_sum_cycles_of_not_connected (by omega) hc
  have hp3 : p = 3 := by omega
  have hq3 : q = 3 := by omega
  subst p q
  exact Or.inr he

end SimpleGraph
