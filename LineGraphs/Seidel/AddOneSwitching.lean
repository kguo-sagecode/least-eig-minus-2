/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.AddOneRegular
import LineGraphs.Seidel.SwitchingTransport
import LineGraphs.Computations.C22

/-! # Regular switchings of T(6) with an isolated vertex

Lemma `lem:414-E7` of Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

/-- Relabel the endpoint graph while fixing the extra vertex (`lem:414-E7`). -/
def Iso.switchTriangularAddOne {n m : ℕ} {X : SimpleGraph (Fin n)}
    {Y : SimpleGraph (Fin m)} (e : X ≃g Y) :
    switchTriangularAddOne X ≃g switchTriangularAddOne Y := by
  let f := ((Iso.completeGraph e.toEquiv).lineGraph).sumCongr
    (Iso.refl : (⊥ : SimpleGraph (Fin 1)) ≃g ⊥)
  have hm (a : (⊤ : SimpleGraph (Fin n)).edgeSet ⊕ Fin 1) :
      Sum.elim (fun b ↦ b.val ∈ Y.edgeSet) (fun _ ↦ False) (f a) ↔
        Sum.elim (fun b ↦ b.val ∈ X.edgeSet) (fun _ ↦ False) a := by
    cases a with
    | inl a => exact e.map_mem_edgeSet_iff
    | inr a => rfl
  refine { toEquiv := f.toEquiv, map_rel_iff' := ?_ }
  intro u v
  change (f u ≠ f v ∧ ((triangularAddOne m).Adj (f u) (f v) ↔
    (Sum.elim (fun b ↦ b.val ∈ Y.edgeSet) (fun _ ↦ False) (f u) ↔
      Sum.elim (fun b ↦ b.val ∈ Y.edgeSet) (fun _ ↦ False) (f v)))) ↔ _
  simp only [SimpleGraph.switchTriangularAddOne, switch_adj, f.injective.ne_iff,
    show (triangularAddOne m).Adj (f u) (f v) ↔ (triangularAddOne n).Adj u v from
      f.map_adj_iff, Set.mem_ofPred_eq, hm]

/-- Excluding the extra vertex realizes a switching set as the edges of its endpoint graph
in `lem:414-E7`. -/
theorem switchTriangularAddOne_triangularSwitchingGraph {n : ℕ}
    (H : Set ((⊤ : SimpleGraph (Fin n)).edgeSet ⊕ Fin 1)) (hH : Sum.inr 0 ∉ H) :
    switchTriangularAddOne (triangularSwitchingGraph {e | Sum.inl e ∈ H}) =
      (triangularAddOne n).switch H := by
  unfold switchTriangularAddOne
  congr 1
  ext (e | u)
  · exact mem_edgeSet_triangularSwitchingGraph {e | Sum.inl e ∈ H} e
  · have hu : u = 0 := Subsingleton.elim _ _
    subst u
    simp [hH]

open Classical in
-- Lemma (regular switchings of T(6) with an isolated vertex), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-E7`, Remark 4.14: a six-regular switching of `T(6)` with an isolated
vertex is Shrikhande or the line graph of `K₄,₄`. The switching set is arbitrary. -/
theorem nonempty_iso_shrikhande_or_lineGraph_completeBipartite_of_switch_triangular6AddOne
    (H : Set ((⊤ : SimpleGraph (Fin 6)).edgeSet ⊕ Fin 1))
    (hr : ((triangularAddOne 6).switch H).IsRegularOfDegree 6) :
    Nonempty ((triangularAddOne 6).switch H ≃g shrikhande) ∨
      Nonempty ((triangularAddOne 6).switch H ≃g
        (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph) := by
  let H' := if Sum.inr 0 ∈ H then Hᶜ else H
  have hH' : Sum.inr 0 ∉ H' := by
    dsimp [H']
    split_ifs with h <;> simp [h]
  have heq : (triangularAddOne 6).switch H' = (triangularAddOne 6).switch H := by
    dsimp [H']
    split_ifs <;> simp
  let Z := triangularSwitchingGraph {e | Sum.inl e ∈ H'}
  let e : (triangularAddOne 6).switch H ≃g switchTriangularAddOne Z := by
    dsimp [Z]
    rw [switchTriangularAddOne_triangularSwitchingGraph H' hH', heq]
  have hz : (switchTriangularAddOne Z).IsRegularOfDegree 6 := by
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    exact (e.degree_eq v).trans (hr v)
  have htwo := isRegularOfDegree_two_of_switchTriangularAddOne_six Z hz
  rcases htwo.nonempty_iso_of_two_of_card_eq_six rfl with h | h
  · obtain ⟨f⟩ := h
    obtain ⟨g⟩ := Computations.C22.e7_switch_cycle6
    exact Or.inl ⟨e.trans (f.switchTriangularAddOne.trans g)⟩
  · obtain ⟨f⟩ := h
    obtain ⟨g⟩ := Computations.C22.e7_switch_twoC3
    exact Or.inr ⟨e.trans ((Iso.switchTriangularAddOne (f.trans twoC3.sumIso)).trans g)⟩

end SimpleGraph
