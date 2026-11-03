/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SwitchingModels

/-!
# Relabelling triangular switching sets

The relabelling and complementation steps of `lem:414-E6` and `lem:414-E8`
in Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

/-- Relabel the switching graph and the complete graph together, as in `lem:414-switch`. -/
def Iso.switchTriangular {n m : ℕ} {X : SimpleGraph (Fin n)} {Y : SimpleGraph (Fin m)}
    (e : X ≃g Y) : switchTriangular X ≃g switchTriangular Y := by
  let f := (Iso.completeGraph e.toEquiv).lineGraph
  refine { toEquiv := f.toEquiv, map_rel_iff' := ?_ }
  intro u v
  have hm (a : (⊤ : SimpleGraph (Fin n)).edgeSet) :
      (f a).val ∈ Y.edgeSet ↔ a.val ∈ X.edgeSet := e.map_mem_edgeSet_iff
  change (f u ≠ f v ∧ ((⊤ : SimpleGraph (Fin m)).lineGraph.Adj (f u) (f v) ↔
    ((f u).val ∈ Y.edgeSet ↔
    (f v).val ∈ Y.edgeSet))) ↔ _
  simp only [SimpleGraph.switchTriangular, switch_adj, f.injective.ne_iff, f.map_adj_iff,
    Set.mem_ofPred_eq, hm]

/-- Complementary edge sets give the same triangular switching (`lem:414-E8`). -/
theorem switchTriangular_compl {n : ℕ} (Z : SimpleGraph (Fin n)) :
    switchTriangular Zᶜ = switchTriangular Z := by
  have he : {e : (⊤ : SimpleGraph (Fin n)).edgeSet | e.val ∈ Zᶜ.edgeSet} =
      {e : (⊤ : SimpleGraph (Fin n)).edgeSet | e.val ∈ Z.edgeSet}ᶜ := by
    ext e
    have hn := e.property
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ i j =>
      have hij : i ≠ j := by simpa using hn
      simp [compl_adj, hij]
  simp only [switchTriangular, he, switch_compl]

/-- Regard an arbitrary cut of a triangular graph as edges of a graph on its endpoints (4.14). -/
def triangularSwitchingGraph {n : ℕ} (H : Set (⊤ : SimpleGraph (Fin n)).edgeSet) :
    SimpleGraph (Fin n) := fromEdgeSet (Subtype.val '' H)

/-- The arbitrary cut is recovered from its endpoint graph in `lem:414-E6` and `lem:414-E8`. -/
theorem mem_edgeSet_triangularSwitchingGraph {n : ℕ}
    (H : Set (⊤ : SimpleGraph (Fin n)).edgeSet) (e : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    e.val ∈ (triangularSwitchingGraph H).edgeSet ↔ e ∈ H := by
  have hn : ¬ e.val.IsDiag := by simpa using e.property
  simp only [triangularSwitchingGraph, edgeSet_fromEdgeSet, Set.mem_sdiff,
    Set.mem_image, Sym2.mem_diagSet, hn, not_false_eq_true, and_true]
  constructor
  · rintro ⟨a, ha, he⟩
    exact (Subtype.ext he : a = e) ▸ ha
  · exact fun h ↦ ⟨e, h, rfl⟩

/-- Every cut occurs in the graph-parametrized formulation of the regular-switching lemmas. -/
theorem switchTriangular_triangularSwitchingGraph {n : ℕ}
    (H : Set (⊤ : SimpleGraph (Fin n)).edgeSet) :
    switchTriangular (triangularSwitchingGraph H) =
      (⊤ : SimpleGraph (Fin n)).lineGraph.switch H := by
  unfold switchTriangular
  congr 1
  ext e
  exact mem_edgeSet_triangularSwitchingGraph H e

end SimpleGraph
