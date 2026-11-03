/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Isomorphisms
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Recognition lemmas for LG1

The connected graph recognition steps of Lemma `lem:4-LG1`, used in
Theorem 4.13 and Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {V W : Type*} {X : SimpleGraph V} {Y : SimpleGraph W}

/-- The degree exhaustion argument for Lemma LG1, Theorem 4.13 of [CGSS]:
a finite regular graph embedded as a subgraph of a connected regular graph
of the same degree fills the whole graph. -/
theorem IsRegularOfDegree.nonempty_iso_of_injective_hom_of_connected
    [Fintype V] [Nonempty V] [Fintype W] [DecidableRel X.Adj] [DecidableRel Y.Adj]
    {k : ℕ} (hX : X.IsRegularOfDegree k) (hY : Y.IsRegularOfDegree k)
    (f : X →g Y) (hf : Function.Injective f) (hc : Y.Connected) :
    Nonempty (X ≃g Y) := by
  classical
  have hclosed {u : V} {v : W} (huv : Y.Adj (f u) v) : v ∈ Set.range f := by
    let g : X.neighborSet u → Y.neighborSet (f u) := fun w ↦ ⟨f w, f.map_adj w.property⟩
    have hg : Function.Injective g := fun w z he ↦
      Subtype.ext (hf (congrArg Subtype.val he))
    have hdeg : Fintype.card (X.neighborSet u) = Fintype.card (Y.neighborSet (f u)) := by
      rw [card_neighborSet_eq_degree, card_neighborSet_eq_degree, hX u, hY (f u)]
    have hgs := (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq hdeg)).mp hg
    obtain ⟨w, hw⟩ := hgs ⟨v, huv⟩
    exact ⟨w, congrArg Subtype.val hw⟩
  have hwalk {u v : W} (p : Y.Walk u v) : u ∈ Set.range f → v ∈ Set.range f := by
    induction p with
    | nil => exact id
    | cons hadj _ ih =>
      rintro ⟨w, rfl⟩
      exact ih (hclosed hadj)
  obtain ⟨u₀⟩ := ‹Nonempty V›
  have hs : Function.Surjective f := fun v ↦
    hwalk (hc.preconnected (f u₀) v).some ⟨u₀, rfl⟩
  exact hX.nonempty_iso_of_injective_hom hY f hf
    (Fintype.card_congr (Equiv.ofBijective f ⟨hf, hs⟩))

-- Lemma SE4 (Remark 4.14), assertion 1
/-- Assertion 1 of `res:414-SE4`, Remark 4.14 of [CGSS], also used in step
`s4lgsmall` of Lemma LG1: every finite connected graph of degree two is a cycle. -/
theorem IsRegularOfDegree.nonempty_iso_cycle
    [Fintype V] [DecidableRel X.Adj] (hr : X.IsRegularOfDegree 2) (hc : X.Connected) :
    Nonempty (X ≃g cycleGraph (Fintype.card V)) := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  have hcycles : X.IsCycles := by
    intro w _
    simpa only [Set.ncard_eq_toFinset_card', ← neighborFinset_def,
      card_neighborFinset_eq_degree] using hr w
  have hn : (X.neighborSet v).Nonempty := by
    apply (X.degree_pos_iff_exists_adj v).mp
    rw [hr v]
    omega
  obtain ⟨p, hp, _⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := X.connectedComponentMk v) (by rfl) hn
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by have := hp.three_le_length; omega)).mpr
    ⟨v, p, hp, rfl⟩
  have hm : p.length - 3 + 3 = p.length := by have := hp.three_le_length; omega
  have hreg : (cycleGraph p.length).IsRegularOfDegree 2 := by
    rw [← hm]
    exact fun _ ↦ cycleGraph_degree_three_le
  let : Nonempty (Fin p.length) := Fin.pos_iff_nonempty.mp (by
    have := hp.three_le_length
    omega)
  obtain ⟨e⟩ := hreg.nonempty_iso_of_injective_hom_of_connected hr f.toHom f.injective hc
  have he : p.length = Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
  rw [← he]
  exact ⟨e.symm⟩

/-- Step `s4lgKn` of Lemma LG1, Theorem 4.13 of [CGSS]: a connected graph
whose neighbourhoods are cliques is complete. -/
theorem Connected.eq_top_of_adj_of_common_neighbor (hc : X.Connected)
    (h : ∀ ⦃i j k⦄, X.Adj i j → X.Adj i k → j ≠ k → X.Adj j k) : X = ⊤ := by
  classical
  have hp {u v : V} (p : X.Walk u v) : u = v ∨ X.Adj u v := by
    induction p with
    | nil => exact Or.inl rfl
    | @cons u w v hadj _ ih =>
      rcases ih with rfl | hnext
      · exact Or.inr hadj
      · by_cases he : u = v
        · exact Or.inl he
        · exact Or.inr (h hadj.symm hnext he)
  exact eq_top_iff_forall_ne_adj.mpr fun u v huv ↦
    (hp (hc.preconnected u v).some).resolve_left huv

/-- The complete-bipartite recognition used in steps `s4lgbip` and `s4lgc2`
of Lemma LG1, Theorem 4.13 of [CGSS]. -/
theorem nonempty_iso_completeBipartite_of_adj_iff [Finite V]
    (P : Set V) {p q : ℕ} (hp : Nat.card P = p) (hq : Nat.card (Pᶜ : Set V) = q)
    (h : ∀ u v, X.Adj u v ↔ (u ∈ P ∧ v ∉ P) ∨ (u ∉ P ∧ v ∈ P)) :
    Nonempty (X ≃g completeBipartiteGraph (Fin p) (Fin q)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e : completeBipartiteGraph P (Pᶜ : Set V) ≃g X :=
    { toEquiv := Equiv.Set.sumCompl P
      map_rel_iff' := by
        rintro (u | u) (v | v)
        · simp [h, completeBipartiteGraph, u.property, v.property]
        · simp [h, completeBipartiteGraph, u.property, show (v : V) ∉ P from v.property]
        · simp [h, completeBipartiteGraph, v.property, show (u : V) ∉ P from u.property]
        · simp [h, completeBipartiteGraph, show (u : V) ∉ P from u.property,
            show (v : V) ∉ P from v.property] }
  let ep : P ≃ Fin p := Fintype.equivOfCardEq (by simpa using hp)
  let eq : (Pᶜ : Set V) ≃ Fin q := Fintype.equivOfCardEq (by simpa using hq)
  exact ⟨e.symm.trans (completeBipartiteGraphCongr ep eq)⟩

/-- Step `s4lgbip` of Lemma LG1, Theorem 4.13 of [CGSS]: if every neighbour
of a vertex is a leaf, connectedness makes the graph a star. -/
theorem Connected.nonempty_iso_completeBipartite_of_neighbor_degree_one
    [Fintype V] [DecidableRel X.Adj] (hc : X.Connected) (i : V)
    (hleaf : ∀ j, X.Adj i j → X.degree j = 1) :
    Nonempty (X ≃g completeBipartiteGraph (Fin 1) (Fin (X.degree i))) := by
  classical
  have hu {j l : V} (hij : X.Adj i j) (hjl : X.Adj j l) : l = i := by
    obtain ⟨w, _, hw⟩ := degree_eq_one_iff_existsUnique_adj.mp (hleaf j hij)
    exact (hw l hjl).trans (hw i hij.symm).symm
  have hp {u v : V} (p : X.Walk u v) : v = i → u = i ∨ X.Adj i u := by
    induction p with
    | nil => exact fun hv ↦ Or.inl hv
    | cons hadj _ ih =>
      intro hv
      rcases ih hv with rfl | hnext
      · exact Or.inr hadj.symm
      · exact Or.inl (hu hnext hadj.symm)
  have hall (v : V) : v = i ∨ X.Adj i v := hp (hc.preconnected v i).some rfl
  have hn : X.neighborSet i = ({i} : Set V)ᶜ := by
    ext v
    exact ⟨fun hv ↦ hv.ne.symm, fun hv ↦ (hall v).resolve_left hv⟩
  apply nonempty_iso_completeBipartite_of_adj_iff {i} (by simp)
  · rw [← hn, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  · intro u v
    simp only [Set.mem_singleton_iff]
    constructor
    · intro huv
      rcases hall u with rfl | hiu
      · exact Or.inl ⟨rfl, huv.ne.symm⟩
      · exact Or.inr ⟨hiu.ne.symm, hu hiu huv⟩
    · rintro (⟨rfl, hv⟩ | ⟨hu, rfl⟩)
      · exact (hall v).resolve_left hv
      · exact ((hall u).resolve_left hu).symm

end SimpleGraph
