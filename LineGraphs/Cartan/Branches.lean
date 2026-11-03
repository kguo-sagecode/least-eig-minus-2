/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.PathLabelling

/-!
# Branches of a tree

Deleting a vertex of a tree leaves components with exactly one attachment to
that vertex. These are the parts used in the three-arm labelling proof.
-/

namespace SimpleGraph

open Walk

variable {V : Type*} {X : SimpleGraph V} {v : V}

/-- Every component after deleting a vertex of a connected graph has an attachment to it. -/
theorem Connected.exists_neighbor_deletedComponent (hconn : X.Connected)
    (c : (X.induce {v}ᶜ).ConnectedComponent) : ∃ w : c, X.Adj v w.val.val := by
  classical
  obtain ⟨p, hp⟩ := hconn.exists_isPath v c.out.val
  have hout : c.out.val ≠ v := c.out.property
  have hnil : ¬ p.Nil := not_nil_of_ne hout.symm
  have hvw := p.adj_snd hnil
  have hn : v ∉ p.tail.support := by
    have h := hp.support_nodup
    rw [← cons_support_tail hnil, List.nodup_cons] at h
    exact h.1
  have havoid : ∀ z, z ∈ p.tail.support → z ∈ ({v}ᶜ : Set V) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hzv
    exact hn (hzv ▸ hz)
  let q' := p.tail.induce {v}ᶜ havoid
  have hwc : (⟨p.snd, havoid _ p.tail.start_mem_support⟩ : ({v}ᶜ : Set V)) ∈ c.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.sound q'.reachable).trans c.out_eq
  exact ⟨⟨⟨p.snd, havoid _ p.tail.start_mem_support⟩, hwc⟩, hvw⟩

/-- In a forest, one component after deleting a vertex has at most one attachment to it. -/
theorem IsAcyclic.eq_of_neighbor_deletedComponent (hacyc : X.IsAcyclic)
    (c : (X.induce {v}ᶜ).ConnectedComponent) (a b : c)
    (ha : X.Adj v a.val.val) (hb : X.Adj v b.val.val) : a = b := by
  classical
  obtain ⟨p, hp⟩ := c.connected_toSimpleGraph.exists_isPath a b
  let f : c.toSimpleGraph →g X := (Embedding.induce {v}ᶜ).toHom.comp c.toSimpleGraph_hom
  have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
  have hn : v ∉ (p.map f).support := by
    simp only [Walk.support_map, List.mem_map]
    rintro ⟨x, _, hx⟩
    exact x.val.property hx
  have hpath : ((p.map f).cons ha).IsPath := (hp.map hf).cons hn
  have heq := hacyc.eq_snd_of_adj_start hpath hb ((p.map f).cons ha).end_mem_support
  apply Subtype.ext
  apply Subtype.ext
  have hsnd : ((p.map f).cons ha).snd = a.val.val := by
    exact Walk.snd_cons _ _
  exact hsnd.symm.trans heq.symm

/-- Each deleted component of a tree has exactly one neighbor of the deleted vertex. -/
theorem IsTree.existsUnique_neighbor_deletedComponent (hX : X.IsTree)
    (c : (X.induce {v}ᶜ).ConnectedComponent) : ∃! w : c, X.Adj v w.val.val := by
  obtain ⟨w, hw⟩ := hX.connected.exists_neighbor_deletedComponent c
  exact ⟨w, hw, fun y hy => hX.isAcyclic.eq_of_neighbor_deletedComponent c y w hy hw⟩

/-- Components after deleting a vertex of a tree correspond to its neighbors. -/
noncomputable def IsTree.deletedComponentEquivNeighbor (hX : X.IsTree) (v : V) :
    (X.induce {v}ᶜ).ConnectedComponent ≃ X.neighborSet v := by
  classical
  let f : X.neighborSet v → (X.induce {v}ᶜ).ConnectedComponent :=
    fun w => (X.induce {v}ᶜ).connectedComponentMk ⟨w.val, w.property.ne'⟩
  apply Equiv.symm
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    let c := f a
    let a' : c := ⟨⟨a.val, a.property.ne'⟩, rfl⟩
    let b' : c := ⟨⟨b.val, b.property.ne'⟩, hab.symm⟩
    have h := hX.isAcyclic.eq_of_neighbor_deletedComponent c a' b' a.property b.property
    exact Subtype.ext (congrArg (fun x : c => x.val.val) h)
  · intro c
    obtain ⟨w, hw⟩ := hX.connected.exists_neighbor_deletedComponent c
    exact ⟨⟨w.val.val, hw⟩, w.property⟩

variable [Fintype V] [DecidableRel X.Adj]

/-- With degrees at most two away from the deleted vertex, each component is a path
whose first vertex is its unique attachment. -/
theorem IsTree.deletedComponent_path_labelling (hX : X.IsTree) (v : V)
    (hdeg : ∀ w, w ≠ v → X.degree w ≤ 2)
    (c : (X.induce {v}ᶜ).ConnectedComponent) :
    ∃ e : pathGraph (Nat.card c) ≃g c.toSimpleGraph,
      ∀ i, X.Adj v (e i).val.val ↔ i.val = 0 := by
  classical
  let _ : Fintype c := Fintype.ofFinite c
  obtain ⟨w, hw, hunique⟩ := hX.existsUnique_neighbor_deletedComponent c
  let f : Copy c.toSimpleGraph X :=
    ⟨(Embedding.induce {v}ᶜ).toHom.comp c.toSimpleGraph_hom,
      fun x y h => Subtype.ext (Subtype.ext h)⟩
  have hdegree (z : c) : c.toSimpleGraph.degree z ≤ 2 :=
    (f.degree_le z).trans (hdeg _ z.val.property)
  have hwdegree : c.toSimpleGraph.degree w ≤ 1 := by
    let g : c.toSimpleGraph.neighborSet w → X.neighborSet w.val.val :=
      fun z => ⟨z.val.val.val, z.property⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : X.neighborSet w.val.val => z.val) hab
    have hmiss : (⟨v, hw.symm⟩ : X.neighborSet w.val.val) ∉ Set.range g := by
      rintro ⟨z, hz⟩
      exact z.val.val.property (congrArg Subtype.val hz)
    have hlt := Fintype.card_lt_of_injective_of_notMem g hg hmiss
    rw [card_neighborSet_eq_degree, card_neighborSet_eq_degree] at hlt
    have hle := hdeg _ w.val.property
    omega
  have hacyc : c.toSimpleGraph.IsAcyclic := (hX.isAcyclic.induce {v}ᶜ).induce c.supp
  obtain ⟨e, he⟩ := exists_path_labelling_from c.connected_toSimpleGraph hacyc hdegree w hwdegree
  have hcard : Nat.card c = Fintype.card c := Nat.card_eq_fintype_card
  let e' : Fin (Nat.card c) ≃ c := (finCongr hcard).trans e.toEquiv
  refine ⟨{ e' with map_rel_iff' := ?_ }, ?_⟩
  · intro i j
    change c.toSimpleGraph.Adj (e (finCongr hcard i)) (e (finCongr hcard j)) ↔ _
    rw [e.map_rel_iff, pathGraph_adj, pathGraph_adj]
    rfl
  · intro i
    change X.Adj v (e (finCongr hcard i)).val.val ↔ i.val = 0
    constructor
    · intro hi
      have hh := e.injective ((hunique _ hi).trans he.symm)
      exact congrArg Fin.val hh
    · intro hi
      have hz : finCongr hcard i =
          ⟨0, Fintype.card_pos_iff.mpr c.connected_toSimpleGraph.nonempty⟩ :=
        Fin.ext hi
      rw [hz, he]
      exact hw

end SimpleGraph
