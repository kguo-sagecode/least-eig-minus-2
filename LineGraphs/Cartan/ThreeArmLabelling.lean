/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Branches
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Recognition of three-armed trees

`lem:arm-labelling` of the Remark 3.11 blueprint. The three positive arm lengths
are sorted, and the graph isomorphism sends the specified centre to `none` in reverse.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {X : SimpleGraph V} [DecidableRel X.Adj]

/-- A finite tree with one vertex of degree three and all others of degree at most two
has a three-arm labelling, with positive lengths in increasing order. -/
theorem exists_three_arm_labelling (hconn : X.Connected) (hacyc : X.IsAcyclic)
    (v : V) (hv : X.degree v = 3) (hdeg : ∀ w, w ≠ v → X.degree w ≤ 2) :
    ∃ a : Fin 3 → ℕ, (∀ r, 0 < a r) ∧ Monotone a ∧
      ∃ e : armTree a ≃g X, e none = v := by
  classical
  let hX : X.IsTree := ⟨hconn, hacyc⟩
  let Y := X.induce {v}ᶜ
  let ec : Fin 3 ≃ Y.ConnectedComponent :=
    (Fintype.equivFinOfCardEq ((X.card_neighborSet_eq_degree v).trans hv)).symm.trans
      (hX.deletedComponentEquivNeighbor v).symm
  let lengths : Fin 3 → ℕ := fun r => Nat.card (ec r)
  let cs : Fin 3 ≃ Y.ConnectedComponent := (Tuple.sort lengths).trans ec
  let a : Fin 3 → ℕ := fun r => Nat.card (cs r)
  have hpos (r : Fin 3) : 0 < a r := by
    have : Nonempty (cs r) := (cs r).connected_toSimpleGraph.nonempty
    exact Nat.card_pos
  have hmono : Monotone a := Tuple.monotone_sort lengths
  have hlabel (r : Fin 3) := hX.deletedComponent_path_labelling v hdeg (cs r)
  choose es hes using hlabel
  let f : ArmVertex a → V
    | none => v
    | some ⟨r, i⟩ => (es r i).val.val
  have hcomp (r : Fin 3) (i : Fin (a r)) :
      Y.connectedComponentMk (es r i).val = cs r := (es r i).property
  have hne (r : Fin 3) (i : Fin (a r)) : (es r i).val.val ≠ v := (es r i).val.property
  have hinj : Function.Injective f := by
    rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩) h
    · rfl
    · exact (hne s j h.symm).elim
    · exact (hne r i h).elim
    · have hvtx : (es r i).val = (es s j).val := Subtype.ext h
      have hrs : r = s := cs.injective (by rw [← hcomp r i, ← hcomp s j, hvtx])
      subst s
      have hij : i = j := (es r).injective (Subtype.ext hvtx)
      subst j
      rfl
  have hsurj : Function.Surjective f := by
    intro x
    by_cases hx : x = v
    · exact ⟨none, hx.symm⟩
    · let x' : ({v}ᶜ : Set V) := ⟨x, hx⟩
      let r := cs.symm (Y.connectedComponentMk x')
      have hxr : x' ∈ (cs r).supp := by
        rw [ConnectedComponent.mem_supp_iff]
        exact (cs.apply_symm_apply _).symm
      let z : cs r := ⟨x', hxr⟩
      refine ⟨some ⟨r, (es r).symm z⟩, ?_⟩
      change ((es r) ((es r).symm z)).val.val = x
      rw [(es r).apply_symm_apply]
  let e : ArmVertex a ≃ V := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨a, hpos, hmono, { e with map_rel_iff' := ?_ }, rfl⟩
  rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩)
  · change X.Adj v v ↔ False
    simp
  · exact hes s j
  · change X.Adj (es r i).val.val v ↔ i.val = 0
    rw [X.adj_comm]
    exact hes r i
  · change X.Adj (es r i).val.val (es s j).val.val ↔
      r = s ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    constructor
    · intro hij
      have hc : Y.connectedComponentMk (es r i).val = Y.connectedComponentMk (es s j).val :=
        ConnectedComponent.sound (show Y.Adj (es r i).val (es s j).val from hij).reachable
      have hrs : r = s := cs.injective (by rwa [hcomp, hcomp] at hc)
      subst s
      refine ⟨rfl, ?_⟩
      apply pathGraph_adj.mp
      exact (es r).map_rel_iff.mp hij
    · rintro ⟨rfl, hij⟩
      exact (es r).map_rel_iff.mpr (pathGraph_adj.mpr hij)

end SimpleGraph
