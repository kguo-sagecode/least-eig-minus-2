/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Switching graphs

Definition `def:414-switch` and Lemma `lem:414-switch` of the blueprint for
Remark 4.14 of [CGSS]. Switching reverses adjacency across a vertex cut.
-/

namespace SimpleGraph

variable {V W : Type*} {X : SimpleGraph V} {Y : SimpleGraph W}

-- Definition (switching), for Remark 4.14 of [CGSS]
/-- Definition `def:414-switch`, Remark 4.14 of [CGSS]: reverse adjacency between
`U` and its complement, keeping adjacency within each part. -/
def switch (X : SimpleGraph V) (U : Set V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (X.Adj u v ↔ (u ∈ U ↔ v ∈ U))
  symm.symm u v h := ⟨h.1.symm, by
    exact (X.adj_comm v u).trans (h.2.trans iff_comm)⟩
  loopless.irrefl u h := h.1 rfl

instance decidableAdjSwitch (X : SimpleGraph V) (U : Set V) [DecidableEq V] [DecidableRel X.Adj]
    [DecidablePred (· ∈ U)] : DecidableRel (X.switch U).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Adjacency in the switching of Remark 4.14 of [CGSS]. -/
theorem switch_adj (X : SimpleGraph V) (U : Set V) (u v : V) :
    (X.switch U).Adj u v ↔ u ≠ v ∧ (X.Adj u v ↔ (u ∈ U ↔ v ∈ U)) := Iff.rfl

-- Lemma (switching), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-switch`, assertion 1, Remark 4.14 of [CGSS]: complementary
switching sets give the same graph (step `s414swcompl`). -/
@[simp] theorem switch_compl (X : SimpleGraph V) (U : Set V) :
    X.switch Uᶜ = X.switch U := by
  classical
  ext u v
  simp only [switch_adj, Set.mem_compl_iff, not_iff_not]

-- Lemma (switching), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-switch`, assertion 2, Remark 4.14 of [CGSS]: an isomorphism
carries a switching to the switching by the image set (step `s414swiso`). -/
def Iso.switch (e : X ≃g Y) (U : Set V) : X.switch U ≃g Y.switch (e '' U) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    change (e u ≠ e v ∧ (Y.Adj (e u) (e v) ↔ (e u ∈ e '' U ↔ e v ∈ e '' U))) ↔ _
    simp only [switch_adj, e.injective.ne_iff, Set.mem_image, e.injective.eq_iff,
      exists_eq_right, e.map_rel_iff]

-- Lemma (switching), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-switch`, assertion 3, Remark 4.14 of [CGSS]: the induced edge
map carries switched line graphs to one another (step `s414swline`). -/
def Iso.lineGraphSwitch (e : X ≃g Y) (H : Set X.edgeSet) :
    X.lineGraph.switch H ≃g Y.lineGraph.switch (e.lineGraph '' H) :=
  e.lineGraph.switch H

end SimpleGraph
