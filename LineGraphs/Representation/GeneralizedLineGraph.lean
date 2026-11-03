/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.LineGraph
import LineGraphs.LineSystem.Models

/-!
# Cocktail party graphs and generalized line graphs

Definitions `def:CP` and `def:glg` before Theorem 4.2 of [CGSS]. Petals are labelled
by a vertex, an index in `Fin (a i)`, and a Boolean sign.
-/

open scoped RealInnerProductSpace

namespace SimpleGraph

/-- Definition `def:CP` before Theorem 4.2 of [CGSS]: the cocktail party graph on `2m`
vertices, with the two vertices of each matched pair nonadjacent. -/
def cocktailParty (m : ℕ) : SimpleGraph (Fin m × Bool) where
  Adj u v := u.1 ≠ v.1
  symm.symm _ _ := Ne.symm
  loopless.irrefl _ := not_not_intro rfl

instance (m : ℕ) : DecidableRel (cocktailParty m).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- Definition `def:glg` before Theorem 4.2 of [CGSS]: edges and signed petals. -/
abbrev GeneralizedLineGraphVertex {V : Type*} (Y : SimpleGraph V) (a : V → ℕ) :=
  Y.edgeSet ⊕ ((i : V) × (Fin (a i) × Bool))

/-- Definition `def:glg` before Theorem 4.2 of [CGSS]: attach `CP(a i)` at the edges
incident to each vertex `i` of `Y`. -/
def generalizedLineGraph {V : Type*} (Y : SimpleGraph V) (a : V → ℕ) :
    SimpleGraph (GeneralizedLineGraphVertex Y a) where
  Adj
    | .inl e, .inl f => Y.lineGraph.Adj e f
    | .inl e, .inr p => p.1 ∈ (e : Sym2 V)
    | .inr p, .inl e => p.1 ∈ (e : Sym2 V)
    | .inr p, .inr q => p.1 = q.1 ∧ p.2.1.val ≠ q.2.1.val
  symm.symm := by
    rintro (e | p) (f | q)
    · exact Adj.symm
    · exact id
    · exact id
    · exact fun h ↦ ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := by
    rintro (e | p)
    · exact Y.lineGraph.loopless.irrefl e
    · exact fun h ↦ h.2 rfl

noncomputable instance {V : Type*} (Y : SimpleGraph V) (a : V → ℕ) :
    DecidableRel (generalizedLineGraph Y a).Adj := Classical.decRel _

/-- Definition `def:glg` before Theorem 4.2 of [CGSS]: being isomorphic to one of
the explicitly constructed finite generalized line graphs. -/
def IsGeneralizedLineGraph {V : Type*} (X : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (Y : SimpleGraph (Fin m)) (a : Fin m → ℕ),
    Nonempty (X ≃g generalizedLineGraph Y a)

end SimpleGraph
