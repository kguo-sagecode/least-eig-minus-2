/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Integer
import Mathlib.Data.Finset.SymmDiff

/-!
# The combinatorial models for C9

The folded five-cube and the double-six model of the generalized quadrangle of
order `(2,4)`, as specified in Section 6 of `cgss/proofs/clebsch/clebsch.tex`.
These are the complements of the vector graphs in Examples 4.8 and 4.6 of [CGSS].
-/

namespace SimpleGraph

open scoped symmDiff

/-- C9, Example 4.8 of [CGSS], and `cgss/proofs/clebsch/clebsch.tex`: the folded
five-cube on even subsets, joined at symmetric difference of size four. -/
def foldedFiveCube : SimpleGraph {s : Finset (Fin 5) // Even s.card} where
  Adj s t := (s.val ∆ t.val).card = 4
  symm.symm := by intro s t h; simpa only [symmDiff_comm] using h
  loopless.irrefl := by intro s; simp

instance : DecidableRel foldedFiveCube.Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ = 4))

/-- C9, Example 4.6 of [CGSS], and `cgss/proofs/clebsch/clebsch.tex`: the double-six
graph, with labels `(0,i) = aᵢ`, `(1,i) = bᵢ`, and two-subsets `{i,j} = cᵢⱼ`. -/
def gq24 : SimpleGraph ((Fin 2 × Fin 6) ⊕ {s : Finset (Fin 6) // s.card = 2}) where
  Adj
    | .inl i, .inl j => i.1 ≠ j.1 ∧ i.2 ≠ j.2
    | .inl i, .inr s => i.2 ∈ s.val
    | .inr s, .inl i => i.2 ∈ s.val
    | .inr s, .inr t => Disjoint s.val t.val
  symm.symm := by
    rintro (i | s) (j | t)
    · exact fun h ↦ ⟨h.1.symm, h.2.symm⟩
    · exact id
    · exact id
    · exact fun h ↦ h.symm
  loopless.irrefl := by
    rintro (i | s)
    · exact fun h ↦ h.1 rfl
    · intro h
      have hs : s.val = ∅ := disjoint_self.mp h
      have := s.property
      simp [hs] at this

instance : DecidableRel gq24.Adj := by
  rintro (i | s) (j | t) <;> dsimp [gq24] <;> infer_instance

/-- C9, Example 4.8 of [CGSS]: the complement of the folded five-cube joins
even subsets at symmetric difference of size two. -/
theorem compl_foldedFiveCube_adj_iff (s t : {s : Finset (Fin 5) // Even s.card}) :
    foldedFiveCubeᶜ.Adj s t ↔ (s.val ∆ t.val).card = 2 := by
  exact (by decide +kernel : ∀ s t : {s : Finset (Fin 5) // Even s.card},
    foldedFiveCubeᶜ.Adj s t ↔ (s.val ∆ t.val).card = 2) s t

/-- C9, Example 4.6 of [CGSS]: the complement adjacency of the double-six
model, in the three types of vertex pair. -/
theorem compl_gq24_adj_iff
    (u v : (Fin 2 × Fin 6) ⊕ {s : Finset (Fin 6) // s.card = 2}) :
    gq24ᶜ.Adj u v ↔ match u, v with
      | .inl i, .inl j => i ≠ j ∧ (i.1 = j.1 ∨ i.2 = j.2)
      | .inl i, .inr s => i.2 ∉ s.val
      | .inr s, .inl i => i.2 ∉ s.val
      | .inr s, .inr t => s ≠ t ∧ ¬ Disjoint s.val t.val := by
  rcases u with i | s <;> rcases v with j | t
  · simp [SimpleGraph.compl_adj, gq24]
    tauto
  · simp [SimpleGraph.compl_adj, gq24]
  · simp [SimpleGraph.compl_adj, gq24]
  · simp [SimpleGraph.compl_adj, gq24]

end SimpleGraph
