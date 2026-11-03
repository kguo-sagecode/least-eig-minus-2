/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Petersen

/-!
# The Petersen isomorphism in C9

Example 4.9 of [CGSS]: the vector graph is the Kneser graph of two-subsets of a
five-set. The labels compose the permutation in `cgss/certificates/data/c09.json`
with the usual two-subset labels of the outer pentagon and inner pentagram.
-/

namespace SimpleGraph

/-- C9, Example 4.9 of [CGSS]: the Kneser graph on two-subsets of `Fin 5`. -/
def petersen.kneserGraph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := s ≠ t ∧ Disjoint s.val t.val
  symm.symm := fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := fun _ h ↦ h.1 rfl

instance : DecidableRel petersen.kneserGraph.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- C9, Example 4.9 of [CGSS]: two-subset labels for the ten integer rows. -/
def petersen.kneserLabel : Fin 10 → {s : Finset (Fin 5) // s.card = 2} :=
  ![⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩, ⟨{0, 3}, by decide⟩,
    ⟨{1, 2}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{3, 4}, by decide⟩,
    ⟨{0, 4}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{1, 4}, by decide⟩,
    ⟨{2, 4}, by decide⟩]

/-- C9, Example 4.9 of [CGSS]: the certificate identifies the vector graph
with the Kneser graph on two-subsets of a five-set. -/
noncomputable def petersen.kneserIso : petersen ≃g petersen.kneserGraph where
  toEquiv := Equiv.ofBijective petersen.kneserLabel (by decide +kernel)
  map_rel_iff' := by decide +kernel

end SimpleGraph
