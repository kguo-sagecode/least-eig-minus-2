/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Models
import LineGraphs.Computations.C9Clebsch
import LineGraphs.Computations.C9Schlafli

/-!
# The two model isomorphisms of C9

Certificates from `cgss/proofs/clebsch/checks/clebsch_check.sage`, Section 6 of the
Clebsch note, for Examples 4.6 and 4.8 of [CGSS]. The closed-form labels in that
script are transcribed here and checked for bijectivity and every adjacency.
-/

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.8 of [CGSS]: the closed-form even-subset certificate. -/
def clebsch.subsetLabel : Fin 16 → Finset (Fin 5) :=
  ![∅, {2, 3}, {2, 4}, {3, 4},
    {0, 1}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4},
    {0, 2, 3, 4}, {0, 4}, {0, 3}, {0, 2},
    {1, 2, 3, 4}, {1, 4}, {1, 3}, {1, 2}]

/-- C9, Example 4.8 of [CGSS]: all labels in the certificate have even size. -/
theorem clebsch.even_subsetLabel : ∀ i, Even (clebsch.subsetLabel i).card := by
  decide +kernel

/-- C9, Example 4.8 of [CGSS]: the certificate as a map to the model vertices. -/
def clebsch.foldedFiveCubeLabel (i : Fin 16) : {s : Finset (Fin 5) // Even s.card} :=
  ⟨clebsch.subsetLabel i, clebsch.even_subsetLabel i⟩

/-- C9, Example 4.8 of [CGSS]: the vector Clebsch graph is isomorphic to
the complement of the folded five-cube. -/
noncomputable def clebsch.foldedFiveCubeComplIso : clebsch ≃g foldedFiveCubeᶜ where
  toEquiv := Equiv.ofBijective clebsch.foldedFiveCubeLabel (by decide +kernel)
  map_rel_iff' := by decide +kernel

/-- C9, Example 4.8 of [CGSS], and SE2: the folded five-cube has parameters `(16,5,0,2)`. -/
theorem foldedFiveCube_isSRGWith : foldedFiveCube.IsSRGWith 16 5 0 2 := by
  simpa using (clebsch.foldedFiveCubeComplIso.isSRGWith clebsch_isSRGWith).compl

/-- C9, Example 4.6 of [CGSS]: the double-six labels of the vector rows. -/
def schlafli.gq24Label :
    Fin 27 → (Fin 2 × Fin 6) ⊕ {s : Finset (Fin 6) // s.card = 2} :=
  ![.inr ⟨{0, 1}, by decide⟩,
    .inr ⟨{0, 2}, by decide⟩,
    .inr ⟨{0, 3}, by decide⟩,
    .inr ⟨{0, 4}, by decide⟩,
    .inr ⟨{0, 5}, by decide⟩,
    .inr ⟨{1, 2}, by decide⟩,
    .inr ⟨{1, 3}, by decide⟩,
    .inr ⟨{1, 4}, by decide⟩,
    .inr ⟨{1, 5}, by decide⟩,
    .inr ⟨{2, 3}, by decide⟩,
    .inr ⟨{2, 4}, by decide⟩,
    .inr ⟨{2, 5}, by decide⟩,
    .inr ⟨{3, 4}, by decide⟩,
    .inr ⟨{3, 5}, by decide⟩,
    .inr ⟨{4, 5}, by decide⟩,
    .inl (0, 0),
    .inl (0, 1),
    .inl (0, 2),
    .inl (0, 3),
    .inl (0, 4),
    .inl (0, 5),
    .inl (1, 0),
    .inl (1, 1),
    .inl (1, 2),
    .inl (1, 3),
    .inl (1, 4),
    .inl (1, 5)]

/-- C9, Example 4.6 of [CGSS]: the vector Schläfli graph is isomorphic to
the complement of the double-six model of the generalized quadrangle `(2,4)`. -/
noncomputable def schlafli.gq24ComplIso : schlafli ≃g gq24ᶜ where
  toEquiv := Equiv.ofBijective schlafli.gq24Label (by decide +kernel)
  map_rel_iff' := by decide +kernel

/-- C9, Example 4.6 of [CGSS], and SE3: the double-six graph has parameters `(27,10,1,5)`. -/
theorem gq24_isSRGWith : gq24.IsSRGWith 27 10 1 5 := by
  simpa using (schlafli.gq24ComplIso.isSRGWith schlafli_isSRGWith).compl

end SimpleGraph
