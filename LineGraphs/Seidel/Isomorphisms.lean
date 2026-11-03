/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.StarCertificates

/-!
# Isomorphisms and complements

Lemma `lem:414-iso` of the blueprint for Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

variable {V W : Type*} {X : SimpleGraph V} {Y : SimpleGraph W}

-- Lemma (isomorphisms and complements), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-iso`, assertion 1, Remark 4.14 of [CGSS]: complementing
both graphs preserves an isomorphism (step `s414isocompl`). -/
def Iso.compl (e : X ≃g Y) : Xᶜ ≃g Yᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    change (e u ≠ e v ∧ ¬ Y.Adj (e u) (e v)) ↔ u ≠ v ∧ ¬ X.Adj u v
    rw [e.injective.ne_iff, e.map_rel_iff]

-- Lemma (isomorphisms and complements), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-iso`, assertion 2, Remark 4.14 of [CGSS]: strong regularity
is preserved by isomorphism (step `s414isosrg`). -/
theorem IsSRGWith.of_iso [Fintype V] [Fintype W] [DecidableRel X.Adj]
    [DecidableRel Y.Adj] {n k a c : ℕ} (h : X.IsSRGWith n k a c) (e : X ≃g Y) :
    Y.IsSRGWith n k a c := e.isSRGWith h

/-- The degree exhaustion argument in step `s414folddisj` of Lemma
`lem:414-foldiso`, Remark 4.14 of [CGSS], in a form for an entire graph:
an injective homomorphism between equally large regular graphs of the same
degree is an isomorphism. -/
theorem IsRegularOfDegree.nonempty_iso_of_injective_hom
    [Fintype V] [Fintype W] [DecidableRel X.Adj] [DecidableRel Y.Adj] {k : ℕ}
    (hX : X.IsRegularOfDegree k) (hY : Y.IsRegularOfDegree k)
    (f : X →g Y) (hf : Function.Injective f) (hcard : Fintype.card V = Fintype.card W) :
    Nonempty (X ≃g Y) := by
  classical
  have hsurj := (Finite.injective_iff_surjective_of_equiv
    (Fintype.equivOfCardEq hcard)).mp hf
  refine ⟨{ toEquiv := Equiv.ofBijective f ⟨hf, hsurj⟩, map_rel_iff' := ?_ }⟩
  intro u v
  change Y.Adj (f u) (f v) ↔ X.Adj u v
  constructor
  · intro huv
    let g : X.neighborSet u → Y.neighborSet (f u) := fun w ↦ ⟨f w, f.map_adj w.property⟩
    have hg : Function.Injective g := fun w z he ↦
      Subtype.ext (hf (congrArg Subtype.val he))
    have hdeg : Fintype.card (X.neighborSet u) = Fintype.card (Y.neighborSet (f u)) := by
      rw [card_neighborSet_eq_degree, card_neighborSet_eq_degree, hX u, hY (f u)]
    have hgs := (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq hdeg)).mp hg
    obtain ⟨w, hw⟩ := hgs ⟨f v, huv⟩
    have hwv : (w : V) = v := hf (congrArg Subtype.val hw)
    exact hwv ▸ w.property
  · exact f.map_adj

end SimpleGraph
