/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.Computations.StarCertificates

/-!
# Integer certificates for representations

Transfers used in C7 and C9, for Theorem 4.3 and Examples 4.5--4.9 of [CGSS].
The graphs are defined by their integer vectors, with certificates checked in the kernel.
-/

open scoped RealInnerProductSpace

namespace Computations

/-- C7 and C9, Section 4 of [CGSS]: interpret an integer row table as vectors. -/
def tableVector {n d : ℕ} (vs : List IntVector) (i : Fin n) (j : Fin d) : ℤ :=
  (vs[i.val]?.getD [])[j.val]?.getD 0

end Computations

namespace SimpleGraph

/-- C7 and C9, Section 4 of [CGSS]: the graph of integer vectors at target
inner product `q`; dividing the vectors by `√q` gives the real representation. -/
def integerGraph {n d : ℕ} (v : Fin n → Fin d → ℤ) (q : ℤ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ LineSystem.integerInner (v i) (v j) = q
  symm.symm := by
    intro i j h
    exact ⟨h.1.symm, by simpa only [LineSystem.integerInner, dotProduct_comm] using h.2⟩
  loopless.irrefl := fun _ h ↦ h.1 rfl

instance {n d : ℕ} (v : Fin n → Fin d → ℤ) (q : ℤ) :
    DecidableRel (integerGraph v q).Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- C7 and C9, Section 4 of [CGSS]: norm and pair-product certificates give
the required Gram matrix after scaling the integer coordinates. -/
theorem integerGraph_isRepresentation {n d : ℕ} (v : Fin n → Fin d → ℤ) (q : ℤ)
    (c : ℝ) (hc : c * c * (q : ℝ) = 1)
    (hn : ∀ i, LineSystem.integerInner (v i) (v i) = 2 * q)
    (hp : ∀ i j, i ≠ j →
      LineSystem.integerInner (v i) (v j) = 0 ∨ LineSystem.integerInner (v i) (v j) = q) :
    (integerGraph v q).IsRepresentation (fun i ↦ LineSystem.integerVector c (v i)) := by
  apply isRepresentation_iff.mpr
  intro i j
  rw [LineSystem.inner_integerVector]
  by_cases hij : i = j
  · subst j
    simp only [hn, Int.cast_mul, Int.cast_ofNat, ite_true]
    nlinarith [hc]
  · rcases hp i j hij with h | h
    · have hq : q ≠ 0 := by intro hz; simp [hz] at hc
      simp [integerGraph, hij, h, hq.symm]
    · simp [integerGraph, hij, h, hc]

/-- C9, Examples 4.5--4.9 of [CGSS]: a checked adjacency matrix and SRG
certificate certify the graph defined by the integer vectors. -/
theorem integerGraph_isSRGWith_of_check {n d k l m : ℕ}
    (v : Fin n → Fin d → ℤ) (q : ℤ) (A : Computations.IntMatrix)
    (hA : Computations.checkAdjacency n A = true)
    (hv : ∀ i j, (integerGraph v q).Adj i j ↔ Computations.entry A i.val j.val = 1)
    (h : Computations.checkSRG n k l m A = true) :
    (integerGraph v q).IsSRGWith n k l m := by
  let e : Computations.graphOfMatrix hA ≃g integerGraph v q :=
    { toEquiv := Equiv.refl _, map_rel_iff' := fun {i j} ↦ (hv i j) }
  exact e.isSRGWith (Computations.checkSRG_sound hA h)

end SimpleGraph
