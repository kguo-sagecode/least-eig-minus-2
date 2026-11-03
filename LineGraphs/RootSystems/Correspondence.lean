/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Decomposition
import Mathlib.Tactic.TFAE

/-!
# Theorem 3.10 of [CGSS]

The settled declaration is `LineSystem.isRootSet_tfae` (`cgss/notation.md`, §10).
The three clauses are the root-set predicate of Definition 3.9, star closure, and a
finite orthogonal sum of the A/D/E models. A bundled line system already contains the
angle and both-sign conditions; `isRootSet_tfae_of_inner_self_eq_two` gives the statement
for an arbitrary spanning set of vectors of squared norm two as well.

The current blueprint contains Definition 3.9 and the bridge in `sec3-remark311.tex`
but no statement or Lamport proof of Theorem 3.10. We follow the corrected paper's
three clauses, including decomposable systems, using Theorem 3.5 (`thm:3.5`).
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS]: for a spanning line system, the roots form a Root System
of Definition 3.9, the system is star-closed, and it is an orthogonal sum of A/D/E models
are equivalent. The two implications through angles and reflections are in
`isRootSet_iff_isStarClosed`; the decomposition uses Theorem 3.5 (`thm:3.5`). -/
theorem isRootSet_tfae (S : LineSystem V) (hspan : span ℝ S.Φ = ⊤) :
    List.TFAE [IsRootSet S.Φ, S.IsStarClosed, S.IsOrthogonalSumOfModels] := by
  tfae_have 1 ↔ 2 := S.isRootSet_iff_isStarClosed hspan
  tfae_have 2 ↔ 3 :=
    ⟨IsStarClosed.isOrthogonalSumOfModels, IsOrthogonalSumOfModels.isStarClosed⟩
  tfae_finish

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS] on an arbitrary spanning set of vectors of squared norm two:
the angle condition is included in the existence of a `LineSystem` on precisely these
roots. This exposes the full (i) ↔ (ii) ↔ (iii), without presupposing the allowed angles. -/
theorem isRootSet_tfae_of_inner_self_eq_two (Φ : Set V)
    (h₂ : ∀ r ∈ Φ, ⟪r, r⟫ = 2) (hspan : span ℝ Φ = ⊤) :
    List.TFAE [IsRootSet Φ,
      ∃ S : LineSystem V, S.Φ = Φ ∧ S.IsStarClosed,
      ∃ S : LineSystem V, S.Φ = Φ ∧ S.IsOrthogonalSumOfModels] := by
  tfae_have 1 → 2 := fun h ↦ ⟨h.toLineSystem h₂, rfl, h.isStarClosed_toLineSystem h₂⟩
  tfae_have 2 → 1 := by
    rintro ⟨S, hS, hSC⟩
    exact hS ▸ hSC.isRootSet (hS.symm ▸ hspan)
  tfae_have 2 → 3 := by
    rintro ⟨S, hS, hSC⟩
    exact ⟨S, hS, hSC.isOrthogonalSumOfModels⟩
  tfae_have 3 → 2 := by
    rintro ⟨S, hS, hsum⟩
    exact ⟨S, hS, hsum.isStarClosed⟩
  tfae_finish

-- Theorem 3.10
/-- The indecomposable specialization of Theorem 3.10 of [CGSS], combined with
Theorem 3.5 (`thm:3.5`): the A/D/E type is unique. -/
theorem isRootSet_and_isIndecomposable_iff (S : LineSystem V) (hne : S.Φ.Nonempty)
    (hspan : span ℝ S.Φ = ⊤) :
    IsRootSet S.Φ ∧ S.IsIndecomposable ↔ ∃! t : RootType, Nonempty (S.Iso t.model) := by
  rw [S.isRootSet_iff_isStarClosed hspan, and_comm, S.classification hne]

end LineSystem
