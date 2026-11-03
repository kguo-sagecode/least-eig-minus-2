/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.RelativeBound
import LineGraphs.Representation.RootTypeClassified

/-!
# EQ2: equiangular lines spanning eight dimensions

Lemma `lem:4-EQ2` of `blueprint/sec4-leasteigenvalue.tex`, used in Theorem 4.4 of [CGSS] and
the remark after it (errata, Gap 7). The cone of `Spectral/RelativeBound.lean` is a connected
representation spanning nine dimensions; `IsRepresentation.exists_isRepresentedIn_rootType`
(step `s4eq2type`) puts it in a model of rank nine, and C20 counts the apex's neighbours.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace InnerProductSpace

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

-- Lemma EQ2
/-- Lemma EQ2 (`lem:4-EQ2`), for Theorem 4.4 of [CGSS]: unit vectors spanning a space of
dimension 8, with mutual inner products `±1/3`, number at most 14. Steps `s4eq2ip` and
`s4eq2rep` (`SimpleGraph.isRepresentation_equiangularCone`, `equiangularConeGraph_connected`,
`finrank_span_equiangularCone`), step `s4eq2type`
(`SimpleGraph.IsRepresentation.exists_isRepresentedIn_rootType`), and the count of C20
(`SimpleGraph.IsRepresentedIn.card_le_fourteen_of_equiangularCone`). -/
theorem card_le_fourteen_of_finrank_eq_eight (v : ι → E) (hv : ∀ i, ‖v i‖ = 1)
    (hpair : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 1 / 3 ∨ ⟪v i, v j⟫ = -(1 / 3))
    (hspan : span ℝ (Set.range v) = ⊤) (hdim : finrank ℝ E = 8) :
    Fintype.card ι ≤ 14 := by
  classical
  obtain ⟨t, hX, ht⟩ := (SimpleGraph.isRepresentation_equiangularCone v hv hpair)
    |>.exists_isRepresentedIn_rootType (SimpleGraph.equiangularConeGraph_connected v)
  rw [finrank_span_equiangularCone v hspan hdim] at ht
  exact hX.card_le_fourteen_of_equiangularCone ht

end InnerProductSpace
