/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Chang I

The integer vectors and SRG certificate of Example 4.5 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.5 of [CGSS]: Chang I, defined from the displayed vectors. -/
def changI : SimpleGraph (Fin 28) := integerGraph changIVectors 4

instance : DecidableRel changI.Adj :=
  inferInstanceAs (DecidableRel (integerGraph changIVectors 4).Adj)

/-- C9, Example 4.5 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem changI_norms_checked :
    ∀ i, LineSystem.integerInner (changIVectors i) (changIVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem changI_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (changIVectors i) (changIVectors j) = 0 ∨
      LineSystem.integerInner (changIVectors i) (changIVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem changI_roots_checked : ∀ i, LineSystem.isE₈Root (changIVectors i) = true := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem changI_isRepresentedIn_E₈ : changI.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (changIVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation changIVectors 4 (1 / 2) (by norm_num)
      changI_norms_checked changI_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (changI_roots_checked i)

/-- C9, Example 4.5 of [CGSS]: Chang I has parameters `(28,12,6,4)`. -/
theorem changI_isSRGWith : changI.IsSRGWith 28 12 6 4 := by
  exact integerGraph_isSRGWith_of_check changIVectors 4 changIAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
