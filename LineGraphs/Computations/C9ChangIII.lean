/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Chang III

The integer vectors and SRG certificate of Example 4.5 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.5 of [CGSS]: Chang III, defined from the displayed vectors. -/
def changIII : SimpleGraph (Fin 28) := integerGraph changIIIVectors 4

instance : DecidableRel changIII.Adj :=
  inferInstanceAs (DecidableRel (integerGraph changIIIVectors 4).Adj)

/-- C9, Example 4.5 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem changIII_norms_checked :
    ∀ i, LineSystem.integerInner (changIIIVectors i) (changIIIVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem changIII_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (changIIIVectors i) (changIIIVectors j) = 0 ∨
      LineSystem.integerInner (changIIIVectors i) (changIIIVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem changIII_roots_checked : ∀ i, LineSystem.isE₈Root (changIIIVectors i) = true := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem changIII_isRepresentedIn_E₈ : changIII.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (changIIIVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation changIIIVectors 4 (1 / 2) (by norm_num)
      changIII_norms_checked changIII_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (changIII_roots_checked i)

/-- C9, Example 4.5 of [CGSS]: Chang III has parameters `(28,12,6,4)`. -/
theorem changIII_isSRGWith : changIII.IsSRGWith 28 12 6 4 := by
  exact integerGraph_isSRGWith_of_check changIIIVectors 4 changIIIAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
