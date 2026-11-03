/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Chang II

The integer vectors and SRG certificate of Example 4.5 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.5 of [CGSS]: Chang II, defined from the displayed vectors. -/
def changII : SimpleGraph (Fin 28) := integerGraph changIIVectors 4

instance : DecidableRel changII.Adj :=
  inferInstanceAs (DecidableRel (integerGraph changIIVectors 4).Adj)

/-- C9, Example 4.5 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem changII_norms_checked :
    ∀ i, LineSystem.integerInner (changIIVectors i) (changIIVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem changII_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (changIIVectors i) (changIIVectors j) = 0 ∨
      LineSystem.integerInner (changIIVectors i) (changIIVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem changII_roots_checked : ∀ i, LineSystem.isE₈Root (changIIVectors i) = true := by
  decide +kernel

/-- C9, Example 4.5 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem changII_isRepresentedIn_E₈ : changII.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (changIIVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation changIIVectors 4 (1 / 2) (by norm_num)
      changII_norms_checked changII_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (changII_roots_checked i)

/-- C9, Example 4.5 of [CGSS]: Chang II has parameters `(28,12,6,4)`. -/
theorem changII_isSRGWith : changII.IsSRGWith 28 12 6 4 := by
  exact integerGraph_isSRGWith_of_check changIIVectors 4 changIIAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
