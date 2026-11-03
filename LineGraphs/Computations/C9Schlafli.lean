/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Schlaefli

The integer vectors and SRG certificate of Example 4.6 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.6 of [CGSS]: Schlaefli, defined from the displayed vectors. -/
def schlafli : SimpleGraph (Fin 27) := integerGraph schlafliVectors 4

instance : DecidableRel schlafli.Adj :=
  inferInstanceAs (DecidableRel (integerGraph schlafliVectors 4).Adj)

/-- C9, Example 4.6 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem schlafli_norms_checked :
    ∀ i, LineSystem.integerInner (schlafliVectors i) (schlafliVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.6 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem schlafli_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (schlafliVectors i) (schlafliVectors j) = 0 ∨
      LineSystem.integerInner (schlafliVectors i) (schlafliVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.6 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem schlafli_roots_checked : ∀ i, LineSystem.isE₈Root (schlafliVectors i) = true := by
  decide +kernel

/-- C9, Example 4.6 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem schlafli_isRepresentedIn_E₈ : schlafli.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (schlafliVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation schlafliVectors 4 (1 / 2) (by norm_num)
      schlafli_norms_checked schlafli_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (schlafli_roots_checked i)

/-- C9, Example 4.6 of [CGSS]: Schlaefli has parameters `(27,16,10,8)`. -/
theorem schlafli_isSRGWith : schlafli.IsSRGWith 27 16 10 8 := by
  exact integerGraph_isSRGWith_of_check schlafliVectors 4 schlafliAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
