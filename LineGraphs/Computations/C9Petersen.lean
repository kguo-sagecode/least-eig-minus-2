/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Petersen

The integer vectors and SRG certificate of Example 4.9 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.9 of [CGSS]: Petersen, defined from the displayed vectors. -/
def petersen : SimpleGraph (Fin 10) := integerGraph petersenVectors 4

instance : DecidableRel petersen.Adj :=
  inferInstanceAs (DecidableRel (integerGraph petersenVectors 4).Adj)

/-- C9, Example 4.9 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem petersen_norms_checked :
    ∀ i, LineSystem.integerInner (petersenVectors i) (petersenVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.9 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem petersen_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (petersenVectors i) (petersenVectors j) = 0 ∨
      LineSystem.integerInner (petersenVectors i) (petersenVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.9 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem petersen_roots_checked : ∀ i, LineSystem.isE₈Root (petersenVectors i) = true := by
  decide +kernel

/-- C9, Example 4.9 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem petersen_isRepresentedIn_E₈ : petersen.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (petersenVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation petersenVectors 4 (1 / 2) (by norm_num)
      petersen_norms_checked petersen_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (petersen_roots_checked i)

/-- C9, Example 4.9 of [CGSS]: Petersen has parameters `(10,3,0,1)`. -/
theorem petersen_isSRGWith : petersen.IsSRGWith 10 3 0 1 := by
  exact integerGraph_isSRGWith_of_check petersenVectors 4 petersenAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
