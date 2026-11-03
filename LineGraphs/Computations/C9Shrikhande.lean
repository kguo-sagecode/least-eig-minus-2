/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Shrikhande

The integer vectors and SRG certificate of Example 4.7 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.7 of [CGSS]: Shrikhande, defined from the displayed vectors. -/
def shrikhande : SimpleGraph (Fin 16) := integerGraph shrikhandeVectors 4

instance : DecidableRel shrikhande.Adj :=
  inferInstanceAs (DecidableRel (integerGraph shrikhandeVectors 4).Adj)

/-- C9, Example 4.7 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem shrikhande_norms_checked :
    ∀ i, LineSystem.integerInner (shrikhandeVectors i) (shrikhandeVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.7 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem shrikhande_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (shrikhandeVectors i) (shrikhandeVectors j) = 0 ∨
      LineSystem.integerInner (shrikhandeVectors i) (shrikhandeVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.7 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem shrikhande_roots_checked : ∀ i, LineSystem.isE₈Root (shrikhandeVectors i) = true := by
  decide +kernel

/-- C9, Example 4.7 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem shrikhande_isRepresentedIn_E₈ : shrikhande.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (shrikhandeVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation shrikhandeVectors 4 (1 / 2) (by norm_num)
      shrikhande_norms_checked shrikhande_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (shrikhande_roots_checked i)

/-- C9, Example 4.7 of [CGSS]: Shrikhande has parameters `(16,6,2,2)`. -/
theorem shrikhande_isSRGWith : shrikhande.IsSRGWith 16 6 2 2 := by
  exact integerGraph_isSRGWith_of_check shrikhandeVectors 4 shrikhandeAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
