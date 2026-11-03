/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Data
import LineGraphs.Computations.ModelTables

/-!
# C9: Clebsch

The integer vectors and SRG certificate of Example 4.8 of [CGSS].
-/

open Computations Computations.C9

namespace SimpleGraph

set_option maxRecDepth 4000

/-- C9, Example 4.8 of [CGSS]: Clebsch, defined from the displayed vectors. -/
def clebsch : SimpleGraph (Fin 16) := integerGraph clebschVectors 4

instance : DecidableRel clebsch.Adj :=
  inferInstanceAs (DecidableRel (integerGraph clebschVectors 4).Adj)

/-- C9, Example 4.8 of [CGSS]: the doubled vectors have squared norm eight. -/
theorem clebsch_norms_checked :
    ∀ i, LineSystem.integerInner (clebschVectors i) (clebschVectors i) = 8 := by
  decide +kernel

/-- C9, Example 4.8 of [CGSS]: the off-diagonal integer products are zero or four. -/
theorem clebsch_products_checked : ∀ i j, i ≠ j →
    LineSystem.integerInner (clebschVectors i) (clebschVectors j) = 0 ∨
      LineSystem.integerInner (clebschVectors i) (clebschVectors j) = 4 := by
  decide +kernel

/-- C9, Example 4.8 of [CGSS]: all vectors decode as roots of `E₈`. -/
theorem clebsch_roots_checked : ∀ i, LineSystem.isE₈Root (clebschVectors i) = true := by
  decide +kernel

/-- C9, Example 4.8 of [CGSS]: the vector graph is represented in `E₈`. -/
theorem clebsch_isRepresentedIn_E₈ : clebsch.IsRepresentedIn LineSystem.E₈ := by
  refine ⟨fun i ↦ LineSystem.integerVector (1 / 2) (clebschVectors i), ?_, ?_⟩
  · exact integerGraph_isRepresentation clebschVectors 4 (1 / 2) (by norm_num)
      clebsch_norms_checked clebsch_products_checked
  · intro i
    exact (LineSystem.integerVector_mem_E₈_iff _).mpr (clebsch_roots_checked i)

/-- C9, Example 4.8 of [CGSS]: Clebsch has parameters `(16,10,6,6)`. -/
theorem clebsch_isSRGWith : clebsch.IsSRGWith 16 10 6 6 := by
  exact integerGraph_isSRGWith_of_check clebschVectors 4 clebschAdj
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end SimpleGraph
