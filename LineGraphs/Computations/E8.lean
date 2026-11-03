/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.E8Rows00
import LineGraphs.Computations.E8Rows01
import LineGraphs.Computations.E8Rows02
import LineGraphs.Computations.E8Rows03
import LineGraphs.Computations.E8Rows04
import LineGraphs.Computations.E8Rows05
import LineGraphs.Computations.E8Rows06
import LineGraphs.Computations.E8Rows07
import LineGraphs.Computations.E8Rows08
import LineGraphs.Computations.E8Rows09
import LineGraphs.Computations.E8Rows10
import LineGraphs.Computations.E8Rows11
import LineGraphs.Computations.ModelTables
import LineGraphs.LineSystem.ModelSpans
import LineGraphs.LineSystem.ClassicalModels

/-!
# Certified star-closure of E₈, E₇ and E₆

C4 for the default model, using the common integer presentation.
-/
namespace Computations.C4

open E₈Data

/-- C4: the dimension and star-membership checks succeed on every pair. -/
theorem e₈_star_checked : checkStar 8 (-4) e₈Tree.contains e₈Roots = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by decide +kernel, ?_⟩
  apply all_eq_true_of_chunks (chunk := e₈Chunk) (m := 12) (by decide +kernel)
  apply List.all_eq_true.mp
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    e₈_star_chunk_0,
    e₈_star_chunk_1,
    e₈_star_chunk_2,
    e₈_star_chunk_3,
    e₈_star_chunk_4,
    e₈_star_chunk_5,
    e₈_star_chunk_6,
    e₈_star_chunk_7,
    e₈_star_chunk_8,
    e₈_star_chunk_9,
    e₈_star_chunk_10,
    e₈_star_chunk_11, Bool.and_self]

end Computations.C4

namespace LineSystem

-- Theorem 3.5 / computation C4
/-- C4 for Theorem 3.5 of [CGSS]. Model (ii) of E₈ is star-closed, by the list certificates. -/
theorem isStarClosed_E₈ : E₈.IsStarClosed := by
  apply E₈viaD₈.integerModel.isStarClosed_of_checkStar
    (table := Computations.E₈Data.e₈Roots) (decode := Computations.E₈Data.e₈Tree.contains)
  · exact Computations.E₈Data.ofFn_e₈Root_mem
  · intro w hw
    obtain ⟨a, ha⟩ := Computations.E₈Data.e₈Roots_sound
      (Computations.VectorTree.contains_sound hw)
    exact ⟨a, List.ofFn_inj.mp ha⟩
  · exact Computations.C4.e₈_star_checked

-- Theorem 3.5 / computation C4
/-- C4: the subsystem perpendicular to a root of E₈ is star-closed. -/
theorem isStarClosed_E₇ : E₇.IsStarClosed := isStarClosed_E₈.orthogonalTo e₇Normal

-- Theorem 3.5 / computation C4
/-- C4: the subsystem perpendicular to the fixed star of E₈ is star-closed. -/
theorem isStarClosed_E₆ : E₆.IsStarClosed := isStarClosed_E₇.orthogonalTo e₆Normal

end LineSystem
