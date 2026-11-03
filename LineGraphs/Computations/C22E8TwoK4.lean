/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22TriangularModel

/-! # C22: switching by `twoK4` in the E8 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 3
/-- The `twoK4` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e8_switch_twoK4 :
    Nonempty (switchTriangular (twoK4) ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) := by
  obtain ⟨e⟩ := nonempty_iso_switchTriangular_of_check (twoK4) (graphOfMatrix Examples.t8_adjacency)
      edgePairs8 edgePairs8_bijective
      e8TwoK4Adj (CliqueBenchmarkData.t8) e8TwoK4Permutation
      (by decide +kernel) (fun _ _ ↦ Iff.rfl) (by decide +kernel)
  exact ⟨e.trans triangular8TableIso⟩

-- Computation C22, assertion 3
/-- The empty switching set gives the triangular graph, assertion 3 of `comp:C22`. -/
theorem e8_switch_empty :
    Nonempty (switchTriangular (⊥ : SimpleGraph (Fin 8)) ≃g
      (⊤ : SimpleGraph (Fin 8)).lineGraph) := by
  rw [switchTriangular_bot]
  exact ⟨Iso.refl⟩

end Computations.C22

