/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C22Data
import LineGraphs.Computations.C22Labels
import LineGraphs.Computations.C22BipartiteModel

/-! # C22: switching by `twoC3` in the E7 case -/

namespace Computations.C22

open SimpleGraph

set_option maxRecDepth 10000

-- Computation C22, assertion 2
/-- The `twoC3` isomorphism certificate of `comp:C22` (Remark 4.14). -/
theorem e7_switch_twoC3 :
    Nonempty (switchTriangularAddOne twoC3 ≃g
      (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph) := by
  obtain ⟨e⟩ := nonempty_iso_switchTriangularAddOne_of_check twoC3
      (graphOfMatrix lattice44_adjacency)
      e7TwoC3Adj (lattice44Adj) e7TwoC3Permutation
      (by decide +kernel) (fun _ _ ↦ Iff.rfl) (by decide +kernel)
  exact ⟨e.trans lattice44TableIso⟩

end Computations.C22
