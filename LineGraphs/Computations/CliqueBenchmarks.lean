/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.CliqueBenchmarkT8
import LineGraphs.Computations.CliqueBenchmarkChangI
import LineGraphs.Computations.CliqueBenchmarkChangII
import LineGraphs.Computations.CliqueBenchmarkChangIII

/-!
# Non-isomorphism from the C22 clique profiles

The global four- and five-clique counts agree for Chang II and III. The finer profile
distinguishes them, and its soundness rules out every graph isomorphism.
-/

namespace Computations.Examples

open CliqueBenchmarkData

theorem changII_not_iso_changIII :
    ¬ Nonempty (graphOfMatrix changII_adjacency ≃g graphOfMatrix changIII_adjacency) := by
  apply checkNonisomorphic_sound changII_adjacency changIII_adjacency (k := 4)
  rw [checkNonisomorphic, changII_adjacency, changIII_adjacency,
    changII_clique_profile, changIII_clique_profile]
  decide +kernel

end Computations.Examples
