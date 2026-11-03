/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Computations.CliqueBenchmarkData

/-!
# Kernel benchmark for T8

Counts of four- and five-cliques and the per-vertex four-clique profile.
-/

namespace Computations.Examples

open CliqueBenchmarkData

theorem t8_adjacency : checkAdjacency 28 t8 = true := by decide +kernel

theorem t8_four_cliques : cliqueCount 28 4 t8 = 280 := by
  decide +kernel

theorem t8_five_cliques : cliqueCount 28 5 t8 = 168 := by
  decide +kernel

theorem t8_clique_profile : cliqueProfile 28 4 t8 =
    [40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
     40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40] := by
  decide +kernel

end Computations.Examples
