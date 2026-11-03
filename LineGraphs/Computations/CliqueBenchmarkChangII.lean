/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Computations.CliqueBenchmarkData

/-!
# Kernel benchmark for Chang II

Counts of four- and five-cliques and the per-vertex four-clique profile.
-/

namespace Computations.Examples

open CliqueBenchmarkData

theorem changII_adjacency : checkAdjacency 28 changII = true := by decide +kernel

theorem changII_four_cliques : cliqueCount 28 4 changII = 240 := by
  decide +kernel

theorem changII_five_cliques : cliqueCount 28 5 changII = 48 := by
  decide +kernel

theorem changII_clique_profile : cliqueProfile 28 4 changII =
    [34, 34, 34, 36, 34, 34, 34, 34, 34, 34, 36, 34, 34, 34,
     34, 34, 36, 34, 34, 34, 34, 36, 34, 34, 34, 34, 34, 34] := by
  decide +kernel

end Computations.Examples
