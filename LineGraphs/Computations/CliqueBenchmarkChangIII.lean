/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Computations.CliqueBenchmarkData

/-!
# Kernel benchmark for Chang III

Counts of four- and five-cliques and the per-vertex four-clique profile.
-/

namespace Computations.Examples

open CliqueBenchmarkData

theorem changIII_adjacency : checkAdjacency 28 changIII = true := by decide +kernel

theorem changIII_four_cliques : cliqueCount 28 4 changIII = 240 := by
  decide +kernel

theorem changIII_five_cliques : cliqueCount 28 5 changIII = 48 := by
  decide +kernel

theorem changIII_clique_profile : cliqueProfile 28 4 changIII =
    [35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35, 35,
     35, 35, 35, 35, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33] := by
  decide +kernel

end Computations.Examples
