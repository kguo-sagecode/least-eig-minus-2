/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Computations.CliqueBenchmarkData

/-!
# Kernel benchmark for Chang I

Counts of four- and five-cliques and the per-vertex four-clique profile.
-/

namespace Computations.Examples

open CliqueBenchmarkData

theorem changI_adjacency : checkAdjacency 28 changI = true := by decide +kernel

theorem changI_four_cliques : cliqueCount 28 4 changI = 248 := by
  decide +kernel

theorem changI_five_cliques : cliqueCount 28 5 changI = 72 := by
  decide +kernel

theorem changI_clique_profile : cliqueProfile 28 4 changI =
    [36, 36, 36, 32, 36, 36, 36, 36, 36, 36, 32, 36, 36, 36,
     36, 36, 32, 36, 36, 36, 36, 32, 36, 36, 36, 36, 36, 36] := by
  decide +kernel

end Computations.Examples
