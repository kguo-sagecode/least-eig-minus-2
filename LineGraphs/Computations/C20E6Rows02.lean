/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20Data

/-!
# C20 neighborhood sweep

A block of the exhaustive C20 neighborhood count. -/

namespace Computations.C20

theorem e6_chunk_2 : e6Chunk 2 = true := by decide +kernel

end Computations.C20
