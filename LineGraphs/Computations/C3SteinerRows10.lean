/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C3Data
import LineGraphs.Computations.ExceptionalData

/-!
# C3 scaled Gram certificate

Twenty rows of the scaled Gram comparison for the Sage map. -/

namespace Computations.C3

theorem steiner_gram_chunk_10 : steinerGramChunk 10 = true := by
  decide +kernel

end Computations.C3
