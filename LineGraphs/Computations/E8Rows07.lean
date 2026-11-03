/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.E8Data

/-!
# Twenty star rows of E₈

One kernel proof per chunk; shared data are independent of C4.
-/

namespace Computations.C4

open E₈Data

theorem e₈_star_chunk_7 :
    (e₈Chunk 7).all (checkStarRow (-4) e₈Tree.contains e₈Roots) = true := by
  decide +kernel

end Computations.C4
