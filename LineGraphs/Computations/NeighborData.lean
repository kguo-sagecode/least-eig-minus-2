/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData

/-!
# Executable neighbor counts

The target is the integer model's normalization constant.
-/

namespace Computations

/-- Count roots having the prescribed dot product with one root. -/
def checkNeighborCount (q : ℤ) (k : ℕ) (roots : List IntVector) (v : IntVector) : Bool :=
  (roots.filter (fun w => dot w v == q)).length == k

end Computations
