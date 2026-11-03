/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData

/-!
# C16: the five integer Hadamard matrices

The rows are copied from `cgss/certificates/data/c16.json`. These data are untrusted;
subsequent kernel checks prove orthogonality and Hypothesis 6.1.
-/

namespace Computations.C16

/-- The Paley12 matrix from the C16 certificate. -/
def h12Rows : IntMatrix :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [-1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1],
   [-1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1, 1],
   [-1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1, -1],
   [-1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, -1],
   [-1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1],
   [-1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1],
   [-1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, 1],
   [-1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1],
   [-1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1],
   [-1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1],
   [-1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1]]

/-- The Sylvester2 matrix from the C16 certificate. -/
def h2Rows : IntMatrix :=
  [[1, 1],
   [1, -1]]

/-- The Sylvester4 matrix from the C16 certificate. -/
def h4Rows : IntMatrix :=
  [[1, 1, 1, 1],
   [1, -1, 1, -1],
   [1, 1, -1, -1],
   [1, -1, -1, 1]]

/-- The Sylvester8 matrix from the C16 certificate. -/
def h8Rows : IntMatrix :=
  [[1, 1, 1, 1, 1, 1, 1, 1],
   [1, -1, 1, -1, 1, -1, 1, -1],
   [1, 1, -1, -1, 1, 1, -1, -1],
   [1, -1, -1, 1, 1, -1, -1, 1],
   [1, 1, 1, 1, -1, -1, -1, -1],
   [1, -1, 1, -1, -1, 1, -1, 1],
   [1, 1, -1, -1, -1, -1, 1, 1],
   [1, -1, -1, 1, -1, 1, 1, -1]]

/-- The Sylvester16 matrix from the C16 certificate. -/
def h16Rows : IntMatrix :=
  [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1],
   [1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1],
   [1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1],
   [1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1],
   [1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1],
   [1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1],
   [1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1],
   [1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
   [1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1],
   [1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1],
   [1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1],
   [1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
   [1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1],
   [1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1],
   [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]]

end Computations.C16
