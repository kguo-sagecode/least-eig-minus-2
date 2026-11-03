import LineGraphs.Computations.ListData

/-!
# Computation C13: certificate data for [CGSS], Corollary 5.10

Transcribed from `cgss/certificates/data/c13.json`, schema `linegraphs-sage-v1`.
These are untrusted inputs; the accompanying modules prove their properties in Lean.
-/

namespace Computations.C13

/-- C13, [CGSS] Corollary 5.10: adjacency table 1. -/
def adjacency1 : IntMatrix :=
  [[0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1],
   [0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1],
   [1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
   [0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0],
   [0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1],
   [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
   [1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
   [0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0],
   [1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0]]

/-- C13, [CGSS] Corollary 5.10: adjacency table 2. -/
def adjacency2 : IntMatrix :=
  [[0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1],
   [0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1],
   [1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
   [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
   [0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0],
   [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
   [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
   [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0],
   [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0]]

/-- C13, [CGSS] Corollary 5.10: adjacency eigenvalues and multiplicities. -/
def spectralData : List (ℤ × ℕ) :=
  [(4, 1), (2, 3), (0, 3), (-2, 5)]

/-- C13, [CGSS] Corollary 5.10: printed Steiner vectors, set 1. -/
def roots1 : IntMatrix :=
  [[2, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0],
   [1, 1, 0, 0, 1, -1, 0, 0],
   [0, 1, 1, 0, -1, 0, 0, 1],
   [0, 0, 1, 1, 0, 0, 1, -1],
   [1, 0, 0, 1, 0, 1, -1, 0],
   [1, 1, 0, 0, -1, 1, 0, 0],
   [0, 1, 1, 0, 1, 0, 0, -1],
   [0, 0, 1, 1, 0, 0, -1, 1],
   [1, 0, 0, 1, 0, -1, 1, 0]]

/-- C13, [CGSS] Corollary 5.10: printed Steiner vectors, set 2. -/
def roots2 : IntMatrix :=
  [[2, 0, 0, 0, 0, 0, 0, 0],
   [0, 2, 0, 0, 0, 0, 0, 0],
   [0, 0, 2, 0, 0, 0, 0, 0],
   [0, 0, 0, 2, 0, 0, 0, 0],
   [1, 1, 0, 0, 1, -1, 0, 0],
   [0, 1, 1, 0, -1, 0, 0, 1],
   [0, 0, 1, 1, 0, 0, 1, -1],
   [1, 0, 0, 1, 0, 1, -1, 0],
   [1, 1, 0, 0, 0, 0, 1, -1],
   [0, 1, 1, 0, 0, 1, -1, 0],
   [0, 0, 1, 1, 1, -1, 0, 0],
   [1, 0, 0, 1, -1, 0, 0, 1]]

/-- C13, [CGSS] Corollary 5.10: the integral map to the fixed E₇ model. -/
def rootMap : IntMatrix :=
  [[-1, 1, 0, 0, 0, 0, 0, 0],
   [-1, -1, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0, 0],
   [0, 0, 1, -1, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 1, 0],
   [0, 0, 0, 0, -1, 0, 1, 0],
   [0, 0, 0, 0, 0, 1, 0, -1],
   [0, 0, 0, 0, 0, -1, 0, -1]]

/-- C13, [CGSS] Corollary 5.10: the design flag table. -/
def flagAdjacency : IntMatrix :=
  [[0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
   [1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0],
   [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
   [1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0],
   [0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1],
   [1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0],
   [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1],
   [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1],
   [0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1],
   [0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0]]

/-- C13, [CGSS] Corollary 5.10: the permutation from graph 1 to flags. -/
def flagPermutation : List ℕ :=
  [0, 4, 11, 7, 3, 9, 8, 2, 1, 5, 10, 6]

/-- C13, [CGSS] Corollary 5.10: the switching signs. -/
def switchSigns : IntVector :=
  [1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1]

/-- C13, [CGSS] Corollary 5.10: the switching permutation. -/
def switchPermutation : List ℕ :=
  [0, 1, 2, 3, 4, 9, 6, 11, 10, 7, 8, 5]

/-- C13, [CGSS] Corollary 5.10: the spectrum for J − I − 2A. -/
def seidelSpectralData : List (ℤ × ℕ) :=
  [(-5, 3), (-1, 3), (3, 6)]

end Computations.C13
