/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData

/-!
# C4 E₆ witnesses

Marked-star and connectivity witnesses translated from the Sage C4 certificate. -/

namespace Computations.C4

/-- Sage parents certificate, reindexed by the sorted root table. -/
def e6Parents : List ℕ := [
  71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56,
  55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40,
  39, 38, 37, 36, 44, 44, 70, 70, 70, 70, 71, 71, 71, 71, 71, 71,
  37, 44, 52, 44, 70, 70, 70, 70, 71, 71, 71, 71, 71, 71, 71, 71,
  70, 71, 71, 71, 71, 71, 71, 71]

/-- Sage depths certificate, reindexed by the sorted root table. -/
def e6Depths : List ℕ := [
  1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2,
  3, 3, 3, 3, 3, 4, 3, 4, 2, 2, 2, 2, 2, 2, 3, 3,
  3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1,
  3, 2, 3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1,
  2, 1, 1, 1, 1, 1, 1, 0]

/-- Sage gamma certificate, reindexed by the sorted root table. -/
def e6Gamma : List ℕ := [
  7, 41, 38, 40, 39, 23, 22, 21, 20]

/-- Sage delta certificate, reindexed by the sorted root table. -/
def e6Delta : List ℕ := [
  37, 36, 35, 34, 55, 54, 53, 52, 19, 18, 17, 16]

/-- Orthogonality adjacency on the certified Gamma labels. -/
def e6Adjacency : IntMatrix := [
  [0, 1, 1, 1, 1, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 0, 0, 1, 1],
  [1, 1, 0, 0, 0, 1, 1, 0, 0],
  [1, 0, 0, 0, 1, 0, 1, 0, 1],
  [1, 0, 0, 1, 0, 1, 0, 1, 0],
  [0, 0, 1, 0, 1, 0, 1, 1, 0],
  [0, 0, 1, 1, 0, 1, 0, 0, 1],
  [0, 1, 0, 0, 1, 1, 0, 0, 1],
  [0, 1, 0, 1, 0, 0, 1, 1, 0]]

end Computations.C4
