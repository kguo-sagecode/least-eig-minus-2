/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData

/-!
# C21 E₆ integer data

Simple roots, coordinates and scaled LDL data from the Sage C21 certificate. -/

namespace Computations.C21

/-- The Sage simple matrix in integer coordinates. -/
def e6Simple : IntMatrix := [
  [2, 2, 0, 0, 0, 0, 0, 0],
  [-2, 2, 0, 0, 0, 0, 0, 0],
  [0, -2, 2, 0, 0, 0, 0, 0],
  [0, 0, -2, 2, 0, 0, 0, 0],
  [0, 0, 0, -2, 2, 0, 0, 0],
  [1, -1, -1, -1, -1, 1, 1, 1]]

/-- The Sage gram matrix in integer coordinates. -/
def e6Gram : IntMatrix := [
  [2, 0, -1, 0, 0, 0],
  [0, 2, -1, 0, 0, -1],
  [-1, -1, 2, -1, 0, 0],
  [0, 0, -1, 2, -1, 0],
  [0, 0, 0, -1, 2, 0],
  [0, -1, 0, 0, 0, 2]]

/-- The Sage lower matrix in integer coordinates. -/
def e6Lower : IntMatrix := [
  [2, 0, 0, 0, 0, 0],
  [0, 2, 0, 0, 0, 0],
  [-1, -1, 2, 0, 0, 0],
  [0, 0, -2, 2, 0, 0],
  [0, 0, 0, -2, 2, 0],
  [0, -1, -1, -1, -1, 2]]

/-- Four times the diagonal in the rational LDL factorization. -/
def e6Diagonal : IntVector := [8, 8, 4, 4, 4, 3]

/-- Integral coordinates of twenty roots. -/
def e6Coefficients0 : IntMatrix := [
  [-1, 0, 0, 0, 0, 0],
  [-1, 0, -1, 0, 0, 0],
  [-1, 0, -1, -1, 0, 0],
  [-1, 0, -1, -1, -1, 0],
  [0, 1, 1, 1, 1, 0],
  [0, 1, 1, 1, 0, 0],
  [0, 1, 1, 0, 0, 0],
  [0, 1, 0, 0, 0, 0],
  [-2, -2, -3, -2, -1, -1],
  [0, 1, 1, 1, 1, 1],
  [0, 1, 1, 1, 0, 1],
  [-1, -1, -1, 0, 0, -1],
  [0, 1, 1, 0, 0, 1],
  [-1, -1, -1, -1, 0, -1],
  [-1, -1, -1, -1, -1, -1],
  [1, 2, 3, 2, 1, 1],
  [0, 1, 0, 0, 0, 1],
  [-1, -1, -2, -1, 0, -1],
  [-1, -1, -2, -1, -1, -1],
  [1, 2, 2, 2, 1, 1]]

/-- Integral coordinates of twenty roots. -/
def e6Coefficients1 : IntMatrix := [
  [-1, -1, -2, -2, -1, -1],
  [1, 2, 2, 1, 1, 1],
  [1, 2, 2, 1, 0, 1],
  [0, 0, 0, 0, 0, -1],
  [-1, -1, -1, 0, 0, 0],
  [-1, -1, -1, -1, 0, 0],
  [-1, -1, -1, -1, -1, 0],
  [0, 0, 1, 1, 1, 0],
  [0, 0, 1, 1, 0, 0],
  [0, 0, 1, 0, 0, 0],
  [-1, -1, -2, -1, 0, 0],
  [-1, -1, -2, -1, -1, 0],
  [0, 0, 0, 1, 1, 0],
  [0, 0, 0, 1, 0, 0],
  [-1, -1, -2, -2, -1, 0],
  [0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, -1, 0],
  [1, 1, 2, 2, 1, 0],
  [0, 0, 0, -1, 0, 0],
  [0, 0, 0, -1, -1, 0]]

/-- Integral coordinates of twenty roots. -/
def e6Coefficients2 : IntMatrix := [
  [1, 1, 2, 1, 1, 0],
  [1, 1, 2, 1, 0, 0],
  [0, 0, -1, 0, 0, 0],
  [0, 0, -1, -1, 0, 0],
  [0, 0, -1, -1, -1, 0],
  [1, 1, 1, 1, 1, 0],
  [1, 1, 1, 1, 0, 0],
  [1, 1, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 1],
  [-1, -2, -2, -1, 0, -1],
  [-1, -2, -2, -1, -1, -1],
  [1, 1, 2, 2, 1, 1],
  [-1, -2, -2, -2, -1, -1],
  [1, 1, 2, 1, 1, 1],
  [1, 1, 2, 1, 0, 1],
  [0, -1, 0, 0, 0, -1],
  [-1, -2, -3, -2, -1, -1],
  [1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 0, 1],
  [0, -1, -1, 0, 0, -1]]

/-- Integral coordinates of twenty roots. -/
def e6Coefficients3 : IntMatrix := [
  [1, 1, 1, 0, 0, 1],
  [0, -1, -1, -1, 0, -1],
  [0, -1, -1, -1, -1, -1],
  [2, 2, 3, 2, 1, 1],
  [0, -1, 0, 0, 0, 0],
  [0, -1, -1, 0, 0, 0],
  [0, -1, -1, -1, 0, 0],
  [0, -1, -1, -1, -1, 0],
  [1, 0, 1, 1, 1, 0],
  [1, 0, 1, 1, 0, 0],
  [1, 0, 1, 0, 0, 0],
  [1, 0, 0, 0, 0, 0]]

/-- Coordinates in the sorted root-table order. -/
def e6Coefficients : IntMatrix :=
  e6Coefficients0 ++
    e6Coefficients1 ++
    e6Coefficients2 ++
    e6Coefficients3

end Computations.C21

-- Computation C21, for Remark 4.14 of [CGSS].
