/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Line graphs, root systems, and elliptic geometry

This library formalizes

  P. J. Cameron, J. M. Goethals, J. J. Seidel and E. E. Shult, *Line graphs, root systems, and
  elliptic geometry*, J. Algebra 43 (1976), 305–327,

down to Mathlib, with no `sorry`, no `axiom` and no `native_decide`. The layout of the library is
described in `README.md`, and the structured proofs that each file follows are in `blueprint/`.

This file is the root of the library's own definitions; it fixes the imports that every part of
the library needs.
-/
