/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData

/-!
# Executable root-map checks

These checks have no dependency on real geometry or the structured root models.
-/

namespace Computations

/-- One row of a scaled Gram comparison, evaluated on materialized roots. -/
def checkScaledGramRow (qs qt : ℤ) (s t : List IntVector) (i : ℕ) : Bool :=
  (List.range s.length).all fun j =>
    qt * dot (s[i]?.getD []) (s[j]?.getD []) ==
      qs * dot (t[i]?.getD []) (t[j]?.getD [])

/-- Verify all root images under a rational matrix given by numerator and denominator. -/
def checkRootImages (dim : ℕ) (den : ℤ) (mat : IntMatrix)
    (s t : List IntVector) : Bool :=
  (List.range s.length).all fun i => (List.range dim).all fun j =>
    dot (s[i]?.getD []) (mat.map fun row => row[j]?.getD 0) == den * entry t i j

end Computations
