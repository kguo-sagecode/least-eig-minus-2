/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.RootMapData

/-!
# Soundness of the rational root-map checker

Each checked coordinate is the exact numerator identity for the rational row-vector map.
-/

namespace Computations

/-- A successful root-image check gives every coordinate of every rational image. -/
theorem checkRootImages_sound {dim : ℕ} {den : ℤ} {mat : IntMatrix}
    {s t : List IntVector} (h : checkRootImages dim den mat s t = true)
    {i j : ℕ} (hi : i < s.length) (hj : j < dim) :
    dot (s[i]?.getD []) (mat.map fun row => row[j]?.getD 0) = den * entry t i j := by
  unfold checkRootImages at h
  exact beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj))

end Computations
