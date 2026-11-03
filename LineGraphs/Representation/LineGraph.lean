/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# The representation of a line graph

Lemma `lem:4-linegraph` in the Section 4 blueprint for [CGSS]. Inner products count
common endpoints.
-/

open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (Y : SimpleGraph V)

noncomputable local instance decidableAdjLineGraphRepresentation : DecidableRel Y.lineGraph.Adj :=
  Classical.decRel _

/-- Lemma `lem:4-linegraph`, Section 4 of [CGSS]: the vector with a one at each endpoint. -/
noncomputable def lineGraphVector (e : Y.edgeSet) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun i ↦ if i ∈ (e : Sym2 V) then 1 else 0)

omit [Fintype V] in
/-- Lemma `lem:4-linegraph`, step `s4lgip`, Section 4 of [CGSS]: the endpoint formula. -/
theorem lineGraphVector_mk {i j : V} (hij : Y.Adj i j) :
    Y.lineGraphVector ⟨s(i, j), hij⟩ =
      EuclideanSpace.single i 1 + EuclideanSpace.single j 1 := by
  ext k
  simp only [lineGraphVector,
    Sym2.mem_iff, PiLp.add_apply, PiLp.single_apply]
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [hij.ne]

/-- Lemma `lem:4-linegraph`, Section 4 of [CGSS]: endpoint vectors represent the line graph.
Step `s4lgip` counts common endpoints. -/
theorem lineGraph_isRepresentation : Y.lineGraph.IsRepresentation Y.lineGraphVector := by
  apply isRepresentation_iff.mpr
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  have hij' : i ≠ j := hij.ne
  have hkl' : k ≠ l := hkl.ne
  rw [Y.lineGraphVector_mk hij, Y.lineGraphVector_mk hkl]
  have hadj : Y.lineGraph.Adj ⟨s(i, j), hij⟩ ⟨s(k, l), hkl⟩ ↔
      s(i, j) ≠ s(k, l) ∧ (i = k ∨ i = l ∨ j = k ∨ j = l) := by
    rw [lineGraph_adj_iff_exists]
    simp only [ne_eq, Subtype.mk.injEq, Sym2.mem_iff]
    aesop
  simp only [inner_add_left, inner_add_right, EuclideanSpace.inner_single_left,
    PiLp.single_apply, map_one, one_mul, hadj, Subtype.mk.injEq, Sym2.eq_iff]
  by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> simp_all <;> norm_num

end SimpleGraph
