/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Lines
import LineGraphs.LineSystem.SpanExtension

/-! # The lattice roots of a representation

Lemma `lem:414-lattice` of Remark 4.14 of [CGSS].
-/

open scoped RealInnerProductSpace
open Submodule

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

omit [Fintype V] in
/-- Step `s414latint` of `lem:414-lattice`: the generating Gram matrix is integral. -/
theorem IsRepresentation.inner_mem_int (hx : X.IsRepresentation x) (u v : V) :
    ⟪x u, x v⟫ ∈ Set.range (Int.cast : ℤ → ℝ) := by
  rw [isRepresentation_iff.mp hx u v]
  split_ifs
  · exact ⟨2, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

omit [Fintype V] in
/-- Step `s414latint` of `lem:414-lattice`: inner products on the integer span are integral. -/
theorem IsRepresentation.inner_mem_int_of_mem_span_int (hx : X.IsRepresentation x)
    {y z : E} (hy : y ∈ span ℤ (Set.range x)) (hz : z ∈ span ℤ (Set.range x)) :
    ⟪y, z⟫ ∈ Set.range (Int.cast : ℤ → ℝ) := by
  have hgen (u : V) : ⟪x u, z⟫ ∈ Set.range (Int.cast : ℤ → ℝ) := by
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨v, rfl⟩ := hz; exact hx.inner_mem_int u v
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ ihz ihw =>
      obtain ⟨a, ha⟩ := ihz
      obtain ⟨b, hb⟩ := ihw
      exact ⟨a + b, by simp [inner_add_right, ha, hb]⟩
    | smul a z _ ih =>
      obtain ⟨b, hb⟩ := ih
      exact ⟨a * b, by simp [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hb]⟩
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨u, rfl⟩ := hy; exact hgen u
  | zero => exact ⟨0, by simp⟩
  | add y w _ _ ihy ihw =>
    obtain ⟨a, ha⟩ := ihy
    obtain ⟨b, hb⟩ := ihw
    exact ⟨a + b, by simp [inner_add_left, ha, hb]⟩
  | smul a y _ ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨a * b, by simp [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hb]⟩

omit [Fintype V] [DecidableEq V] in
/-- The integer span lies in the real span (step `s414latmem` of `lem:414-lattice`). -/
theorem mem_span_real_of_mem_span_int {y : E} (hy : y ∈ span ℤ (Set.range x)) :
    y ∈ span ℝ (Set.range x) := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ ihy ihz => exact add_mem ihy ihz
  | smul a y _ ih =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact smul_mem _ _ ih

/-- Step `s414latvals` of `lem:414-lattice`: integral products of norm-two vectors
belong to the five allowed values. Also used for the apex in `lem:414-transversal`. -/
theorem inner_mem_five_of_mem_int {y z : E} (hy : ⟪y, y⟫ = 2) (hz : ⟪z, z⟫ = 2)
    (h : ⟪y, z⟫ ∈ Set.range (Int.cast : ℤ → ℝ)) :
    ⟪y, z⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
  obtain ⟨a, ha⟩ := h
  have hb := real_inner_mul_inner_self_le y z
  rw [hy, hz, ← ha] at hb
  have hlow : (-2 : ℝ) ≤ a := by nlinarith
  have hhigh : (a : ℝ) ≤ 2 := by nlinarith
  have hlow' : -2 ≤ a := by exact_mod_cast hlow
  have hhigh' : a ≤ 2 := by exact_mod_cast hhigh
  rw [← ha]
  interval_cases a <;> norm_num

omit [Fintype V] in
/-- Step `s414latfin` of `lem:414-lattice`: lattice roots are among the finitely many
vectors compatible with the original spanning line system. -/
theorem IsRepresentation.finite_latticeRoots [Finite V] (hx : X.IsRepresentation x) :
    {y | y ∈ span ℤ (Set.range x) ∧ ⟪y, y⟫ = 2}.Finite := by
  let : Fintype V := Fintype.ofFinite V
  apply hx.lineSystem.finite_spanCandidates.subset
  intro y hy
  refine ⟨?_, hy.2, ?_⟩
  · rw [hx.span_lineSystem]
    exact mem_span_real_of_mem_span_int hy.1
  intro z hz
  have hzint : z ∈ span ℤ (Set.range x) := by
    rcases hz with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact subset_span (Set.mem_range_self u)
    · exact neg_mem (subset_span (Set.mem_range_self u))
  exact inner_mem_five_of_mem_int hy.2 (hx.lineSystem.inner_self z hz)
    (hx.inner_mem_int_of_mem_span_int hy.1 hzint)

-- Lemma (the lattice roots), for Remark 4.14 of [CGSS]
/-- The line system of norm-two vectors in the integer span, Lemma `lem:414-lattice`
of Remark 4.14 of [CGSS]. -/
def IsRepresentation.latticeRoots (hx : X.IsRepresentation x) : LineSystem E where
  Φ := {y | y ∈ span ℤ (Set.range x) ∧ ⟪y, y⟫ = 2}
  finite := hx.finite_latticeRoots
  inner_self _ hy := hy.2
  neg_mem _ hy := ⟨neg_mem hy.1, by simpa using hy.2⟩
  inner_mem _ hy _ hz := inner_mem_five_of_mem_int hy.2 hz.2
    (hx.inner_mem_int_of_mem_span_int hy.1 hz.1)

/-- Step `s414latmem` of `lem:414-lattice`: each representing vector is a lattice root. -/
theorem IsRepresentation.mem_latticeRoots (hx : X.IsRepresentation x) (u : V) :
    x u ∈ hx.latticeRoots.Φ := ⟨subset_span (Set.mem_range_self u), hx.inner_self u⟩

/-- Step `s414latstar` of `lem:414-lattice`: the sum of an ordered star is a lattice root. -/
theorem IsRepresentation.isStarClosed_latticeRoots (hx : X.IsRepresentation x) :
    hx.latticeRoots.IsStarClosed := by
  intro y hy z hz hyz
  refine ⟨add_mem hy.1 hz.1, ?_⟩
  have hzy : ⟪z, y⟫ = -1 := by rw [real_inner_comm, hyz]
  rw [inner_add_left, inner_add_right, inner_add_right, hy.2, hz.2, hyz, hzy]
  norm_num

/-- Step `s414latspan` of `lem:414-lattice`: passing to lattice roots preserves the span. -/
theorem IsRepresentation.span_latticeRoots (hx : X.IsRepresentation x) :
    span ℝ hx.latticeRoots.Φ = span ℝ (Set.range x) := by
  apply le_antisymm
  · exact span_le.mpr fun _ hy ↦ mem_span_real_of_mem_span_int hy.1
  · apply span_mono
    rintro _ ⟨u, rfl⟩
    exact hx.mem_latticeRoots u

/-- Step `s414latind` of `lem:414-lattice`: connectedness and equality of spans
carry indecomposability from the representing lines to all lattice roots. -/
theorem IsRepresentation.isIndecomposable_latticeRoots (hx : X.IsRepresentation x)
    (hX : X.Connected) : hx.latticeRoots.IsIndecomposable := by
  apply (hx.isIndecomposable_of_connected hX).of_span_eq
  · rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact hx.mem_latticeRoots u
    · exact hx.latticeRoots.neg_mem _ (hx.mem_latticeRoots u)
  · rw [hx.span_latticeRoots, hx.span_lineSystem]

/-- The nonemptiness in step `s414latind` of `lem:414-lattice`. -/
theorem IsRepresentation.latticeRoots_nonempty (hx : X.IsRepresentation x)
    (hX : X.Connected) : hx.latticeRoots.Φ.Nonempty := by
  obtain ⟨u⟩ := hX.nonempty
  exact ⟨x u, hx.mem_latticeRoots u⟩

/-- Assertion 3 of `lem:414-lattice`: the original family represents the graph
in its lattice-root system. -/
theorem IsRepresentation.isRepresentedIn_latticeRoots (hx : X.IsRepresentation x) :
    X.IsRepresentedIn hx.latticeRoots := ⟨x, hx, hx.mem_latticeRoots⟩

end SimpleGraph
