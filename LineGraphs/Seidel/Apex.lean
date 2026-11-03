/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.LatticeRoots

/-! # The apex of a regular representation

Lemma `lem:414-apex` of Remark 4.14 of [CGSS].
-/

open scoped RealInnerProductSpace
open Submodule

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

-- Lemma (the apex), for Remark 4.14 of [CGSS]
/-- The apex in `lem:414-apex`, Remark 4.14: the sum of the representing vectors
divided by `k + 2`. -/
noncomputable def IsRepresentation.apex (_hx : X.IsRepresentation x) (k : ℕ) : E :=
  ((k : ℝ) + 2)⁻¹ • ∑ u, x u

/-- The Gram row sum used in step `s414apexone` of `lem:414-apex`. -/
theorem IsRepresentation.sum_inner_eq_degree_add_two (hx : X.IsRepresentation x) (v : V) :
    ∑ u, ⟪x u, x v⟫ = (X.degree v : ℝ) + 2 := by
  classical
  have he (u : V) : ⟪x u, x v⟫ =
      (if u = v then (2 : ℝ) else 0) + if X.Adj v u then 1 else 0 := by
    rw [isRepresentation_iff.mp hx u v]
    by_cases huv : u = v
    · subst v
      simp
    · simp [huv, X.adj_comm u v]
  simp_rw [he]
  simp [Finset.sum_add_distrib, ← neighborFinset_eq_filter, add_comm]

/-- Assertion 1 of `lem:414-apex`: the apex pairs to one with every representing vector. -/
theorem IsRepresentation.inner_apex (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) (v : V) : ⟪hx.apex k, x v⟫ = 1 := by
  rw [apex, real_inner_smul_left, sum_inner, hx.sum_inner_eq_degree_add_two, hr v]
  exact inv_mul_cancel₀ (by positivity)

/-- Assertion 2 of `lem:414-apex`: the squared norm is the order divided by `k + 2`. -/
theorem IsRepresentation.inner_apex_self (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) :
    ⟪hx.apex k, hx.apex k⟫ = Fintype.card V / ((k : ℝ) + 2) := by
  change ⟪hx.apex k, ((k : ℝ) + 2)⁻¹ • ∑ u, x u⟫ = _
  rw [inner_smul_right, inner_sum]
  simp_rw [hx.inner_apex hr]
  simp [div_eq_mul_inv, mul_comm]

/-- Assertion 3 of `lem:414-apex`: the apex pairs integrally with the whole integer span. -/
theorem IsRepresentation.inner_apex_mem_int (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) {y : E} (hy : y ∈ span ℤ (Set.range x)) :
    ⟪hx.apex k, y⟫ ∈ Set.range (Int.cast : ℤ → ℝ) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    exact ⟨1, by simp [hx.inner_apex hr]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨a, ha⟩ := ihy
    obtain ⟨b, hb⟩ := ihz
    exact ⟨a + b, by simp [inner_add_right, ha, hb]⟩
  | smul a y _ ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨a * b, by simp [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hb]⟩

/-- Assertion 4 of `lem:414-apex`: the apex belongs to the real representation span. -/
theorem IsRepresentation.apex_mem_span (hx : X.IsRepresentation x) (k : ℕ) :
    hx.apex k ∈ span ℝ (Set.range x) :=
  smul_mem _ _ (sum_mem fun u _ ↦ subset_span (Set.mem_range_self u))

end SimpleGraph
