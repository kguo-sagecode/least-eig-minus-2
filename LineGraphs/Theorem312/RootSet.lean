/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.IntegerSpan

/-!
# The explicit root set for Theorem 3.12 of [CGSS]

`lem:312-reflection`, `lem:312-proportional` and `prop:312-rootset` of the blueprint.
The parity condition against the fixed integer span is preserved by adjointness.
-/

open scoped RealInnerProductSpace
open Submodule

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.12
/-- `t312reflAdjoint` of `lem:312-reflection`, Theorem 3.12 of [CGSS]. -/
theorem IsRootSet.reflection_self_adjoint (r : V) (hr : r ≠ 0) (x y : V) :
    ⟪IsRootSet.reflection r hr x, y⟫ = ⟪x, IsRootSet.reflection r hr y⟫ := by
  have h := (IsRootSet.reflection r hr).inner_map_map x (IsRootSet.reflection r hr y)
  rwa [IsRootSet.reflection_involutive r hr y] at h

namespace LineSystem

/-- `t312propUnequal` of `lem:312-proportional`, Theorem 3.12 of [CGSS]. -/
private theorem int_sq_ne_eight (z : ℤ) : z ^ 2 ≠ 8 := by
  intro hz
  have hlo : -3 < z := by nlinarith [sq_nonneg (z + 3)]
  have hhi : z < 3 := by nlinarith [sq_nonneg (z - 3)]
  interval_cases z <;> norm_num at hz

/-- `lem:312-proportional`, Theorem 3.12 of [CGSS]: integral proportional
vectors of squared norms 2 or 4 differ only in sign. -/
theorem eq_one_or_neg_one_of_integral_proportional {r s : V} {t : ℝ}
    (hr : ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 4) (hs : ⟪s, s⟫ = 2 ∨ ⟪s, s⟫ = 4)
    (hint : ∃ z : ℤ, ⟪r, s⟫ = z) (hst : s = t • r) : t = 1 ∨ t = -1 := by
  obtain ⟨z, hz⟩ := hint
  have hnorm : ⟪s, s⟫ = t ^ 2 * ⟪r, r⟫ := by
    rw [hst, real_inner_smul_left, real_inner_smul_right]
    ring
  have hprod : ⟪r, s⟫ ^ 2 = ⟪r, r⟫ * ⟪s, s⟫ := by
    rw [hnorm, hst, real_inner_smul_right]
    ring
  have hne : (z : ℝ) ^ 2 ≠ 8 := by exact_mod_cast int_sq_ne_eight z
  have ht : t ^ 2 = 1 := by
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · nlinarith
    · exfalso
      apply hne
      rw [hz, hr, hs] at hprod
      linarith only [hprod]
    · exfalso
      apply hne
      rw [hz, hr, hs] at hprod
      linarith only [hprod]
    · nlinarith
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using ht)

/-- `t312psiLengths` of `prop:312-rootset`, Theorem 3.12 of [CGSS]. -/
theorem sqNorm_mem_integralSpanRoots {T : Set V} {r : V} (hr : r ∈ integralSpanRoots T) :
    ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 4 := hr.2.imp_right And.left

/-- `t312psiSeeds` of `prop:312-rootset`, Theorem 3.12 of [CGSS]. -/
theorem subset_integralSpanRoots {T : Set V}
    (hnorm : ∀ t ∈ T, ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4)
    (heven : ∀ t ∈ T, ⟪t, t⟫ = 4 → ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = 2 * z) :
    T ⊆ integralSpanRoots T := by
  intro t ht
  refine ⟨subset_span ht, ?_⟩
  rcases hnorm t ht with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, fun x hx ↦ inner_even_of_mem_intSpan (heven t ht h) hx⟩

/-- `t312psiCoefficient` of `prop:312-rootset`, Theorem 3.12 of [CGSS]. -/
private theorem integralSpanRoots_coefficient_int {T : Set V}
    (hint : ∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z)
    {r x : V} (hr : r ∈ integralSpanRoots T) (hx : x ∈ span ℤ T) :
    ∃ z : ℤ, 2 * ⟪r, x⟫ / ⟪r, r⟫ = z := by
  rcases hr.2 with h | ⟨h, heven⟩
  · obtain ⟨z, hz⟩ := inner_int_of_mem_intSpan hint hr.1 hx
    exact ⟨z, by rw [h, hz]; ring⟩
  · obtain ⟨z, hz⟩ := heven x hx
    exact ⟨z, by rw [h, hz]; ring⟩

/-- `t312psiLattice` of `prop:312-rootset`, Theorem 3.12 of [CGSS]. -/
private theorem reflection_mem_intSpan {T : Set V}
    (hint : ∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z)
    {r x : V} (hr : r ∈ integralSpanRoots T) (hr0 : r ≠ 0) (hx : x ∈ span ℤ T) :
    IsRootSet.reflection r hr0 x ∈ span ℤ T := by
  obtain ⟨z, hz⟩ := integralSpanRoots_coefficient_int hint hr hx
  rw [IsRootSet.reflection_apply, hz, Int.cast_smul_eq_zsmul]
  exact sub_mem hx (smul_mem _ _ hr.1)

/-- `prop:312-rootset`, Theorem 3.12 of [CGSS]. The explicit Ψ(T) satisfies
all six conditions of Definition 3.9, contains the seeds, and has squared norms
2 or 4. The proof retains the long-root parity invariant under reflection. -/
theorem isRootSet_integralSpanRoots {T : Set V} (hfin : T.Finite)
    (hspan : span ℝ T = ⊤) (hnorm : ∀ t ∈ T, ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4)
    (hint : ∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z)
    (heven : ∀ t ∈ T, ⟪t, t⟫ = 4 → ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = 2 * z) :
    IsRootSet (integralSpanRoots T) ∧ T ⊆ integralSpanRoots T ∧
      ∀ r ∈ integralSpanRoots T, ⟪r, r⟫ = 2 ∨ ⟪r, r⟫ = 4 := by
  have hsub := subset_integralSpanRoots hnorm heven
  have hn (r : V) (hr : r ∈ integralSpanRoots T) := sqNorm_mem_integralSpanRoots hr
  have hzero : (0 : V) ∉ integralSpanRoots T := by
    intro h
    have := hn 0 h
    norm_num at this
  refine ⟨?_, hsub, hn⟩
  refine {
    finite := (finite_bounded_intSpan hfin hnorm hint).subset ?_
    zero_notMem := hzero
    span_eq_top := top_unique (hspan ▸ span_mono hsub)
    crystallographic := ?_
    reduced := ?_
    reflection_mem := ?_ }
  · intro r hr
    exact ⟨hr.1, by rcases hn r hr with h | h <;> linarith⟩
  · intro r hr s hs
    obtain ⟨z, hz⟩ := integralSpanRoots_coefficient_int hint hr hs.1
    exact ⟨z, hz.symm⟩
  · intro r hr t ht
    exact eq_one_or_neg_one_of_integral_proportional (hn r hr) (hn (t • r) ht)
      (inner_int_of_mem_intSpan hint hr.1 ht.1) rfl
  · intro r hr s hs
    have hr0 : r ≠ 0 := fun h ↦ hzero (h ▸ hr)
    rw [← IsRootSet.reflection_apply r hr0]
    refine ⟨reflection_mem_intSpan hint hr hr0 hs.1, ?_⟩
    rcases hs.2 with hs | ⟨hs, he⟩
    · exact Or.inl (by rwa [LinearIsometryEquiv.inner_map_map])
    · refine Or.inr ⟨by rwa [LinearIsometryEquiv.inner_map_map], ?_⟩
      intro x hx
      rw [IsRootSet.reflection_self_adjoint]
      exact he _ (reflection_mem_intSpan hint hr hr0 hx)

end LineSystem
