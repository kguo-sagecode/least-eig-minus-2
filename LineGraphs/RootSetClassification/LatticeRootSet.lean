/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic

/-!
# Root sets of norm two in integral lattices

The argument `rEreflection`--`rErootset` of `lem:E` in the blueprint for
Remark 3.11 of [CGSS], stated for an arbitrary integral additive subgroup.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Steps `rEreflection`--`rErootset` of Remark 3.11: the finite, spanning norm-two
vectors of an integral additive subgroup form a root set. -/
theorem of_norm_two_lattice (L : AddSubgroup V) (Φ : Set V)
    (heq : Φ = {x | x ∈ L ∧ ⟪x, x⟫ = 2}) (hfin : Φ.Finite)
    (hspan : Submodule.span ℝ Φ = ⊤)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, (z : ℝ) = ⟪x, y⟫) : IsRootSet Φ where
  finite := hfin
  zero_notMem := by simp [heq]
  span_eq_top := hspan
  crystallographic r hr s hs := by
    rw [heq] at hr hs
    obtain ⟨z, hz⟩ := hint r hr.1 s hs.1
    exact ⟨z, by rw [hr.2, ← hz]; ring⟩
  reduced r hr t ht := by
    rw [heq] at hr ht
    have he := ht.2
    rw [real_inner_smul_left, real_inner_smul_right, hr.2] at he
    have hp : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  reflection_mem r hr s hs := by
    rw [heq] at hr hs ⊢
    have hr0 : r ≠ 0 := by intro h; subst r; simp at hr
    have hn := (reflection r hr0).inner_map_map s s
    rw [reflection_apply, hs.2] at hn
    refine ⟨?_, hn⟩
    obtain ⟨z, hz⟩ := hint r hr.1 s hs.1
    have hc : 2 * ⟪r, s⟫ / ⟪r, r⟫ = (z : ℝ) := by rw [hr.2, ← hz]; ring
    rw [hc, Int.cast_smul_eq_zsmul ℝ]
    exact L.sub_mem hs.1 (L.zsmul_mem hr.1 z)

end IsRootSet
