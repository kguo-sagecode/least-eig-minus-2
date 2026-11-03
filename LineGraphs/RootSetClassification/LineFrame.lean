/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.RootFrame
import LineGraphs.RootSetClassification.LineRepresentatives

/-!
# The line frame identity

`lem:tight-frame` of the blueprint for Remark 3.11 of [CGSS]. The full
root frame is twice the frame with one representative per line. Arbitrary
unit vectors on those lines have the same projectors.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Φ : Set V} {I : Type*} [Fintype I]

/-- The frame with unit columns in `lem:C-convention`. -/
noncomputable def lineFrame (u : I → V) : Module.End ℝ V := ∑ i, lineProjector (u i)

omit [Fintype I] in
/-- Step `rCsurjective`: every choice of vectors spanning the root lines spans the space. -/
theorem RootRepresentatives.span_unit (hΦ : IsRootSet Φ) {r u : I → V}
    (hr : RootRepresentatives Φ r) (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    span ℝ (Set.range u) = ⊤ := by
  apply top_unique
  rw [← hΦ.span_eq_top]
  apply span_le.mpr
  intro s hs
  obtain ⟨i, hi | hi⟩ := hr.covers s hs
  all_goals
    have hm : r i ∈ ℝ ∙ u i := by rw [hl i]; exact mem_span_singleton_self _
    have hiu : ℝ ∙ u i ≤ span ℝ (Set.range u) :=
      span_le.mpr (Set.singleton_subset_iff.mpr (subset_span ⟨i, rfl⟩))
  · rw [hi]; exact hiu hm
  · rw [hi]; exact Submodule.neg_mem _ (hiu hm)

/-- Step `rfrsign`: any unit vector on a root line has the same projector. -/
theorem rootProjector_eq_of_unit_mem {r u : V} (hr : r ≠ 0) (hu : ‖u‖ = 1)
    (hru : r ∈ ℝ ∙ u) : rootProjector r = lineProjector u := by
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hru
  have ha : a ≠ 0 := by intro he; exact hr (by simp [he])
  have haa : |a| ≠ 0 := abs_ne_zero.mpr ha
  ext x
  simp only [rootProjector, normalizedRoot, norm_smul, Real.norm_eq_abs, hu, mul_one,
    smul_smul, lineProjector_apply, real_inner_smul_left]
  have he : (|a|⁻¹ * a * ⟪u, x⟫) * (|a|⁻¹ * a) = ⟪u, x⟫ := by
    field_simp
    rw [sq_abs]
  rw [he]

/-- Step `rfrvalue`: the full root frame contains each line projector twice. -/
theorem RootRepresentatives.rootFrame_eq_twice [Fintype Φ] (hΦ : IsRootSet Φ)
    {r : I → V} (hr : RootRepresentatives Φ r) :
    hΦ.rootFrame = (2 : ℝ) • lineFrame (fun i ↦ normalizedRoot (r i)) := by
  unfold rootFrame
  rw [← (hr.signEquiv hΦ).sum_comp]
  simp only [RootRepresentatives.signEquiv, Equiv.ofBijective_apply,
    RootRepresentatives.signedRoot, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, rootProjector_neg]
  simp only [lineFrame, rootProjector, two_smul, Finset.sum_add_distrib]

/-- The normalized-root version of `lem:tight-frame` in Remark 3.11. -/
theorem frame_identity_normalized (hΦ : IsRootSet Φ) (hI : hΦ.IsIndecomposable)
    {r : I → V} (hr : RootRepresentatives Φ r) :
    lineFrame (fun i ↦ normalizedRoot (r i)) =
      ((Fintype.card I : ℝ) / Module.finrank ℝ V) • LinearMap.id := by
  let := hΦ.finite_root_index
  let := Fintype.ofFinite Φ
  have he := congrArg (fun F : Module.End ℝ V ↦ (1 / 2 : ℝ) • F)
    (hΦ.rootFrame_eq_smul_id hI)
  rw [hr.rootFrame_eq_twice hΦ, hr.card hΦ] at he
  simp only [Nat.cast_mul, Nat.cast_ofNat, smul_smul] at he
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] at he
  convert he using 1
  congr 1
  ring

-- Remark 3.11, lem:tight-frame
/-- The line frame identity of Remark 3.11, for any unit representatives of
the root lines. The line equality allows every choice of representative signs. -/
theorem frame_identity (hΦ : IsRootSet Φ) (hI : hΦ.IsIndecomposable)
    {r u : I → V} (hr : RootRepresentatives Φ r) (hu : ∀ i, ‖u i‖ = 1)
    (hl : ∀ i, ℝ ∙ u i = ℝ ∙ r i) :
    0 < Module.finrank ℝ V ∧
      lineFrame u = ((Fintype.card I : ℝ) / Module.finrank ℝ V) • LinearMap.id := by
  refine ⟨hΦ.finrank_pos_of_isIndecomposable hI, ?_⟩
  rw [← hΦ.frame_identity_normalized hI hr]
  apply Finset.sum_congr rfl
  intro i _
  apply (rootProjector_eq_of_unit_mem (hΦ.ne_zero (hr.mem i)) (hu i) ?_).symm
  rw [hl i]
  exact mem_span_singleton_self _

end IsRootSet
