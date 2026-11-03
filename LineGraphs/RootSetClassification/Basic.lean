/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Similarities and root bases for Remark 3.11

The definitions follow `def:roots` and `def:rem-bases` of
`blueprint/sec3-remark311.tex`. The similarity laws are `lem:rem-similarity-laws`.
Root bases use integer coefficients of one sign, with the second root supplying
the denominator of the Cartan pairing.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V W U : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {Φ : Set V} {Ψ : Set W} {Ω : Set U}

/-- A similarity with specified squared-length factor, as in `def:roots`
of Remark 3.11 of [CGSS]. -/
structure IsSimilarity (Φ : Set V) (Ψ : Set W) (f : V ≃ₗ[ℝ] W) (a : ℝ) : Prop where
  factor_pos : 0 < a
  inner_map : ∀ x y, ⟪f x, f y⟫ = a * ⟪x, y⟫
  image_eq : f '' Φ = Ψ

-- Remark 3.11, lem:rem-similarity-laws
/-- Step `rsimcompose`: similarities compose, with product squared-length factor. -/
theorem similarity_comp {f : V ≃ₗ[ℝ] W} {g : W ≃ₗ[ℝ] U} {a b : ℝ}
    (hf : IsSimilarity Φ Ψ f a) (hg : IsSimilarity Ψ Ω g b) :
    IsSimilarity Φ Ω (f.trans g) (a * b) where
  factor_pos := mul_pos hf.factor_pos hg.factor_pos
  inner_map x y := by
    change ⟪g (f x), g (f y)⟫ = _
    rw [hg.inner_map, hf.inner_map]
    ring
  image_eq := by
    change (g ∘ f) '' Φ = Ω
    rw [Set.image_comp, hf.image_eq, hg.image_eq]

-- Remark 3.11, lem:rem-similarity-laws
/-- Step `rsiminvert`: the inverse similarity has reciprocal squared-length factor. -/
theorem similarity_symm {f : V ≃ₗ[ℝ] W} {a : ℝ} (hf : IsSimilarity Φ Ψ f a) :
    IsSimilarity Ψ Φ f.symm a⁻¹ where
  factor_pos := inv_pos.mpr hf.factor_pos
  inner_map x y := by
    have h := hf.inner_map (f.symm x) (f.symm y)
    simp only [f.apply_symm_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hf.factor_pos), one_mul]
  image_eq := by
    rw [← hf.image_eq, ← Set.image_comp]
    simp only [Function.comp_def, f.symm_apply_apply, Set.image_id']

/-- The Cartan pairing of `def:rem-bases` in Remark 3.11 of [CGSS]. -/
noncomputable def cartanPairing {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (α : I → V) : Matrix I I ℝ := fun i j ↦ 2 * ⟪α i, α j⟫ / ⟪α j, α j⟫

variable {I : Type*} [Fintype I]

-- Remark 3.11, def:rem-bases
/-- A root base in Remark 3.11 of [CGSS]: independent roots with integer
expansions whose coefficients have one sign. Finiteness is carried by the index type. -/
structure IsBase (hΦ : IsRootSet Φ) (α : I → V) : Prop where
  mem : ∀ i, α i ∈ Φ
  linearIndependent : LinearIndependent ℝ α
  coefficients : ∀ r ∈ Φ, ∃ c : I → ℤ,
    ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0)) ∧ r = ∑ i, (c i : ℝ) • α i

namespace IsBase

variable {hΦ : IsRootSet Φ} {α : I → V} (hα : hΦ.IsBase α)

include hα in
/-- The spanning assertion following `def:rem-bases` in Remark 3.11. -/
theorem span_eq_top : span ℝ (Set.range α) = ⊤ := by
  apply top_unique
  rw [← hΦ.span_eq_top]
  apply span_le.mpr
  intro r hr
  obtain ⟨c, _, hc⟩ := hα.coefficients r hr
  rw [hc]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (Set.mem_range_self i))

/-- The real vector-space basis supplied by `def:rem-bases` in Remark 3.11. -/
noncomputable def toBasis : Module.Basis I ℝ V :=
  Module.Basis.mk hα.linearIndependent hα.span_eq_top.ge

/-- The basis in `def:rem-bases` retains the prescribed simple roots. -/
@[simp] theorem toBasis_apply (i : I) : hα.toBasis i = α i :=
  Module.Basis.mk_apply _ _ i

end IsBase

/-- Step `rBmonoid` of Remark 3.11: a positive-or-negative natural span gives
integer coefficients of one sign, in exactly the convention of `def:rem-bases`. -/
theorem coefficients_of_mem_nat_span_or_neg_mem {α : I → V} {r : V}
    (hr : r ∈ span ℕ (Set.range α) ∨ -r ∈ span ℕ (Set.range α)) :
    ∃ c : I → ℤ, ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0)) ∧
      r = ∑ i, (c i : ℝ) • α i := by
  rcases hr with hr | hr
  · obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℕ).mp hr
    refine ⟨fun i ↦ c i, Or.inl (fun i ↦ Int.natCast_nonneg _), ?_⟩
    simpa only [Int.cast_natCast, Nat.cast_smul_eq_nsmul] using hc.symm
  · obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℕ).mp hr
    refine ⟨fun i ↦ -(c i : ℤ), Or.inr (fun i ↦ neg_nonpos.mpr (Int.natCast_nonneg _)), ?_⟩
    simpa only [Int.cast_neg, Int.cast_natCast, neg_smul, Nat.cast_smul_eq_nsmul,
      Finset.sum_neg_distrib, neg_neg] using congrArg Neg.neg hc.symm

/-- Steps `rclsimplesspan`, `rclindependent`, and `rclbase` of Remark 3.11:
a generating family of the right cardinality with one-sign expansions is a root base. -/
theorem isBase_of_mem_nat_span_or_neg_mem (hΦ : IsRootSet Φ) (α : I → V)
    (hmem : ∀ i, α i ∈ Φ) (hcard : Fintype.card I = Module.finrank ℝ V)
    (hpos : ∀ r ∈ Φ, r ∈ span ℕ (Set.range α) ∨ -r ∈ span ℕ (Set.range α)) :
    hΦ.IsBase α := by
  have hexp := fun r hr ↦ coefficients_of_mem_nat_span_or_neg_mem (hpos r hr)
  have hspan : ⊤ ≤ span ℝ (Set.range α) := by
    rw [← hΦ.span_eq_top]
    apply span_le.mpr
    intro r hr
    obtain ⟨c, _, hc⟩ := hexp r hr
    rw [hc]
    exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span (Set.mem_range_self i))
  exact ⟨hmem, linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard, hexp⟩

end IsRootSet
