/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LineRepresentatives
import LineGraphs.RootSetClassification.SmallRankSimilarity

/-!
# The common B and C line sets

Steps `rCclassicalsame`, `rCcounts`, and the rank-two construction case
in Theorem C of the blueprint for Remark 3.11 of [CGSS].
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] {Φ : Set V} {Ψ : Set W}

/-- Similarities preserve indecomposability, including the `rBCtwo` construction case. -/
theorem IsSimilarity.isIndecomposable (hΦ : IsRootSet Φ) (hΨ : IsRootSet Ψ)
    {f : V ≃ₗ[ℝ] W} {a : ℝ} (hf : IsSimilarity Φ Ψ f a) (hI : hΦ.IsIndecomposable) :
    hΨ.IsIndecomposable := by
  have hpre : f ⁻¹' Ψ = Φ := by rw [← hf.image_eq]; exact f.injective.preimage_image Φ
  refine ⟨hf.image_eq ▸ hI.1.image f, ?_⟩
  intro A B hab horth
  have hp : f ⁻¹' A ∪ f ⁻¹' B = Φ := by rw [← Set.preimage_union, hab, hpre]
  have ho : ∀ r ∈ f ⁻¹' A, ∀ s ∈ f ⁻¹' B, ⟪r, s⟫ = 0 := by
    intro r hr s hs
    have he := horth (f r) hr (f s) hs
    rw [hf.inner_map] at he
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hf.factor_pos)
  rcases hI.2 _ _ hp ho with hA | hB
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : f.symm x ∈ f ⁻¹' A := by simpa using hx
    simp only [hA, Set.mem_empty_iff_false] at this
  · right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : f.symm x ∈ f ⁻¹' B := by simpa using hx
    simp only [hB, Set.mem_empty_iff_false] at this

end IsRootSet

namespace RootSetModel

open IsRootSet

/-- Step `rCsameaxes`: every nonzero axis length gives the same coordinate lines. -/
theorem rootLines_axisRoots (n : ℕ) {c : ℝ} (hc : c ≠ 0) :
    rootLines (axisRoots n c) = Set.range (fun i : Fin n ↦ ℝ ∙ unit i) := by
  ext L
  constructor
  · rintro ⟨r, ⟨i, rfl | rfl⟩, rfl⟩
    · exact ⟨i, (span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _).symm⟩
    · refine ⟨i, ?_⟩
      rw [← neg_smul]
      exact (span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc)) _).symm
  · rintro ⟨i, rfl⟩
    exact ⟨c • unit i, ⟨i, Or.inl rfl⟩,
      span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _⟩

-- Remark 3.11, thm:C
/-- Steps `rCsameaxes`, `rCsamepairs`: B and C have exactly the same actual line sets. -/
theorem Bn_Cn_same_lines (n : ℕ) : rootLines (Bn n) = rootLines (Cn n) := by
  change (fun r ↦ ℝ ∙ r) '' (axisRoots n 1 ∪ Dn n) =
    (fun r ↦ ℝ ∙ r) '' (axisRoots n 2 ∪ Dn n)
  rw [Set.image_union, Set.image_union]
  change rootLines (axisRoots n 1) ∪ rootLines (Dn n) =
    rootLines (axisRoots n 2) ∪ rootLines (Dn n)
  rw [rootLines_axisRoots n (by norm_num : (1 : ℝ) ≠ 0),
    rootLines_axisRoots n (by norm_num : (2 : ℝ) ≠ 0)]

/-- Step `rCcounts`: both classical line sets have `n²` lines in dimension `n`. -/
theorem Bn_Cn_line_counts (n : ℕ) :
    (rootLines (Bn n)).ncard = n ^ 2 ∧ (rootLines (Cn n)).ncard = n ^ 2 ∧
      Module.finrank ℝ (span ℝ (Bn n)) = n := by
  have hb : (rootLines (Bn n)).ncard = n ^ 2 := by
    rw [(Bn_isRootSet n).ncard_rootLines, IsRootSet.numLines, Bn_ncard]
    omega
  refine ⟨hb, by rw [← Bn_Cn_same_lines]; exact hb, ?_⟩
  rw [(Bn_isRootSet n).span_eq_top, finrank_top]
  simp

/-- The C construction remains indecomposable at rank two (`rBCtwo`, `rCframes`). -/
theorem Cn_isIndecomposable {n : ℕ} (hn : 2 ≤ n) : (Cn_isRootSet n).IsIndecomposable := by
  by_cases he : n = 2
  · subst n
    exact B₂_C₂_similarity.isIndecomposable (Bn_isRootSet 2) (Cn_isRootSet 2)
      (isIndecomposable (.b 2 le_rfl))
  · exact isIndecomposable (.c n (by omega))

end RootSetModel
