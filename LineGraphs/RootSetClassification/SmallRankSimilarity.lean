/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.RootCounts

/-!
# The similarity between B₂ and C₂

Step `rBCtwo` of the indecomposable classification in Remark 3.11 of [CGSS].
The map has columns `(1,-1)` and `(1,1)`, and squared-length factor two.
-/

open scoped RealInnerProductSpace

namespace RootSetModel

/-- The explicit map in `rBCtwo` of Remark 3.11, including its inverse. -/
noncomputable def b₂ToC₂ : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 ![x 0 + x 1, -x 0 + x 1]
  invFun x := WithLp.toLp 2 ![(x 0 - x 1) / 2, (x 0 + x 1) / 2]
  left_inv x := by
    ext i
    fin_cases i
    · simp
    · simp; ring
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

/-- Steps `rBCaxis1`, `rBCaxis2`: the images of the coordinate axes. -/
theorem b₂ToC₂_unit : b₂ToC₂ (unit 0) = unit 0 - unit 1 ∧
    b₂ToC₂ (unit 1) = unit 0 + unit 1 := by
  constructor <;> ext i <;> fin_cases i <;> norm_num [b₂ToC₂, unit]

/-- Step `rBCmetric`: the explicit map multiplies inner products by two. -/
theorem b₂ToC₂_inner (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪b₂ToC₂ x, b₂ToC₂ y⟫ = 2 * ⟪x, y⟫ := by
  simp [b₂ToC₂, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Steps `rBCaxis1`--`rBCminus`: the map sends every B₂ root to a C₂ root. -/
theorem b₂ToC₂_mem {r : EuclideanSpace ℝ (Fin 2)} (hr : r ∈ Bn 2) :
    b₂ToC₂ r ∈ Cn 2 := by
  have haxis (i : Fin 2) : b₂ToC₂ (unit i) ∈ Cn 2 := by
    fin_cases i
    · change b₂ToC₂ (unit (0 : Fin 2)) ∈ Cn 2
      rw [b₂ToC₂_unit.1]
      exact Or.inr (LineSystem.sub_single_mem_Dn 0 1 (by decide))
    · change b₂ToC₂ (unit (1 : Fin 2)) ∈ Cn 2
      rw [b₂ToC₂_unit.2]
      exact Or.inr (LineSystem.add_single_mem_Dn 0 1 (by decide))
  rcases hr with ⟨i, rfl | rfl⟩ | hr
  · simpa only [one_smul] using haxis i
  · simpa only [one_smul, map_neg] using (Cn_isRootSet 2).neg_mem (haxis i)
  · obtain ⟨⟨⟨⟨i, j⟩, hij⟩, a, b⟩, rfl⟩ := hr
    have hi : i = 0 := by apply Fin.ext; have := j.isLt; change i.val < j.val at hij; omega
    have hj : j = 1 := by apply Fin.ext; have := j.isLt; change i.val < j.val at hij; omega
    subst i
    subst j
    change b₂ToC₂ (LineSystem.integerVector 1
      (LineSystem.dnRoot (⟨(0, 1), hij⟩, a, b))) ∈ _
    rw [dnRoot_eq_signed_units, map_add, map_smul, map_smul,
      b₂ToC₂_unit.1, b₂ToC₂_unit.2]
    cases a <;> cases b <;>
      simp only [LineSystem.rootSign, Bool.false_eq_true, ite_false, ite_true,
        Int.cast_one, Int.cast_neg, one_smul, neg_smul]
    · left
      refine ⟨0, Or.inl ?_⟩
      simp only [two_smul]
      abel
    · left
      refine ⟨1, Or.inr ?_⟩
      simp only [two_smul]
      abel
    · left
      refine ⟨1, Or.inl ?_⟩
      simp only [two_smul]
      abel
    · left
      refine ⟨0, Or.inr ?_⟩
      simp only [two_smul]
      abel

/-- Step `rBCtwo`: C₂ is omitted from the canonical list because this explicit
map is a similarity from B₂ onto C₂, with squared-length factor two. -/
theorem B₂_C₂_similarity : IsRootSet.IsSimilarity (Bn 2) (Cn 2) b₂ToC₂ 2 where
  factor_pos := by norm_num
  inner_map := b₂ToC₂_inner
  image_eq := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨r, hr, rfl⟩
      exact b₂ToC₂_mem hr
    · rw [Set.ncard_image_of_injective _ b₂ToC₂.injective, Bn_ncard, Cn_ncard]
    · exact (Cn_isRootSet 2).finite

end RootSetModel
