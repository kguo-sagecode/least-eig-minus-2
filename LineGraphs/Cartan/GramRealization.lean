/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Positivity
import LineGraphs.Spectral.Gram

/-!
# Gram realizations of nonnegative forms

Lemma (a Gram realization), `lem:rem-gram` of the Remark 3.11 blueprint. A real symmetric
matrix `Q` on a finite type `I` with nonnegative quadratic form is the Gram matrix of a spanning
family in a Euclidean space of dimension `|I| - dim ker Q`. In every real inner product space,
the linear relations of a family with Gram matrix `Q` are exactly `ker Q`, and its span has
dimension `|I| - dim ker Q`.

The realization is `Matrix.PosSemidef.exists_gram_euclideanSpace` of the spectral toolkit,
which takes square roots of the eigenvalues in an orthonormal eigenbasis (steps
`rgdiag`--`rgentries`). It lies in `EuclideanSpace ℝ (Fin (|I| - dim ker Q))` rather than in the
range of the square-root map `T`, so its spanning (step `rgspan`) follows from the dimension
count of step `rgdimension`.
-/

open Module
open scoped InnerProductSpace

universe u

namespace Matrix

variable {I : Type u} [Fintype I]

/-- Step `rgrelations` of `lem:rem-gram` (Remark 3.11): in any real inner product space, the
linear relations of a family are exactly the kernel of its Gram matrix. -/
theorem sum_smul_eq_zero_iff_gram_mulVec_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : I → E) (x : I → ℝ) :
    ∑ i, x i • w i = 0 ↔ gram ℝ w *ᵥ x = 0 := by
  have hQ : (gram ℝ w).IsSymm := isHermitian_iff_isSymm.mp (isHermitian_gram ℝ w)
  have hnonneg (y : I → ℝ) : 0 ≤ y ⬝ᵥ (gram ℝ w *ᵥ y) := by
    simpa only [star_trivial] using (posSemidef_gram ℝ w).dotProduct_mulVec_nonneg y
  -- Step `rgnorm`: the squared norm of the combination is the quadratic form at `x`.
  have hnorm : x ⬝ᵥ (gram ℝ w *ᵥ x) = ⟪∑ i, x i • w i, ∑ i, x i • w i⟫_ℝ := by
    simpa only [star_trivial] using star_dotProduct_gram_mulVec w x x
  -- Step `rgzero`: by definiteness, the combination vanishes exactly when the form does.
  have hzero : ∑ i, x i • w i = 0 ↔ x ⬝ᵥ (gram ℝ w *ᵥ x) = 0 := by
    rw [hnorm, inner_self_eq_zero]
  -- `lem:rem-null`, and substitution of `Qx = 0`.
  rw [hzero]
  exact ⟨mulVec_eq_zero_of_quadratic_eq_zero hQ hnonneg, fun h ↦ by rw [h, dotProduct_zero]⟩

/-- Step `rgdimension` of `lem:rem-gram` (Remark 3.11): in any real inner product space, the
span of a family has dimension `|I| - dim ker Q` for its Gram matrix `Q`. -/
theorem finrank_span_eq_card_sub_finrank_ker_gram {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : I → E) :
    finrank ℝ (Submodule.span ℝ (Set.range w)) =
      Fintype.card I - finrank ℝ (LinearMap.ker (gram ℝ w).mulVecLin) := by
  -- Rank-nullity for `x ↦ ∑ i, x i • w i`: its range is the span, its kernel `rgrelations`.
  let F : (I → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ w
  have hker : LinearMap.ker F = LinearMap.ker (gram ℝ w).mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, F, Fintype.linearCombination_apply, mulVecLin_apply]
    exact sum_smul_eq_zero_iff_gram_mulVec_eq_zero w x
  have h := LinearMap.finrank_range_add_finrank_ker F
  rw [Fintype.range_linearCombination, hker, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- Lemma (a Gram realization), `lem:rem-gram` of the Remark 3.11 blueprint. Let `Q` be a real
symmetric matrix on a finite type `I` with `xᵀQx ≥ 0` for every real vector `x`. Then `Q` is the
Gram matrix of a spanning family in the Euclidean space `V` of dimension `|I| - dim ker Q`. For
every family `w` with Gram matrix `Q` in any real inner product space, `∑ i, x i • w i = 0`
exactly when `Qx = 0`, and the span of `w` has dimension `|I| - dim ker Q`. The dimension of `V`
is part of its type. In this bundle `E` and `I` share a universe, so projections need no
universe annotation; the separate relation and dimension theorems are universe polymorphic. -/
theorem exists_gram_realization {Q : Matrix I I ℝ} (hQ : Q.IsSymm)
    (hnonneg : ∀ x : I → ℝ, 0 ≤ x ⬝ᵥ (Q *ᵥ x)) :
    (∃ v : I → EuclideanSpace ℝ (Fin (Fintype.card I - finrank ℝ (LinearMap.ker Q.mulVecLin))),
      gram ℝ v = Q ∧ Submodule.span ℝ (Set.range v) = ⊤) ∧
    ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : I → E), gram ℝ w = Q →
      (∀ x : I → ℝ, ∑ i, x i • w i = 0 ↔ Q *ᵥ x = 0) ∧
      finrank ℝ (Submodule.span ℝ (Set.range w)) =
        Fintype.card I - finrank ℝ (LinearMap.ker Q.mulVecLin) := by
  refine ⟨?_, fun w hw ↦ ?_⟩
  · -- Steps `rgdiag`--`rgentries`: the eigenbasis square root realizes `Q` in any dimension
    -- at least its rank, and rank-nullity gives the rank `|I| - dim ker Q`.
    have hpsd : Q.PosSemidef := .of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.mpr hQ)
      (by simpa only [star_trivial] using hnonneg)
    have hrank : Q.rank = Fintype.card I - finrank ℝ (LinearMap.ker Q.mulVecLin) := by
      have h := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h
      change finrank ℝ (LinearMap.range Q.mulVecLin) = _
      omega
    obtain ⟨v, hv⟩ := hpsd.exists_gram_euclideanSpace hrank.le
    refine ⟨v, hv, ?_⟩
    -- Step `rgspan`, by the dimension count `rgdimension` for the constructed family.
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card_sub_finrank_ker_gram v, hv, finrank_euclideanSpace_fin]
  · -- Steps `rgrelations` and `rgdimension`, for every realizing family.
    subst hw
    exact ⟨sum_smul_eq_zero_iff_gram_mulVec_eq_zero w,
      finrank_span_eq_card_sub_finrank_ker_gram w⟩

end Matrix
