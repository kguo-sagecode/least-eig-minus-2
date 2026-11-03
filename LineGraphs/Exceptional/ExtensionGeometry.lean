/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Certificate

/-! # The projection calculation for a one-vertex extension

Linear algebra used in `lem:extension` (Lemma 3.4) of [Exc].
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace Matrix

variable {V E : Type*} [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Matrix V V ℤ} {B : Finset V} {x : V → E}

-- Lemma 3.4 [Exc]
/-- In `lem:extension` (Lemma 3.4) of [Exc], the vectors indexed by a certificate
are independent in every Gram realization of the integer matrix. -/
theorem IsGramCertificate.linearIndependent_gram (hB : M.IsGramCertificate B)
    (hM : M.IsSymm) (hx : gram ℝ x = M.map (Int.cast : ℤ → ℝ)) :
    LinearIndependent ℝ (fun b : B => x b) := by
  have heq : gram ℝ (fun b : B => x b) = (M.certificateMatrix B).map (Int.cast : ℤ → ℝ) := by
    ext b c
    exact congrFun (congrFun hx b) c
  apply linearIndependent_of_posDef_gram
  rw [heq]
  exact hB.posDef hM

-- Lemma 3.4 [Exc]
/-- In `lem:extension` (Lemma 3.4) of [Exc], the vectors indexed by a certificate
span all vectors of the representation. -/
theorem IsGramCertificate.span_gram [Finite V] (hB : M.IsGramCertificate B)
    (hM : M.IsSymm) (hx : gram ℝ x = M.map (Int.cast : ℤ → ℝ)) :
    span ℝ (Set.range (fun b : B => x b)) = span ℝ (Set.range x) := by
  let := Fintype.ofFinite V
  have := FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_mono
    rintro _ ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rw [finrank_span_eq_card (hB.linearIndependent_gram hM hx), Fintype.card_coe,
      hB.card_eq_rank hM, ← hx, rank_gram_eq_finrank_span]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Lemma 3.4 [Exc]
/-- The vector with prescribed inner products, used as the projection in
`lem:extension` (Lemma 3.4) of [Exc]. -/
noncomputable def gramProjection (x : ι → E) (s : ι → ℝ) : E :=
  ∑ i, ((gram ℝ x)⁻¹ *ᵥ s) i • x i

-- Lemma 3.4 [Exc]
/-- The projection constructed in `lem:extension` (Lemma 3.4) of [Exc] lies in the
span of the selected vectors. -/
theorem gramProjection_mem_span (x : ι → E) (s : ι → ℝ) :
    gramProjection x s ∈ span ℝ (Set.range x) :=
  Submodule.sum_mem _ fun i _ => smul_mem _ _ (subset_span (Set.mem_range_self i))

-- Lemma 3.4 [Exc]
/-- The prescribed inner products in `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem inner_gramProjection (x : ι → E) (hp : (gram ℝ x).PosDef) (s : ι → ℝ) (i : ι) :
    ⟪x i, gramProjection x s⟫ = s i := by
  have hdet : IsUnit (gram ℝ x).det := (isUnit_iff_isUnit_det _).mp hp.isUnit
  calc
    ⟪x i, gramProjection x s⟫ = ((gram ℝ x) *ᵥ ((gram ℝ x)⁻¹ *ᵥ s)) i := by
      simp [gramProjection, inner_sum, real_inner_smul_right, mulVec, dotProduct,
        gram_apply, mul_comm]
    _ = s i := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

-- Lemma 3.4 [Exc]
/-- The projection's inner product formula in `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem gramProjection_inner (x : ι → E) (hp : (gram ℝ x).PosDef) (s : ι → ℝ) (y : E) :
    ⟪gramProjection x s, y⟫ = s ⬝ᵥ ((gram ℝ x)⁻¹ *ᵥ fun i => ⟪x i, y⟫) := by
  have ht : ((gram ℝ x)⁻¹)ᵀ = (gram ℝ x)⁻¹ :=
    (isHermitian_iff_isSymm.mp hp.inv.isHermitian).eq
  rw [gramProjection, sum_inner]
  simp only [real_inner_smul_left]
  change ((gram ℝ x)⁻¹ *ᵥ s) ⬝ᵥ _ = _
  rw [dotProduct_mulVec, ← vecMul_transpose, ht]

-- Lemma 3.4 [Exc]
/-- The squared norm formula in `lem:extension` (Lemma 3.4) of [Exc]. -/
theorem gramProjection_inner_self (x : ι → E) (hp : (gram ℝ x).PosDef) (s : ι → ℝ) :
    ⟪gramProjection x s, gramProjection x s⟫ = s ⬝ᵥ ((gram ℝ x)⁻¹ *ᵥ s) := by
  rw [gramProjection_inner x hp]
  simp only [inner_gramProjection x hp]

-- Lemma 3.4 [Exc]
/-- Equality of inner products extends from the selected vectors to their span in
`lem:extension` (Lemma 3.4) of [Exc]. -/
theorem gramProjection_inner_eq_of_mem_span (x : ι → E) (hp : (gram ℝ x).PosDef)
    (s : ι → ℝ) {y z : E} (hy : ∀ i, ⟪y, x i⟫ = s i)
    (hz : z ∈ span ℝ (Set.range x)) : ⟪gramProjection x s, z⟫ = ⟪y, z⟫ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    rw [real_inner_comm (x i) (gramProjection x s), inner_gramProjection x hp, hy]
  | zero => simp
  | add a b _ _ ha hb => simp only [inner_add_right, ha, hb]
  | smul a b _ hb => simp only [real_inner_smul_right, hb]

-- Lemma 3.4 [Exc]
/-- The projection has no greater squared norm, as used in `lem:extension`
(Lemma 3.4) of [Exc]. -/
theorem gramProjection_inner_self_le (x : ι → E) (hp : (gram ℝ x).PosDef)
    (s : ι → ℝ) {y : E} (hy : ∀ i, ⟪y, x i⟫ = s i) :
    ⟪gramProjection x s, gramProjection x s⟫ ≤ ⟪y, y⟫ := by
  have he := gramProjection_inner_eq_of_mem_span x hp s hy (gramProjection_mem_span x s)
  have hn := real_inner_self_nonneg (x := y - gramProjection x s)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, ← he,
    real_inner_comm y (gramProjection x s), ← he] at hn
  linarith

-- Lemma 3.4 [Exc]
/-- Equality of norms when the new vector is already in the span, in `lem:extension`
(Lemma 3.4) of [Exc]. -/
theorem gramProjection_inner_self_eq_of_mem_span (x : ι → E) (hp : (gram ℝ x).PosDef)
    (s : ι → ℝ) {y : E} (hy : ∀ i, ⟪y, x i⟫ = s i)
    (hm : y ∈ span ℝ (Set.range x)) :
    ⟪gramProjection x s, gramProjection x s⟫ = ⟪y, y⟫ := by
  have he := gramProjection_inner_eq_of_mem_span x hp s hy (gramProjection_mem_span x s)
  have he' := gramProjection_inner_eq_of_mem_span x hp s hy hm
  rw [real_inner_comm (gramProjection x s) y] at he
  exact he.trans he'

end Matrix
