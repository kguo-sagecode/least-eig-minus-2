/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LineCounts
import LineGraphs.RootSetClassification.LineRepresentatives
import LineGraphs.RootSetClassification.RootFrame
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The rational coordinate frame

`comp:rem-rational-frame` of the blueprint for Remark 3.11 of [CGSS]: for a coordinate
model with `N` lines and rank `n`, in its coordinate space (which may be larger than its
span), and the matrix `A` with the simple roots as columns,
`(1/2) ∑_{α ∈ Φ} α αᵀ / ‖α‖² = (N / n) A (Aᵀ A)⁻¹ Aᵀ`.
Both sides act by `N / n` on the span of the roots and vanish on its orthogonal complement:
`IsRootSet.half_rootSum_eq_smul_starProjection` (steps `rrfleft`, `rrfequality`) and
`Matrix.projection_mulVec_eq_starProjection` (step `rrfprojection`).
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Φ : Set V}

/-- Step `rrfleft` of Remark 3.11: each line carries exactly two roots, so the number of
roots is twice the number of lines. -/
theorem card_eq_two_mul_numLines [Fintype Φ] (hΦ : IsRootSet Φ) :
    (Fintype.card Φ : ℝ) = 2 * hΦ.numLines := by
  let := (hΦ.finite_rootLines).fintype
  rw [(hΦ.lineRoot_representatives).card hΦ, (hΦ.lineRoot_representatives).numLines hΦ]
  push_cast
  ring

/-- The unit projector on the line of a nonzero root, `x ↦ (⟪r, x⟫ / ‖r‖²) r`
(`lem:rem-projectors`). -/
theorem rootProjector_apply_eq (r x : V) : rootProjector r x = (⟪r, x⟫ / ‖r‖ ^ 2) • r := by
  simp only [rootProjector, normalizedRoot, lineProjector_apply, real_inner_smul_left,
    smul_smul]
  congr 1
  ring

/-- Steps `rrfleft`, `rrfequality` of Remark 3.11: for an indecomposable root set in `V`
and a linear isometry `ι` of `V` into `E`, half the sum over the roots of the unit line
projections acts on `E` as `N / n` times the orthogonal projection onto the image of `ι`. -/
theorem half_rootSum_eq_smul_starProjection [Fintype Φ] [FiniteDimensional ℝ E]
    (hΦ : IsRootSet Φ) (hI : hΦ.IsIndecomposable) (ι : V →ₗᵢ[ℝ] E) (x : E) :
    (1 / 2 : ℝ) • ∑ r : Φ, (⟪ι r, x⟫ / ‖ι r‖ ^ 2) • ι r =
      ((hΦ.numLines : ℝ) / Module.finrank ℝ V) •
        (LinearMap.range ι.toLinearMap).starProjection x := by
  set K := LinearMap.range ι.toLinearMap
  obtain ⟨w, hw⟩ := K.starProjection_apply_mem x
  have hin (r : V) : ⟪ι r, x⟫ = ⟪r, w⟫ := by
    have h0 := K.starProjection_inner_eq_zero x (ι r) ⟨r, rfl⟩
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [real_inner_comm, h0, ← hw, real_inner_comm]
    exact ι.inner_map_map r w
  have hframe := congrArg (fun f ↦ f w) (hΦ.rootFrame_eq_smul_id hI)
  simp only [rootFrame, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hframe
  have hn : (Module.finrank ℝ V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hΦ.finrank_pos_of_isIndecomposable hI))
  calc (1 / 2 : ℝ) • ∑ r : Φ, (⟪ι r, x⟫ / ‖ι r‖ ^ 2) • ι r =
        (1 / 2 : ℝ) • ι (∑ r : Φ, rootProjector (r : V) w) := by
        rw [map_sum]
        congr 1
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [rootProjector_apply_eq, map_smul, hin, LinearIsometry.norm_map]
    _ = (1 / 2 : ℝ) • ι (((Fintype.card Φ : ℝ) / Module.finrank ℝ V) • w) := by
        rw [hframe]
    _ = ((hΦ.numLines : ℝ) / Module.finrank ℝ V) • K.starProjection x := by
        rw [map_smul, ← hw, smul_smul, hΦ.card_eq_two_mul_numLines]
        congr 1
        field_simp

end IsRootSet

namespace Matrix

variable {m n : ℕ}

/-- The columns of a real matrix, as vectors of the coordinate space (`rrfprojection`). -/
noncomputable def columnVector (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i ↦ A i j)

/-- The coordinate inner product with a column is an entry of `Aᵀ x` (`rrfprojection`). -/
theorem inner_columnVector (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) (x : Fin m → ℝ) :
    ⟪WithLp.toLp 2 x, A.columnVector j⟫ = (Aᵀ *ᵥ x) j := by
  simp only [columnVector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mulVec,
    dotProduct, transpose_apply]

/-- Step `rrfprojection` of Remark 3.11: `A c` combines the columns with coefficients `c`. -/
theorem toLp_mulVec_eq_sum (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    WithLp.toLp 2 (A *ᵥ c) = ∑ j, c j • A.columnVector j := by
  ext i
  simp [columnVector, mulVec, dotProduct, Finset.sum_apply, mul_comm]

-- Remark 3.11, comp:rem-rational-frame
/-- Step `rrfprojection` of Remark 3.11: if the columns of `A` are independent, then
`A (Aᵀ A)⁻¹ Aᵀ` is the orthogonal projection onto their span. -/
theorem projection_mulVec_eq_starProjection (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.mulVec) (x : Fin m → ℝ) :
    WithLp.toLp 2 ((A * (Aᵀ * A)⁻¹ * Aᵀ) *ᵥ x) =
      (span ℝ (Set.range A.columnVector)).starProjection (WithLp.toLp 2 x) := by
  have hG : IsUnit (Aᵀ * A).det := by
    have hpd := PosDef.conjTranspose_mul_self A hA
    rw [conjTranspose_eq_transpose_of_trivial] at hpd
    exact (isUnit_iff_isUnit_det _).mp hpd.isUnit
  symm
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Matrix.mul_assoc, ← mulVec_mulVec, toLp_mulVec_eq_sum]
    exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · intro w hw
    refine span_induction (p := fun w _ ↦ ⟪WithLp.toLp 2 x -
      WithLp.toLp 2 ((A * (Aᵀ * A)⁻¹ * Aᵀ) *ᵥ x), w⟫ = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨j, rfl⟩
      rw [← WithLp.toLp_sub, inner_columnVector, mulVec_sub, mulVec_mulVec,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ A, mul_nonsing_inv _ hG, Matrix.one_mul,
        sub_self]
      rfl
    · exact inner_zero_right _
    · intro u v _ _ hu hv
      rw [inner_add_right, hu, hv, add_zero]
    · intro a u _ hu
      rw [inner_smul_right, hu, mul_zero]

end Matrix

namespace RootSetModel

open IsRootSet CartanMatrix Matrix

/-- The dimension of the coordinate space of each model of `eq:list` in Remark 3.11, which
may be larger than the rank (`comp:rem-rational-frame`). -/
def ambientDim {n : ℕ} : FiniteType n → ℕ
  | .a n _ => n + 1
  | .b n _ | .c n _ | .d n _ => n
  | .e₆ | .e₇ | .e₈ => 8
  | .f₄ => 4
  | .g₂ => 3

/-- The inclusion of each model space into its coordinate space
(`comp:rem-rational-frame`). -/
noncomputable def toAmbient {n : ℕ} (t : FiniteType n) :
    Space t →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (ambientDim t)) := by
  cases t with
  | a n _ => exact (span ℝ (LineSystem.An n).Φ).subtypeₗᵢ
  | b n _ | c n _ | d n _ => exact LinearIsometry.id
  | e₆ => exact e₆Space.subtypeₗᵢ
  | e₇ => exact e₇Space.subtypeₗᵢ
  | e₈ | f₄ => exact LinearIsometry.id
  | g₂ => exact g₂Space.subtypeₗᵢ

/-- The matrix `A` of `comp:rem-rational-frame`: the simple roots of the model as columns,
in its coordinate space. -/
noncomputable def simpleRootMatrix {n : ℕ} (t : FiniteType n) :
    Matrix (Fin (ambientDim t)) (Fin n) ℝ :=
  fun i j ↦ toAmbient t (simpleRoot t j) i

/-- The finitely many roots of a model, as an index type for step `rrfleft` of Remark 3.11.
This is used as an instance only in this module. -/
noncomputable local instance fintypeRoots {n : ℕ} (t : FiniteType n) : Fintype (roots t) :=
  (isRootSet t).finite.fintype

/-- The left side of `eq:rational-frame` in Remark 3.11: half the sum over the roots `α`
of `α αᵀ / ‖α‖²`, in coordinates. -/
noncomputable def halfRootSum {n : ℕ} (t : FiniteType n) :
    Matrix (Fin (ambientDim t)) (Fin (ambientDim t)) ℝ :=
  (1 / 2 : ℝ) • ∑ r : roots t, (‖toAmbient t r‖ ^ 2)⁻¹ •
    vecMulVec (fun i ↦ toAmbient t r i) (fun i ↦ toAmbient t r i)

/-- Step `rrfprojection` of Remark 3.11: the columns of `simpleRootMatrix` are the
simple roots in coordinates. -/
theorem columnVector_simpleRootMatrix {n : ℕ} (t : FiniteType n) (j : Fin n) :
    (simpleRootMatrix t).columnVector j = toAmbient t (simpleRoot t j) := rfl

/-- The columns of `simpleRootMatrix` span the image of the model space (`rrfprojection`). -/
theorem span_columnVector_simpleRootMatrix {n : ℕ} (t : FiniteType n) :
    span ℝ (Set.range (simpleRootMatrix t).columnVector) =
      LinearMap.range (toAmbient t).toLinearMap := by
  have hr : Set.range (simpleRootMatrix t).columnVector =
      (toAmbient t).toLinearMap '' Set.range (simpleRoot t) := by
    rw [← Set.range_comp]
    rfl
  rw [hr, ← Submodule.map_span, (base t).span_eq_top, Submodule.map_top]

/-- Step `rrfinvertible`: the simple roots are independent, so `A` has trivial kernel. -/
theorem simpleRootMatrix_mulVec_injective {n : ℕ} (t : FiniteType n) :
    Function.Injective (simpleRootMatrix t).mulVec := by
  intro c d h
  have he : toAmbient t (∑ j, c j • simpleRoot t j) = toAmbient t (∑ j, d j • simpleRoot t j) := by
    simp only [map_sum, map_smul, ← columnVector_simpleRootMatrix, ← toLp_mulVec_eq_sum, h]
  have hs := (toAmbient t).injective he
  exact funext ((Fintype.linearIndependent_iffₛ.mp (base t).linearIndependent) c d hs)

/-- The action of the left side of `eq:rational-frame` on a coordinate vector
(`rrfleft`). -/
theorem toLp_halfRootSum_mulVec {n : ℕ} (t : FiniteType n) (x : Fin (ambientDim t) → ℝ) :
    WithLp.toLp 2 (halfRootSum t *ᵥ x) = (1 / 2 : ℝ) • ∑ r : roots t,
      (⟪toAmbient t r, WithLp.toLp 2 x⟫ / ‖toAmbient t r‖ ^ 2) • toAmbient t r := by
  ext i
  simp only [halfRootSum, smul_mulVec, sum_mulVec, vecMulVec_mulVec, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, dotProduct, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, WithLp.ofLp_smul]
  congr 1
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [div_eq_inv_mul]
  simp only [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Equation `eq:rational-frame` of Remark 3.11: for every model of `eq:list`, with `N`
lines and rank `n`, in its coordinate space,
`(1/2) ∑_{α ∈ Φ} α αᵀ / ‖α‖² = (N / n) A (Aᵀ A)⁻¹ Aᵀ` for the matrix `A` of simple roots
(steps `rrfprojection`, `rrfleft`, `rrfequality`). -/
theorem halfRootSum_eq {n : ℕ} (t : FiniteType n) :
    halfRootSum t = ((lineCount t : ℝ) / n) • (simpleRootMatrix t *
      ((simpleRootMatrix t)ᵀ * simpleRootMatrix t)⁻¹ * (simpleRootMatrix t)ᵀ) := by
  apply mulVec_injective
  funext x
  have key : WithLp.toLp 2 (halfRootSum t *ᵥ x) = WithLp.toLp 2 ((((lineCount t : ℝ) / n) •
      (simpleRootMatrix t * ((simpleRootMatrix t)ᵀ * simpleRootMatrix t)⁻¹ *
        (simpleRootMatrix t)ᵀ)) *ᵥ x) := by
    rw [toLp_halfRootSum_mulVec, half_rootSum_eq_smul_starProjection (isRootSet t)
      (isIndecomposable t) (toAmbient t), smul_mulVec, WithLp.toLp_smul,
      projection_mulVec_eq_starProjection _ (simpleRootMatrix_mulVec_injective t),
      span_columnVector_simpleRootMatrix, RootSetModel.numLines t, finrank_space]
  simpa using congrArg WithLp.ofLp key

/-- Integer coordinates scaled by a rational number are rational (step `rrfrational`). -/
theorem exists_rat_integerVector {m : ℕ} (c : ℚ) (v : Fin m → ℤ) :
    ∃ y : Fin m → ℚ, ∀ i, LineSystem.integerVector (c : ℝ) v i = y i :=
  ⟨fun i ↦ c * v i, fun i ↦ by simp [LineSystem.integerVector]⟩

/-- Step `rrfrational` of Remark 3.11: every model root has rational coordinates. -/
theorem exists_rat_coordinates {n : ℕ} (t : FiniteType n) :
    ∀ r ∈ roots t, ∃ y : Fin (ambientDim t) → ℚ, ∀ i, toAmbient t r i = y i := by
  cases t with
  | a n _ =>
    rintro ⟨r, hrE⟩ ⟨a, ha⟩
    have ha' : LineSystem.integerVector 1 (LineSystem.anRoot a) = r := ha
    obtain ⟨y, hy⟩ := exists_rat_integerVector 1 (LineSystem.anRoot a)
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, ← ha']
    simp
  | b n _ =>
    intro r hr
    change EuclideanSpace ℝ (Fin n) at r
    change r ∈ axisRoots n 1 ∪ Dn n at hr
    obtain ⟨w, hw⟩ := exists_integerVector_of_mem_axisRoots_union_Dn 1 (by simpa using hr)
    obtain ⟨y, hy⟩ := exists_rat_integerVector 1 w
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, hw]
    simp
  | c n _ =>
    intro r hr
    change EuclideanSpace ℝ (Fin n) at r
    change r ∈ axisRoots n 2 ∪ Dn n at hr
    obtain ⟨w, hw⟩ := exists_integerVector_of_mem_axisRoots_union_Dn 2 (by simpa using hr)
    obtain ⟨y, hy⟩ := exists_rat_integerVector 1 w
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, hw]
    simp
  | d n _ =>
    intro r hr
    change EuclideanSpace ℝ (Fin n) at r
    change r ∈ Dn n at hr
    obtain ⟨w, hw⟩ := exists_integerVector_of_mem_axisRoots_union_Dn 1 (Or.inr hr)
    obtain ⟨y, hy⟩ := exists_rat_integerVector 1 w
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, hw]
    simp
  | e₆ =>
    rintro ⟨r, hrE⟩ ⟨a, ha⟩
    have ha' : LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a) = r := ha
    obtain ⟨y, hy⟩ := exists_rat_integerVector (1 / 2) (LineSystem.e₈Root a)
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, ← ha']
    simp
  | e₇ =>
    rintro ⟨r, hrE⟩ ⟨a, ha⟩
    have ha' : LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a) = r := ha
    obtain ⟨y, hy⟩ := exists_rat_integerVector (1 / 2) (LineSystem.e₈Root a)
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, ← ha']
    simp
  | e₈ =>
    intro r hr
    change EuclideanSpace ℝ (Fin 8) at r
    change r ∈ E₈ at hr
    obtain ⟨a, ha⟩ := hr
    obtain ⟨y, hy⟩ := exists_rat_integerVector (1 / 2) (LineSystem.e₈Root a)
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, ← ha]
    simp
  | f₄ =>
    intro r hr
    change EuclideanSpace ℝ (Fin 4) at r
    change r ∈ F₄ at hr
    rw [F₄_eq_range] at hr
    obtain ⟨a, ha⟩ := hr
    obtain ⟨y, hy⟩ := exists_rat_integerVector (1 / 2) (fRootEntries a)
    refine ⟨y, fun i ↦ ?_⟩
    change r i = y i
    rw [← hy i, ← ha]
    simp
  | g₂ =>
    intro r hr
    change g₂Space at r
    change r ∈ G₂ at hr
    rw [G₂_eq_range] at hr
    obtain ⟨a, rfl⟩ := hr
    obtain ⟨y, hy⟩ := exists_rat_integerVector 1 (gRootEntries a)
    refine ⟨y, fun i ↦ ?_⟩
    change LineSystem.integerVector 1 (gRootEntries a) i = y i
    rw [← hy i]
    simp

/-- Step `rrfrational` of Remark 3.11: all entries of `eq:rational-frame` are rational. -/
theorem halfRootSum_rational {n : ℕ} (t : FiniteType n) :
    ∃ R : Matrix (Fin (ambientDim t)) (Fin (ambientDim t)) ℚ,
      R.map (Rat.cast : ℚ → ℝ) = halfRootSum t := by
  choose y hy using exists_rat_coordinates t
  have hy' (r : roots t) (i : Fin (ambientDim t)) : toAmbient t r i = y r r.2 i := hy r r.2 i
  refine ⟨(1 / 2 : ℚ) • ∑ r : roots t, (y r r.2 ⬝ᵥ y r r.2)⁻¹ •
    vecMulVec (y r r.2) (y r r.2), ?_⟩
  have hn (r : roots t) : ‖toAmbient t r‖ ^ 2 = ((y r r.2 ⬝ᵥ y r r.2 : ℚ) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hy', dotProduct]
    push_cast
    rfl
  ext i j
  simp only [map_apply, halfRootSum, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    hy', hn, smul_eq_mul]
  push_cast
  rfl

/-- Step `rrfrational` of Remark 3.11: the simple-root matrix has rational entries. -/
theorem exists_rat_simpleRootMatrix {n : ℕ} (t : FiniteType n) :
    ∃ A : Matrix (Fin (ambientDim t)) (Fin n) ℚ,
      A.map (Rat.cast : ℚ → ℝ) = simpleRootMatrix t := by
  choose y hy using fun j ↦ exists_rat_coordinates t (simpleRoot t j) ((base t).mem j)
  exact ⟨fun i j ↦ y j i, Matrix.ext fun i j ↦ (hy j i).symm⟩

/-- Step `rrfrational` of Remark 3.11: the inverse Gram matrix of the simple roots has
rational entries, by the determinant and adjugate formula. -/
theorem exists_rat_inv_gram_simpleRootMatrix {n : ℕ} (t : FiniteType n) :
    ∃ Q : Matrix (Fin n) (Fin n) ℚ,
      Q.map (Rat.cast : ℚ → ℝ) = ((simpleRootMatrix t)ᵀ * simpleRootMatrix t)⁻¹ := by
  obtain ⟨A, hA⟩ := exists_rat_simpleRootMatrix t
  change A.map (Rat.castHom ℝ) = simpleRootMatrix t at hA
  let Q := Aᵀ * A
  have hQ : Q.map (Rat.cast : ℚ → ℝ) = (simpleRootMatrix t)ᵀ * simpleRootMatrix t := by
    change (Aᵀ * A).map (Rat.castHom ℝ) = _
    rw [Matrix.map_mul, transpose_map, hA]
  have hdet : (Q.map (Rat.cast : ℚ → ℝ)).det = (Q.det : ℝ) :=
    ((Rat.castHom ℝ).map_det Q).symm
  have hadj : (Q.map (Rat.cast : ℚ → ℝ)).adjugate = Q.adjugate.map (Rat.cast : ℚ → ℝ) :=
    ((Rat.castHom ℝ).map_adjugate Q).symm
  refine ⟨Q⁻¹, ?_⟩
  rw [← hQ, inv_def, inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv, hdet, hadj]
  ext i j
  simp only [map_apply, Matrix.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_inv]

-- Remark 3.11, comp:rem-rational-frame
/-- The rational coordinate frame, `comp:rem-rational-frame` of Remark 3.11 of [CGSS]: for
every model of `eq:list`, with `N` lines and rank `n`, in its coordinate space (which may be
larger than its span), `(1/2) ∑_{α ∈ Φ} α αᵀ / ‖α‖² = (N / n) A (Aᵀ A)⁻¹ Aᵀ` for the matrix
`A` with the simple roots as columns. The common matrix, `A`, and `(Aᵀ A)⁻¹` all have
rational entries (step `rrfrational`). -/
theorem rational_frame {n : ℕ} (t : FiniteType n) :
    halfRootSum t = ((lineCount t : ℝ) / n) • (simpleRootMatrix t *
      ((simpleRootMatrix t)ᵀ * simpleRootMatrix t)⁻¹ * (simpleRootMatrix t)ᵀ) ∧
    (∃ R : Matrix (Fin (ambientDim t)) (Fin (ambientDim t)) ℚ,
      R.map (Rat.cast : ℚ → ℝ) = halfRootSum t) ∧
    (∃ A : Matrix (Fin (ambientDim t)) (Fin n) ℚ,
      A.map (Rat.cast : ℚ → ℝ) = simpleRootMatrix t) ∧
    (∃ Q : Matrix (Fin n) (Fin n) ℚ,
      Q.map (Rat.cast : ℚ → ℝ) = ((simpleRootMatrix t)ᵀ * simpleRootMatrix t)⁻¹) :=
  ⟨halfRootSum_eq t, halfRootSum_rational t, exists_rat_simpleRootMatrix t,
    exists_rat_inv_gram_simpleRootMatrix t⟩

end RootSetModel
