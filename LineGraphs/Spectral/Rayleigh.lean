/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Multiplicity
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Rayleigh extrema and equality

Theorem 4.1 of the spectral toolkit (`cgss/proofs/spectraltools/spectraltools-lamport.tex`,
`thm:rayleigh`). The Rayleigh quotient of `x : n → ℝ` is `x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x)`. The
coordinates of `x` in an orthonormal eigenbasis `u` are `u.repr (toLp 2 x)`. The supremum and
infimum statements are in the form of Mathlib's `Analysis/InnerProductSpace/Rayleigh.lean`, over
the nonzero vectors of `EuclideanSpace ℝ n`, for the operator `A.toEuclideanLin`.
-/

open Module Module.End

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Coordinates

variable {I : Type*} [Fintype I] {A : Matrix n n ℝ}
  (u : OrthonormalBasis I ℝ (EuclideanSpace ℝ n)) (μ : I → ℝ)

/-- Theorem 4.1 of the spectral toolkit, the expansion behind steps `ray-numerator` and
`ray-uppereigen`: in an orthonormal eigenbasis, `Ay = ∑ᵢ λᵢ bᵢ vᵢ` for the Euclidean operator. -/
theorem toEuclideanLin_eq_sum_of_orthonormal_eigenbasis
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) (y : EuclideanSpace ℝ n) :
    A.toEuclideanLin y = ∑ i, (μ i * u.repr y i) • u i := by
  -- The eigenvector equations for the Euclidean operator.
  have hT : ∀ j, A.toEuclideanLin (u j) = μ j • u j := fun j => by
    apply WithLp.ofLp_injective 2
    simp [toLpLin_apply, h j]
  conv_lhs => rw [← u.sum_repr y]
  simp only [map_sum, map_smul, hT, smul_smul, mul_comm]

omit [DecidableEq n] in
/-- Theorem 4.1 of the spectral toolkit, step `ray-numerator`: in an orthonormal eigenbasis,
`xᵀAx = ∑ᵢ λᵢ bᵢ²`. -/
theorem dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, μ i * u.repr (WithLp.toLp 2 x) i ^ 2 := by
  classical
  set y : EuclideanSpace ℝ n := WithLp.toLp 2 x
  -- Expand `Ax = ∑ᵢ bᵢ λᵢ vᵢ`.
  have hTy := toEuclideanLin_eq_sum_of_orthonormal_eigenbasis u μ h y
  have hx : x ⬝ᵥ (A *ᵥ x) = inner ℝ y (A.toEuclideanLin y) := by
    simp only [dotProduct, toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      mul_comm, y]
  -- Orthonormality: `⟪x, vᵢ⟫ = bᵢ`.
  rw [hx, hTy, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, real_inner_comm, ← u.repr_apply_apply]
  ring

omit [DecidableEq n] in
/-- Theorem 4.1 of the spectral toolkit, step `ray-denominator`: `‖x‖² = ∑ᵢ bᵢ²`. -/
theorem dotProduct_self_eq_sum_of_orthonormal_basis (x : n → ℝ) :
    x ⬝ᵥ x = ∑ i, u.repr (WithLp.toLp 2 x) i ^ 2 := by
  classical
  have h := dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis (A := 1) u (fun _ => 1)
    (fun j => by rw [one_mulVec, one_smul]) x
  simpa using h

omit [DecidableEq n] in
/-- Theorem 4.1 of the spectral toolkit, steps `ray-uppereigen` and `ray-lowereigen`: in an
orthonormal eigenbasis, `Ax = cx` iff `λᵢ bᵢ = c bᵢ` for every `i`. -/
theorem mulVec_eq_smul_iff_of_orthonormal_eigenbasis
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) (x : n → ℝ) (c : ℝ) :
    A *ᵥ x = c • x ↔
      ∀ i, μ i * u.repr (WithLp.toLp 2 x) i = c * u.repr (WithLp.toLp 2 x) i := by
  classical
  set y : EuclideanSpace ℝ n := WithLp.toLp 2 x
  -- The coordinates of `Ax` are `λᵢ bᵢ`.
  have hcoord : ∀ i, u.repr (A.toEuclideanLin y) i = μ i * u.repr y i := fun i => by
    rw [toEuclideanLin_eq_sum_of_orthonormal_eigenbasis u μ h y, u.repr_apply_apply, inner_sum]
    simp only [real_inner_smul_right, orthonormal_iff_ite.mp u.orthonormal, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hAx : A *ᵥ x = c • x ↔ A.toEuclideanLin y = c • y := by
    constructor
    · intro hx
      apply WithLp.ofLp_injective 2
      simp [y, toLpLin_apply, hx]
    · intro hy
      have := congrArg WithLp.ofLp hy
      simpa [y, toLpLin_apply] using this
  rw [hAx]
  constructor
  · intro hy i
    rw [← hcoord, hy, map_smul]
    rfl
  · intro hc
    apply u.repr.injective
    ext i
    rw [hcoord, hc, map_smul]
    rfl

/-- The Rayleigh quotient of Mathlib's `Rayleigh.lean` for `A.toEuclideanLin` is the coordinate
quotient (step `ray-library-identify`). No symmetry is needed. -/
theorem re_inner_toEuclideanLin_div (x : EuclideanSpace ℝ n) :
    RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖x‖ ^ 2 =
      x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) / (x.ofLp ⬝ᵥ x.ofLp) := by
  have h1 : inner ℝ (A.toEuclideanLin x) x = x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
    simp [PiLp.inner_apply, dotProduct, toLpLin_apply]
  have h2 : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  rw [h1, h2]
  rfl

end Coordinates

namespace IsHermitian

variable {A : Matrix n n ℝ} (hA : A.IsHermitian) [Nonempty n]

/-- Theorem 4.1 of the spectral toolkit, step `ray-uppergap`: in any orthonormal eigenbasis,
`λmax ‖x‖² - xᵀAx = ∑ᵢ (λmax - λᵢ) bᵢ²`. -/
theorem largestEigenvalue_mul_sub_eq_sum {I : Type*} [Fintype I]
    (u : OrthonormalBasis I ℝ (EuclideanSpace ℝ n)) (μ : I → ℝ)
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) (x : n → ℝ) :
    hA.largestEigenvalue * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) =
      ∑ i, (hA.largestEigenvalue - μ i) * u.repr (WithLp.toLp 2 x) i ^ 2 := by
  rw [dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis u μ h,
    dotProduct_self_eq_sum_of_orthonormal_basis u, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Theorem 4.1 of the spectral toolkit, step `ray-lowergap`: in any orthonormal eigenbasis,
`xᵀAx - λmin ‖x‖² = ∑ᵢ (λᵢ - λmin) bᵢ²`. -/
theorem sub_leastEigenvalue_mul_eq_sum {I : Type*} [Fintype I]
    (u : OrthonormalBasis I ℝ (EuclideanSpace ℝ n)) (μ : I → ℝ)
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) - hA.leastEigenvalue * (x ⬝ᵥ x) =
      ∑ i, (μ i - hA.leastEigenvalue) * u.repr (WithLp.toLp 2 x) i ^ 2 := by
  rw [dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis u μ h,
    dotProduct_self_eq_sum_of_orthonormal_basis u, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Theorem 4.1 of the spectral toolkit, step `ray-members`: the eigenvalues of an orthonormal
eigenbasis lie between `λmin` and `λmax`. -/
theorem mem_Icc_of_orthonormal_eigenbasis {I : Type*} [Fintype I]
    (u : OrthonormalBasis I ℝ (EuclideanSpace ℝ n)) (μ : I → ℝ)
    (h : ∀ j, A *ᵥ ⇑(u j) = μ j • ⇑(u j)) (i : I) :
    hA.leastEigenvalue ≤ μ i ∧ μ i ≤ hA.largestEigenvalue := by
  -- Theorem 2.2, step `mul-anybasis`: `μ i ∈ Spec(A)`.
  have hmem : μ i ∈ A.spectrumMultiset := by
    rw [spectrumMultiset_eq_of_orthonormal_eigenbasis u μ h]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val _, rfl⟩
  -- Lemma 2.4.
  exact ⟨hA.leastEigenvalue_le_of_mem hmem, hA.le_largestEigenvalue_of_mem hmem⟩

/-- Theorem 4.1 of the spectral toolkit, step `ray-upper` (without division):
`xᵀAx ≤ λmax ‖x‖²`. -/
theorem dotProduct_mulVec_le_largestEigenvalue_mul (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.largestEigenvalue * (x ⬝ᵥ x) := by
  -- Step `ray-uppergap` in Mathlib's eigenbasis.
  have hgap := hA.largestEigenvalue_mul_sub_eq_sum hA.eigenvectorBasis hA.eigenvalues
    hA.mulVec_eigenvectorBasis x
  -- Step `ray-uppert`: every summand is nonnegative.
  have hterm : ∀ i, 0 ≤ (hA.largestEigenvalue - hA.eigenvalues i) *
      hA.eigenvectorBasis.repr (WithLp.toLp 2 x) i ^ 2 := fun i =>
    mul_nonneg (sub_nonneg.mpr (hA.mem_Icc_of_orthonormal_eigenbasis _ _
      hA.mulVec_eigenvectorBasis i).2) (sq_nonneg _)
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
  linarith

/-- Theorem 4.1 of the spectral toolkit, step `ray-lower` (without division):
`λmin ‖x‖² ≤ xᵀAx`. -/
theorem leastEigenvalue_mul_le_dotProduct_mulVec (x : n → ℝ) :
    hA.leastEigenvalue * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  -- Step `ray-lowergap` in Mathlib's eigenbasis.
  have hgap := hA.sub_leastEigenvalue_mul_eq_sum hA.eigenvectorBasis hA.eigenvalues
    hA.mulVec_eigenvectorBasis x
  -- Step `ray-lowert`: every summand is nonnegative.
  have hterm : ∀ i, 0 ≤ (hA.eigenvalues i - hA.leastEigenvalue) *
      hA.eigenvectorBasis.repr (WithLp.toLp 2 x) i ^ 2 := fun i =>
    mul_nonneg (sub_nonneg.mpr (hA.mem_Icc_of_orthonormal_eigenbasis _ _
      hA.mulVec_eigenvectorBasis i).1) (sq_nonneg _)
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
  linarith

/-- Theorem 4.1 of the spectral toolkit: `R_A(x) ≤ λmax(A)` for `x ≠ 0`. -/
theorem rayleigh_le_largestEigenvalue {x : n → ℝ} (hx : x ≠ 0) :
    x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) ≤ hA.largestEigenvalue := by
  -- Step `ray-denominator`.
  have hpos : 0 < x ⬝ᵥ x := by simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx
  -- Step `ray-upper`.
  have hle := hA.dotProduct_mulVec_le_largestEigenvalue_mul x
  exact (div_le_iff₀ hpos).mpr hle

/-- Theorem 4.1 of the spectral toolkit: `λmin(A) ≤ R_A(x)` for `x ≠ 0`. -/
theorem leastEigenvalue_le_rayleigh {x : n → ℝ} (hx : x ≠ 0) :
    hA.leastEigenvalue ≤ x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) := by
  -- Step `ray-denominator`.
  have hpos : 0 < x ⬝ᵥ x := by simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx
  -- Step `ray-lower`.
  have hle := hA.leastEigenvalue_mul_le_dotProduct_mulVec x
  exact (le_div_iff₀ hpos).mpr hle

/-- Theorem 4.1 of the spectral toolkit, the equality case of step `ray-upper`:
`R_A(x) = λmax(A)` iff `Ax = λmax(A) x`, for `x ≠ 0`. -/
theorem rayleigh_eq_largestEigenvalue_iff {x : n → ℝ} (hx : x ≠ 0) :
    x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) = hA.largestEigenvalue ↔ A *ᵥ x = hA.largestEigenvalue • x := by
  set u := hA.eigenvectorBasis
  set b := u.repr (WithLp.toLp 2 x)
  have hpos : 0 < x ⬝ᵥ x := by simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx
  -- Step `ray-uppergap`.
  have hgap := hA.largestEigenvalue_mul_sub_eq_sum u hA.eigenvalues hA.mulVec_eigenvectorBasis x
  -- Step `ray-uppert`.
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ (hA.largestEigenvalue - hA.eigenvalues i) * b i ^ 2 :=
    fun i _ => mul_nonneg (sub_nonneg.mpr (hA.mem_Icc_of_orthonormal_eigenbasis _ _
      hA.mulVec_eigenvectorBasis i).2) (sq_nonneg _)
  -- Step `ray-upperzero`: the gap vanishes iff every summand does.
  have hzero : (∑ i, (hA.largestEigenvalue - hA.eigenvalues i) * b i ^ 2) = 0 ↔
      ∀ i, hA.eigenvalues i * b i = hA.largestEigenvalue * b i := by
    rw [Finset.sum_eq_zero_iff_of_nonneg hterm]
    refine forall_congr' fun i => ?_
    simp only [Finset.mem_univ, true_implies, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
      sub_eq_zero]
    constructor
    · rintro (h | h) <;> simp [h]
    · intro h
      by_cases hb : b i = 0
      · exact Or.inr hb
      · exact Or.inl (mul_right_cancel₀ hb h).symm
  -- Step `ray-uppereigen`.
  have heig := mulVec_eq_smul_iff_of_orthonormal_eigenbasis u hA.eigenvalues
    hA.mulVec_eigenvectorBasis x hA.largestEigenvalue
  rw [heig, ← hzero, ← hgap, div_eq_iff hpos.ne', sub_eq_zero, eq_comm]

/-- Theorem 4.1 of the spectral toolkit, the equality case of step `ray-lower`:
`R_A(x) = λmin(A)` iff `Ax = λmin(A) x`, for `x ≠ 0`. -/
theorem rayleigh_eq_leastEigenvalue_iff {x : n → ℝ} (hx : x ≠ 0) :
    x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) = hA.leastEigenvalue ↔ A *ᵥ x = hA.leastEigenvalue • x := by
  set u := hA.eigenvectorBasis
  set b := u.repr (WithLp.toLp 2 x)
  have hpos : 0 < x ⬝ᵥ x := by simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx
  -- Step `ray-lowergap`.
  have hgap := hA.sub_leastEigenvalue_mul_eq_sum u hA.eigenvalues hA.mulVec_eigenvectorBasis x
  -- Step `ray-lowert`.
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ (hA.eigenvalues i - hA.leastEigenvalue) * b i ^ 2 :=
    fun i _ => mul_nonneg (sub_nonneg.mpr (hA.mem_Icc_of_orthonormal_eigenbasis _ _
      hA.mulVec_eigenvectorBasis i).1) (sq_nonneg _)
  -- Step `ray-lowerzero`.
  have hzero : (∑ i, (hA.eigenvalues i - hA.leastEigenvalue) * b i ^ 2) = 0 ↔
      ∀ i, hA.eigenvalues i * b i = hA.leastEigenvalue * b i := by
    rw [Finset.sum_eq_zero_iff_of_nonneg hterm]
    refine forall_congr' fun i => ?_
    simp only [Finset.mem_univ, true_implies, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
      sub_eq_zero]
    constructor
    · rintro (h | h) <;> simp [h]
    · intro h
      by_cases hb : b i = 0
      · exact Or.inr hb
      · exact Or.inl (mul_right_cancel₀ hb h)
  -- Step `ray-lowereigen`.
  have heig := mulVec_eq_smul_iff_of_orthonormal_eigenbasis u hA.eigenvalues
    hA.mulVec_eigenvectorBasis x hA.leastEigenvalue
  rw [heig, ← hzero, ← hgap, div_eq_iff hpos.ne', sub_eq_zero]

/-- The sorted eigenvector `w₀` (step `ray-witness`). -/
theorem mulVec_sortedEigenvectorBasis_zero :
    A *ᵥ ⇑(hA.sortedEigenvectorBasis ⟨0, Fintype.card_pos⟩) =
      hA.largestEigenvalue • ⇑(hA.sortedEigenvectorBasis ⟨0, Fintype.card_pos⟩) :=
  hA.mulVec_sortedEigenvectorBasis _

/-- Theorem 4.1 of the spectral toolkit, step `ray-attain`: `λmax` is the supremum of the
Rayleigh quotient over nonzero vectors, in the form of Mathlib's `Rayleigh.lean`. -/
theorem iSup_rayleigh_eq_largestEigenvalue :
    (⨆ x : {x : EuclideanSpace ℝ n // x ≠ 0},
      RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) =
      hA.largestEigenvalue := by
  have hT : A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  -- Step `ray-sup-library`: the supremum is an eigenvalue of `A.toEuclideanLin`.
  have hsup := hT.hasEigenvalue_iSup_of_finiteDimensional
  set s := ⨆ x : {x : EuclideanSpace ℝ n // x ≠ 0},
    RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2
  -- Hence `s ∈ Spec(A)` (Theorem 2.2) and `s ≤ λmax` (Lemma 2.4).
  have hle : s ≤ hA.largestEigenvalue := by
    obtain ⟨v, hvv⟩ := hsup.exists_hasEigenvector
    have hv := hvv.apply_eq_smul
    have hv0 := hvv.2
    apply hA.le_largestEigenvalue_of_mem
    refine (hA.mem_spectrumMultiset_iff).mpr ⟨v.ofLp, fun h => hv0 ?_, ?_⟩
    · exact WithLp.ofLp_injective 2 (by simpa using h)
    · have := congrArg WithLp.ofLp hv
      simpa [toLpLin_apply] using this
  -- Step `ray-uniform` (bounded above) and step `ray-witness`.
  have hbdd : BddAbove (Set.range fun x : {x : EuclideanSpace ℝ n // x ≠ 0} =>
      RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) := by
    refine ⟨hA.largestEigenvalue, ?_⟩
    rintro _ ⟨x, rfl⟩
    dsimp only
    rw [re_inner_toEuclideanLin_div]
    exact hA.rayleigh_le_largestEigenvalue fun h => x.2 (WithLp.ofLp_injective 2 (by simpa using h))
  have hwit : hA.largestEigenvalue ≤ s := by
    let w := hA.sortedEigenvectorBasis ⟨0, Fintype.card_pos⟩
    have hw : w ≠ 0 := (hA.sortedEigenvectorBasis).orthonormal.ne_zero _
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨w, hw⟩)
    rw [re_inner_toEuclideanLin_div]
    symm
    rw [hA.rayleigh_eq_largestEigenvalue_iff
      fun h => hw (WithLp.ofLp_injective 2 (by simpa using h))]
    exact hA.mulVec_sortedEigenvectorBasis_zero
  exact le_antisymm hle hwit

/-- The sorted eigenvector `w_{n-1}` (step `ray-witness`). -/
theorem mulVec_sortedEigenvectorBasis_last :
    A *ᵥ ⇑(hA.sortedEigenvectorBasis (lastIndex n)) =
      hA.leastEigenvalue • ⇑(hA.sortedEigenvectorBasis (lastIndex n)) :=
  hA.mulVec_sortedEigenvectorBasis _

/-- Theorem 4.1 of the spectral toolkit, step `ray-attain`: `λmin` is the infimum of the
Rayleigh quotient over nonzero vectors, in the form of Mathlib's `Rayleigh.lean`. -/
theorem iInf_rayleigh_eq_leastEigenvalue :
    (⨅ x : {x : EuclideanSpace ℝ n // x ≠ 0},
      RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) =
      hA.leastEigenvalue := by
  have hT : A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  -- Step `ray-inf-library`: the infimum is an eigenvalue of `A.toEuclideanLin`.
  have hinf := hT.hasEigenvalue_iInf_of_finiteDimensional
  set s := ⨅ x : {x : EuclideanSpace ℝ n // x ≠ 0},
    RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2
  -- Hence `s ∈ Spec(A)` (Theorem 2.2) and `λmin ≤ s` (Lemma 2.4).
  have hge : hA.leastEigenvalue ≤ s := by
    obtain ⟨v, hvv⟩ := hinf.exists_hasEigenvector
    have hv := hvv.apply_eq_smul
    have hv0 := hvv.2
    apply hA.leastEigenvalue_le_of_mem
    refine (hA.mem_spectrumMultiset_iff).mpr ⟨v.ofLp, fun h => hv0 ?_, ?_⟩
    · exact WithLp.ofLp_injective 2 (by simpa using h)
    · have := congrArg WithLp.ofLp hv
      simpa [toLpLin_apply] using this
  -- Step `ray-uniform` (bounded below) and step `ray-witness`.
  have hbdd : BddBelow (Set.range fun x : {x : EuclideanSpace ℝ n // x ≠ 0} =>
      RCLike.re (inner ℝ (A.toEuclideanLin x) x) / ‖(x : EuclideanSpace ℝ n)‖ ^ 2) := by
    refine ⟨hA.leastEigenvalue, ?_⟩
    rintro _ ⟨x, rfl⟩
    dsimp only
    rw [re_inner_toEuclideanLin_div]
    exact hA.leastEigenvalue_le_rayleigh fun h => x.2 (WithLp.ofLp_injective 2 (by simpa using h))
  have hwit : s ≤ hA.leastEigenvalue := by
    let w := hA.sortedEigenvectorBasis (lastIndex n)
    have hw : w ≠ 0 := (hA.sortedEigenvectorBasis).orthonormal.ne_zero _
    refine le_trans (ciInf_le hbdd ⟨w, hw⟩) (le_of_eq ?_)
    rw [re_inner_toEuclideanLin_div]
    rw [hA.rayleigh_eq_leastEigenvalue_iff fun h => hw (WithLp.ofLp_injective 2 (by simpa using h))]
    exact hA.mulVec_sortedEigenvectorBasis_last
  exact le_antisymm hwit hge

omit [DecidableEq n] [Nonempty n] in
include hA in
/-- Theorem 4.1 of the spectral toolkit, step `ray-orth`: eigenvectors of a symmetric matrix at
distinct eigenvalues are orthogonal. -/
theorem dotProduct_eq_zero_of_eigenvalue_ne {y z : n → ℝ} {s t : ℝ}
    (hy : A *ᵥ y = s • y) (hz : A *ᵥ z = t • z) (hst : s ≠ t) : y ⬝ᵥ z = 0 := by
  -- Step `ray-symmetric`.
  have hsym : s * (y ⬝ᵥ z) = t * (y ⬝ᵥ z) := by
    -- Step `ray-left-eigen`.
    have h1 : s * (y ⬝ᵥ z) = (A *ᵥ y) ⬝ᵥ z := by rw [hy, smul_dotProduct, smul_eq_mul]
    -- Step `ray-adjoint`.
    have h2 : (A *ᵥ y) ⬝ᵥ z = y ⬝ᵥ (A *ᵥ z) := by
      have hAt : Aᵀ = A := (isHermitian_iff_isSymm.mp hA).eq
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hAt, dotProduct_comm]
    -- Step `ray-right-eigen`.
    have h3 : y ⬝ᵥ (A *ᵥ z) = t * (y ⬝ᵥ z) := by rw [hz, dotProduct_smul, smul_eq_mul]
    rw [h1, h2, h3]
  -- Step `ray-cancel`.
  have hcancel : (s - t) * (y ⬝ᵥ z) = 0 := by rw [sub_mul, hsym, sub_self]
  exact (mul_eq_zero.mp hcancel).resolve_left (sub_ne_zero.mpr hst)

end IsHermitian

end Matrix
