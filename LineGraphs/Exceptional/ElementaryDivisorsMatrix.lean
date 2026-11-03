/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.ElementaryDivisorsAlgebra

/-! # Smith coefficients of an integral Gram factorization

The factorization argument in Lemma `lem:snf` (Lemma 2.3) of [Exc].
-/

open Module Submodule Matrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

-- Lemma 2.3 [Exc]
/-- Lemma `lem:snf` (Lemma 2.3) of [Exc]: if the columns of `U` generate
the integral coordinate lattice and `F` is nonsingular, the nonzero Smith
coefficients of `Uᵀ F U` have product `|det F|`. -/
theorem prod_smith_coeffs_eq_natAbs_det (U : Matrix ι κ ℤ) (F : Matrix ι ι ℤ)
    (hU : Function.Surjective U.mulVecLin) (hF : F.det ≠ 0) {r : ℕ}
    (s : Basis.SmithNormalForm (LinearMap.range (Uᵀ * F * U).mulVecLin) κ r) :
    ∏ i, (s.a i).natAbs = F.det.natAbs := by
  classical
  choose w hw using fun i : ι ↦ hU (Pi.single i 1)
  let R : Matrix κ ι ℤ := fun j i ↦ w i j
  have hUR : U * R = 1 := by
    ext i j
    change (∑ k, U i k * w j k) = if i = j then 1 else 0
    simpa only [mulVecLin_apply, mulVec, dotProduct, Pi.single_apply, eq_comm]
      using congrFun (hw j) i
  have hRU : Rᵀ * Uᵀ = 1 := by rw [← transpose_mul, hUR, transpose_one]
  let J := Uᵀ
  let L := Rᵀ
  let N := LinearMap.range (Uᵀ * F * U).mulVecLin
  let P := LinearMap.range J.mulVecLin
  have hLJ (z : ι → ℤ) : L *ᵥ (J *ᵥ z) = z := by
    rw [mulVec_mulVec, hRU, one_mulVec]
  have hJ : Function.Injective J.mulVecLin := by
    intro z z' hz
    have hh := congrArg (fun v ↦ L *ᵥ v) hz
    exact (hLJ z).symm.trans (hh.trans (hLJ z'))
  have hNP : N ≤ P := by
    rintro z ⟨w, rfl⟩
    exact ⟨F *ᵥ (U *ᵥ w),
      by simp only [mulVecLin_apply, mulVec_mulVec, J, Matrix.mul_assoc]⟩
  have hsat : ∀ (a : ℤ), a ≠ 0 → ∀ z : κ → ℤ, a • z ∈ P → z ∈ P := by
    rintro a ha z ⟨v, hv⟩
    change J *ᵥ v = a • z at hv
    have hv' : v = a • (L *ᵥ z) := by
      have hh := congrArg (fun t ↦ L *ᵥ t) hv
      rw [hLJ, mulVec_smul] at hh
      exact hh
    refine ⟨L *ᵥ z, ?_⟩
    change J *ᵥ (L *ᵥ z) = z
    rw [hv', mulVec_smul] at hv
    ext i
    exact mul_left_cancel₀ ha (congrFun hv i)
  have hindex : ∀ z ∈ P, F.det • z ∈ N := by
    rintro z ⟨v, rfl⟩
    refine ⟨R *ᵥ (F.adjugate *ᵥ v), ?_⟩
    change (Uᵀ * F * U) *ᵥ (R *ᵥ (F.adjugate *ᵥ v)) = F.det • (Uᵀ *ᵥ v)
    calc
      _ = Uᵀ *ᵥ (F *ᵥ ((U * R) *ᵥ (F.adjugate *ᵥ v))) := by
        simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = Uᵀ *ᵥ ((F * F.adjugate) *ᵥ v) := by
        rw [hUR, one_mulVec]
        simp only [mulVec_mulVec]
      _ = _ := by rw [mul_adjugate, smul_mulVec, one_mulVec, mulVec_smul]
  have hNmap : N.toAddSubgroup =
      F.mulVecLin.toAddMonoidHom.range.map J.mulVecLin.toAddMonoidHom := by
    ext z
    change (∃ w, (Uᵀ * F * U) *ᵥ w = z) ↔
      ∃ v, (∃ w, F *ᵥ w = v) ∧ J *ᵥ v = z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨F *ᵥ (U *ᵥ v), ⟨U *ᵥ v, rfl⟩,
        by simp only [mulVec_mulVec, J, Matrix.mul_assoc]⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      obtain ⟨w, hw⟩ := hU v
      refine ⟨w, ?_⟩
      rw [← mulVec_mulVec, ← mulVec_mulVec, show U *ᵥ w = v from hw]
  have hPmap : P.toAddSubgroup =
      (⊤ : AddSubgroup (ι → ℤ)).map J.mulVecLin.toAddMonoidHom := by
    ext z
    simp [P, LinearMap.mem_range]
  calc
    ∏ i, (s.a i).natAbs = N.toAddSubgroup.relIndex P.toAddSubgroup :=
      s.prod_natAbs_eq_relIndex_of_smul_mem P hNP hsat ⟨F.det, hF, hindex⟩
    _ = F.mulVecLin.toAddMonoidHom.range.relIndex ⊤ := by
      rw [hNmap, hPmap, AddSubgroup.relIndex_map_map_of_injective _ _ hJ]
    _ = F.det.natAbs := by rw [AddSubgroup.relIndex_top_right, index_range_mulVec F hF]

end Matrix
