/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Lattice
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Index

/-! # The modular index calculation for a lattice basis

The algebraic step in Lemma `lem:basisdet` (Lemma 2.4) of [Exc].
-/

open Module Submodule Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Lemma 2.4 [Exc]
/-- Lemma `lem:basisdet` (Lemma 2.4) of [Exc]: an integral matrix followed by
coordinatewise reduction modulo the absolute value of an integer. -/
def modularHom (K : Matrix ι ι ℤ) (D : ℤ) : (ι → ℤ) →+ (ι → ZMod D.natAbs) where
  toFun z i := ((K *ᵥ z) i : ZMod D.natAbs)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp [Matrix.mulVec_add]

-- Lemma 2.4 [Exc]
/-- Lemma `lem:basisdet` (Lemma 2.4) of [Exc]: if `K` and `W` are mutual inverses
up to `D`, reduction of `Kz` modulo `D` has kernel the column lattice of `W`. -/
theorem ker_modularHom_eq_range (K W : Matrix ι ι ℤ) {D : ℤ} (hD : D ≠ 0)
    (hKW : K * W = D • 1) (hWK : W * K = D • 1) :
    (K.modularHom D).ker = W.mulVecLin.toAddMonoidHom.range := by
  ext z
  change (fun i ↦ ((K *ᵥ z) i : ZMod D.natAbs)) = 0 ↔ ∃ w, W *ᵥ w = z
  rw [funext_iff]
  constructor
  · intro hz
    have hdvd (i : ι) : D ∣ (K *ᵥ z) i := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz i)
    choose w hw using hdvd
    refine ⟨w, ?_⟩
    have hh : D • (W *ᵥ w) = D • z := by
      rw [← Matrix.mulVec_smul, ← show K *ᵥ z = D • w from funext hw,
        Matrix.mulVec_mulVec, hWK, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    exact mul_left_cancel₀ hD (congrFun hh i)
  · rintro ⟨w, rfl⟩ i
    rw [Matrix.mulVec_mulVec, hKW, Matrix.smul_mulVec, Matrix.one_mulVec]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simp

-- Lemma 2.4 [Exc]
/-- Lemma `lem:basisdet` (Lemma 2.4) of [Exc]: the index of the column lattice
of a nonsingular integral matrix is the absolute determinant. -/
theorem index_range_mulVec (W : Matrix ι ι ℤ) (hW : W.det ≠ 0) :
    W.mulVecLin.toAddMonoidHom.range.index = W.det.natAbs := by
  let e := LinearEquiv.ofInjective W.mulVecLin (Matrix.mulVec_injective_of_det_ne_zero hW)
  have hh := Submodule.natAbs_det_equiv (LinearMap.range W.mulVecLin) e
  have he : (LinearMap.range W.mulVecLin).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap (e : (ι → ℤ) →+ LinearMap.range W.mulVecLin) =
        W.mulVecLin := by ext z i; rfl
  rw [he] at hh
  have hd : LinearMap.det W.mulVecLin = W.det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℤ ι)]
    congr 1
    ext i j
    simp [Matrix.mulVec_single]
  rw [hd] at hh
  exact hh.symm

-- Lemma 2.4 [Exc]
/-- Lemma `lem:basisdet` (Lemma 2.4) of [Exc]: the size of the modular image
is the index, hence the absolute determinant, of the column lattice. -/
theorem natCard_range_modularHom (K W : Matrix ι ι ℤ) {D : ℤ} (hD : D ≠ 0)
    (hW : W.det ≠ 0) (hKW : K * W = D • 1) (hWK : W * K = D • 1) :
    Nat.card (K.modularHom D).range = W.det.natAbs := by
  rw [← AddSubgroup.index_ker, ker_modularHom_eq_range K W hD hKW hWK,
    index_range_mulVec W hW]

-- Lemma 2.4 [Exc]
omit [DecidableEq ι] in
/-- Lemma `lem:basisdet` (Lemma 2.4) of [Exc]: a generating family of the
coordinate lattice generates the entire modular image after applying `K`. -/
theorem range_modularHom_eq_closure_columns {κ : Type*} [Fintype κ]
    (K : Matrix ι ι ℤ) (U : Matrix ι κ ℤ) (D : ℤ)
    (hU : Function.Surjective U.mulVecLin) :
    (K.modularHom D).range = AddSubgroup.closure
      (Set.range (fun u i ↦ ((K * U) i u : ZMod D.natAbs))) := by
  have hspan : span ℤ (Set.range U.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr hU
  have hgen : AddSubgroup.closure (Set.range U.col) = ⊤ := by
    rw [← span_int_eq_addSubgroupClosure, hspan]
    rfl
  calc
    (K.modularHom D).range = (⊤ : AddSubgroup (ι → ℤ)).map (K.modularHom D) := by
      ext z
      simp
    _ = (AddSubgroup.closure (Set.range U.col)).map (K.modularHom D) := by rw [hgen]
    _ = AddSubgroup.closure ((K.modularHom D) '' Set.range U.col) :=
      (K.modularHom D).map_closure _
    _ = _ := by
      congr 1
      rw [← Set.range_comp]
      rfl

end Matrix
