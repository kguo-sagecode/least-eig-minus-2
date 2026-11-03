/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.LatticeBasic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Analysis.Matrix.PosDef

/-! # The determinant of the lattice of a graph representation

Section 2 of [Exc]: integral change of basis and transport between families with
the same Gram matrix. No connectedness assumption is needed here.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace Matrix

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Section 2 [Exc]
omit [Fintype κ] in
/-- Section `sec:lattices` (Section 2) of [Exc]:
the Gram matrix of integral linear combinations. -/
theorem gram_sum_int_smul (v : ι → E) (C : Matrix ι κ ℤ) :
    gram ℝ (fun j ↦ ∑ i, C i j • v i) =
      (C.map (Int.cast : ℤ → ℝ))ᵀ * gram ℝ v * C.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [gram_apply, sum_inner, inner_sum, ← Int.cast_smul_eq_zsmul ℝ,
    real_inner_smul_left, real_inner_smul_right, mul_apply, transpose_apply,
    map_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Matrix

namespace Module.Basis

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

-- Section 2 [Exc]
omit [InnerProductSpace ℝ E] in
/-- Section `sec:lattices` (Section 2) of [Exc]:
a change of integral basis has determinant of square one. -/
theorem toMatrix_det_sq_eq_one (b c : Basis ι ℤ L) : (b.toMatrix c).det ^ 2 = 1 := by
  classical
  have hu := Matrix.isUnit_det_of_left_inverse (c.toMatrix_mul_toMatrix_flip b)
  rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
the Gram determinant does not depend on the integral basis,
including its indexing type. -/
theorem det_gram_eq (b : Basis ι ℤ L) (c : Basis κ ℤ L) :
    (Matrix.gram ℝ (fun i ↦ (b i : E))).det =
      (Matrix.gram ℝ (fun i ↦ (c i : E))).det := by
  classical
  have hs (d : Basis ι ℤ L) :
      (Matrix.gram ℝ (fun i ↦ (d i : E))).det =
        (Matrix.gram ℝ (fun i ↦ (b i : E))).det := by
    have he (j : ι) : (d j : E) = ∑ i, b.toMatrix d i j • (b i : E) := by
      have hh := congrArg L.subtype (b.sum_toMatrix_smul_self d j).symm
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using hh
    simp_rw [he]
    rw [Matrix.gram_sum_int_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      ← Int.cast_det]
    have hu : (((b.toMatrix d).det : ℝ)) ^ 2 = 1 := by
      exact_mod_cast b.toMatrix_det_sq_eq_one d
    calc
      _ = (((b.toMatrix d).det : ℝ)) ^ 2 *
          (Matrix.gram ℝ (fun i ↦ (b i : E))).det := by ring
      _ = _ := by rw [hu, one_mul]
  let e := b.indexEquiv c
  calc
    _ = (Matrix.gram ℝ (fun i ↦ ((c.reindex e.symm) i : E))).det := (hs _).symm
    _ = _ := by
      simp only [Basis.reindex_apply, Equiv.symm_symm]
      change ((Matrix.gram ℝ (fun i ↦ (c i : E))).submatrix e e).det = _
      exact Matrix.det_submatrix_equiv_self e _

end Module.Basis

namespace InnerProductSpace

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
equal Gram matrices induce an inner-product-preserving
integral linear equivalence of the generated lattices. -/
theorem exists_span_int_equiv_of_gram_eq (x : ι → E) (y : ι → F)
    (h : Matrix.gram ℝ x = Matrix.gram ℝ y) :
    ∃ e : span ℤ (Set.range x) ≃ₗ[ℤ] span ℤ (Set.range y),
      (∀ u v, ⟪(e u : F), (e v : F)⟫ = ⟪(u : E), (v : E)⟫) ∧
      ∀ i, (e ⟨x i, subset_span (Set.mem_range_self i)⟩ : F) = y i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let x' : ι → span ℤ (Set.range x) := fun i ↦ ⟨x i, subset_span (Set.mem_range_self i)⟩
  let y' : ι → span ℤ (Set.range y) := fun i ↦ ⟨y i, subset_span (Set.mem_range_self i)⟩
  let f := Fintype.linearCombination ℤ x'
  let g := Fintype.linearCombination ℤ y'
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact (span_range_subtype_eq_top_iff _ _).mpr rfl
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact (span_range_subtype_eq_top_iff _ _).mpr rfl
  have hinner (a b : ι → ℤ) : ⟪(g a : F), (g b : F)⟫ = ⟪(f a : E), (f b : E)⟫ := by
    simp only [f, g, Fintype.linearCombination_apply, coe_sum, coe_smul,
      sum_inner, inner_sum, ← Int.cast_smul_eq_zsmul ℝ,
      real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show ⟪(y' j : F), (y' i : F)⟫ = ⟪(x' j : E), (x' i : E)⟫ from
      (congrFun (congrFun h j) i).symm]
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro a ha
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hinner, LinearMap.mem_ker.mp ha]
    simp
  let T := ((LinearMap.ker f).liftQ g hk).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hT (a : ι → ℤ) : T (f a) = g a := by simp [T]
  have hTi (u v) : ⟪(T u : F), (T v : F)⟫ = ⟪(u : E), (v : E)⟫ := by
    obtain ⟨a, rfl⟩ := hf u
    obtain ⟨b, rfl⟩ := hf v
    rw [hT, hT, hinner]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro u hu
    have hh := hTi u u
    rw [LinearMap.mem_ker.mp hu] at hh
    have hz : (u : E) = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by simpa using hh.symm)
    exact Subtype.ext hz
  have hsurj : Function.Surjective T := by
    intro v
    obtain ⟨a, rfl⟩ := hg v
    exact ⟨f a, hT a⟩
  refine ⟨LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hTi, fun i ↦ ?_⟩
  change (T (x' i) : F) = (y' i : F)
  have hh := congrArg Subtype.val (hT (Pi.single i 1))
  simpa only [f, g, Fintype.linearCombination_apply_single, one_smul] using hh

end InnerProductSpace

namespace Submodule

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
the integer span of a finite family has a finite integral basis. -/
noncomputable def spanIntBasis (x : ι → E) :
    Basis (Fin (finrank ℤ (span ℤ (Set.range x)))) ℤ (span ℤ (Set.range x)) := by
  letI : Module.Finite ℤ (span ℤ (Set.range x)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range x)
  letI : IsAddTorsionFree E := .of_isTorsionFree ℝ E
  exact Module.finBasis ℤ _

end Submodule

namespace Matrix

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
an integral Gram matrix has a natural-number determinant. -/
theorem det_gram_mem_nat (v : ι → E)
    (hv : ∀ i j, ⟪v i, v j⟫ ∈ Set.range (Int.cast : ℤ → ℝ)) :
    (gram ℝ v).det ∈ Set.range (Nat.cast : ℕ → ℝ) := by
  classical
  choose C₀ hC using hv
  let C : Matrix ι ι ℤ := C₀
  have he : C.map (Int.cast : ℤ → ℝ) = gram ℝ v := by ext i j; exact hC i j
  have hd : (C.det : ℝ) = (gram ℝ v).det := by rw [Int.cast_det, he]
  have hn : 0 ≤ C.det := by
    exact_mod_cast (hd.symm ▸ (posSemidef_gram ℝ v).det_nonneg)
  lift C.det to ℕ using hn with d hd'
  exact ⟨d, by exact_mod_cast hd⟩

end Matrix

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (X : SimpleGraph V) [DecidableRel X.Adj]

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
the Gram determinant of an integral basis of the lattice
generated by a representation. It is zero when the graph has no representation. -/
noncomputable def latticeDet : ℕ := by
  classical
  exact if hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef then
    let x := (X.exists_representation_iff_posSemidef.mpr hp).choose
    ⌊(Matrix.gram ℝ (fun i ↦ (spanIntBasis x i : EuclideanSpace ℝ
      (Fin (Fintype.card V))))).det⌋₊
  else 0

variable {X} {x : V → E}

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
the graph lattice determinant is the Gram determinant of
every integral basis of every representation. This proves independence of both choices. -/
theorem IsRepresentation.latticeDet_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hx : X.IsRepresentation x) (b : Basis ι ℤ (span ℤ (Set.range x))) :
    (X.latticeDet : ℝ) = (Matrix.gram ℝ (fun i ↦ (b i : E))).det := by
  classical
  have hp := hx.posSemidef X
  let y := (X.exists_representation_iff_posSemidef.mpr hp).choose
  have hy : X.IsRepresentation y := (X.exists_representation_iff_posSemidef.mpr hp).choose_spec
  let c := spanIntBasis y
  obtain ⟨e, he, _⟩ := InnerProductSpace.exists_span_int_equiv_of_gram_eq y x (hy.trans hx.symm)
  have hgram : Matrix.gram ℝ (fun i ↦ ((c.map e) i : E)) =
      Matrix.gram ℝ (fun i ↦ (c i : EuclideanSpace ℝ (Fin (Fintype.card V)))) := by
    ext i j
    exact he (c i) (c j)
  have hd : (Matrix.gram ℝ (fun i ↦ (c i : EuclideanSpace ℝ (Fin (Fintype.card V))))).det =
      (Matrix.gram ℝ (fun i ↦ (b i : E))).det := by
    rw [← hgram]
    exact (c.map e).det_gram_eq b
  obtain ⟨d, hd'⟩ := Matrix.det_gram_mem_nat (fun i ↦ (b i : E))
    (fun i j ↦ hx.inner_mem_int_of_mem_span_int (b i).property (b j).property)
  simp only [latticeDet, dite_eq_left hp]
  change (⌊(Matrix.gram ℝ (fun i ↦ (c i : EuclideanSpace ℝ
    (Fin (Fintype.card V))))).det⌋₊ : ℝ) = _
  rw [hd, ← hd', Nat.floor_natCast]

end SimpleGraph
