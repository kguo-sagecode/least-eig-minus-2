/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Lattice

/-! # Integral coordinates in a representation lattice

The factorization `M = Uᵀ F U` in Lemmas `lem:basisdet` (Lemma 2.4) and
`lem:snf` (Lemma 2.3) of [Exc].
-/

open Module Submodule Matrix
open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

-- Lemmas 2.2 and 2.3 [Exc]
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the integral Gram matrix of a basis of the representation lattice. -/
noncomputable def IsRepresentation.latticeGramMatrix (hx : X.IsRepresentation x)
    (b : Basis ι ℤ (span ℤ (Set.range x))) : Matrix ι ι ℤ :=
  fun i j ↦ (hx.inner_mem_int_of_mem_span_int (b i).property (b j).property).choose

-- Lemmas 2.2 and 2.3 [Exc]
omit [Fintype V] [Fintype ι] [DecidableEq ι] in
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the integral Gram matrix casts to the real Gram matrix of the lattice basis. -/
theorem IsRepresentation.latticeGramMatrix_cast (hx : X.IsRepresentation x)
    (b : Basis ι ℤ (span ℤ (Set.range x))) :
    (hx.latticeGramMatrix b).map (Int.cast : ℤ → ℝ) =
      Matrix.gram ℝ (fun i ↦ (b i : E)) := by
  ext i j
  exact (hx.inner_mem_int_of_mem_span_int (b i).property (b j).property).choose_spec

-- Lemmas 2.2 and 2.3 [Exc]
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the integral basis Gram determinant is the graph lattice determinant. -/
theorem IsRepresentation.det_latticeGramMatrix (hx : X.IsRepresentation x)
    (b : Basis ι ℤ (span ℤ (Set.range x))) :
    (hx.latticeGramMatrix b).det = (X.latticeDet : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_det, hx.latticeGramMatrix_cast, Int.cast_natCast,
    hx.latticeDet_eq_det_gram b]

-- Lemmas 2.2 and 2.3 [Exc]
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the columns are the coordinates of the representing vectors in an integral lattice basis. -/
noncomputable def latticeCoordinates (b : Basis ι ℤ (span ℤ (Set.range x))) : Matrix ι V ℤ :=
  b.toMatrix (fun u ↦ ⟨x u, subset_span (Set.mem_range_self u)⟩)

-- Lemmas 2.2 and 2.3 [Exc]
omit [Fintype V] [DecidableEq V] [DecidableEq ι] [InnerProductSpace ℝ E] in
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the coordinate matrix reconstructs each representing vector. -/
theorem sum_latticeCoordinates_smul (b : Basis ι ℤ (span ℤ (Set.range x))) (u : V) :
    ∑ i, latticeCoordinates b i u • (b i : E) = x u := by
  have hh := congrArg (span ℤ (Set.range x)).subtype
    (b.sum_toMatrix_smul_self (fun u ↦ ⟨x u, subset_span (Set.mem_range_self u)⟩) u)
  simpa only [map_sum, map_smul, Submodule.subtype_apply, latticeCoordinates] using hh

-- Lemmas 2.2 and 2.3 [Exc]
omit [Fintype ι] [DecidableEq V] [DecidableEq ι] [InnerProductSpace ℝ E] in
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the coordinate columns generate the whole coordinate lattice. -/
theorem latticeCoordinates_surjective [Finite ι] (b : Basis ι ℤ (span ℤ (Set.range x))) :
    Function.Surjective (latticeCoordinates b).mulVecLin := by
  let x' : V → span ℤ (Set.range x) := fun u ↦ ⟨x u, subset_span (Set.mem_range_self u)⟩
  have hf : Function.Surjective (Fintype.linearCombination ℤ x') := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact (span_range_subtype_eq_top_iff _ _).mpr rfl
  have he : (latticeCoordinates b).mulVecLin =
      b.equivFun.toLinearMap.comp (Fintype.linearCombination ℤ x') := by
    apply LinearMap.ext
    intro z
    ext i
    change (∑ j, b.repr (x' j) i * z j) = (b.equivFun (∑ j, z j • x' j)) i
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Basis.equivFun_apply, mul_comm]
  rw [he]
  exact b.equivFun.surjective.comp hf

-- Lemmas 2.2 and 2.3 [Exc]
omit [Fintype V] [DecidableEq ι] in
/-- Lemmas `lem:snf` (Lemma 2.3) and `lem:basisdet` (Lemma 2.4) of [Exc]:
the integral factorization `M = Uᵀ F U`. -/
theorem IsRepresentation.integralGramMatrix_eq_coordinates (hx : X.IsRepresentation x)
    (b : Basis ι ℤ (span ℤ (Set.range x))) :
    X.integralGramMatrix =
      (latticeCoordinates b)ᵀ * hx.latticeGramMatrix b * latticeCoordinates b := by
  apply Matrix.map_injective (Int.cast_injective (α := ℝ))
  change X.integralGramMatrix.map (Int.castRingHom ℝ) =
    ((latticeCoordinates b)ᵀ * hx.latticeGramMatrix b * latticeCoordinates b).map
      (Int.castRingHom ℝ)
  rw [Matrix.map_mul, Matrix.map_mul]
  change X.integralGramMatrix.map (Int.cast : ℤ → ℝ) =
    (latticeCoordinates b |>.map (Int.cast : ℤ → ℝ))ᵀ *
      (hx.latticeGramMatrix b).map (Int.cast : ℤ → ℝ) *
        (latticeCoordinates b).map (Int.cast : ℤ → ℝ)
  rw [X.integralGramMatrix_cast, hx.latticeGramMatrix_cast]
  rw [← hx, ← Matrix.gram_sum_int_smul]
  simp only [sum_latticeCoordinates_smul]

end SimpleGraph
