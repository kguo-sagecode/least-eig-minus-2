/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Rank and positivity of integral graph lattices

The lattice-rank assertion preceding Lemma `lem:rootlattice` (Lemma 2.2) of [Exc],
also needed without connectedness in Lemmas `lem:basisdet` and `lem:snf`.
-/

open Module Submodule Matrix
open scoped RealInnerProductSpace

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
integral Gram entries promote integer linear independence
to real linear independence. This avoids a topological discreteness argument. -/
theorem LinearIndependent.real_of_int_gram {ι E : Type*} [Finite ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : ι → E}
    (hv : LinearIndependent ℤ v)
    (hint : ∀ i j, ⟪v i, v j⟫ ∈ Set.range (Int.cast : ℤ → ℝ)) :
    LinearIndependent ℝ v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose F₀ hF using hint
  let F : Matrix ι ι ℤ := F₀
  have he : F.map (Int.cast : ℤ → ℝ) = Matrix.gram ℝ v := by ext i j; exact hF i j
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [← he, ← Int.cast_det]
  apply Int.cast_ne_zero.mpr
  intro hd
  obtain ⟨z, hz, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hker' : Matrix.gram ℝ v *ᵥ (fun i ↦ (z i : ℝ)) = 0 := by
    rw [← he]
    ext i
    have hh := congrFun hker i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at hh ⊢
    exact_mod_cast hh
  have hsum : ∑ i, z i • v i = 0 := by
    simp only [← Int.cast_smul_eq_zsmul ℝ]
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← Matrix.star_dotProduct_gram_mulVec, hker', dotProduct_zero]
  exact hz (funext (Fintype.linearIndependent_iff.mp hv z hsum))

namespace Module.Basis

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

-- Section 2 [Exc]
omit [Fintype ι] in
/-- Section `sec:lattices` (Section 2) of [Exc]:
the real span of an integral basis is the real span of the lattice. -/
theorem span_real_eq_span_lattice (b : Basis ι ℤ L) :
    span ℝ (Set.range (fun i ↦ (b i : E))) = span ℝ (L : Set E) := by
  have hz : span ℤ (Set.range (fun i ↦ (b i : E))) = L := by
    rw [show Set.range (fun i ↦ (b i : E)) = L.subtype '' Set.range b from
      Set.range_comp L.subtype b, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      L.range_subtype]
  rw [← span_span_of_tower ℤ ℝ, hz]

end Module.Basis

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

-- Section 2 [Exc]
omit [Fintype V] in
/-- Section `sec:lattices` (Section 2) of [Exc]:
any integral basis of a representation lattice is
real-linearly independent. -/
theorem IsRepresentation.linearIndependent_lattice_basis {ι : Type*} [Finite ι]
    (hx : X.IsRepresentation x) (b : Basis ι ℤ (span ℤ (Set.range x))) :
    LinearIndependent ℝ (fun i ↦ (b i : E)) := by
  apply (b.linearIndependent.map' _ (Submodule.ker_subtype _)).real_of_int_gram
  exact fun i j ↦ hx.inner_mem_int_of_mem_span_int (b i).property (b j).property

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
the number of vectors in an integral lattice basis is the
rank of the real Gram matrix. -/
theorem IsRepresentation.card_lattice_basis {ι : Type*} [Fintype ι]
    (hx : X.IsRepresentation x) (b : Basis ι ℤ (span ℤ (Set.range x))) :
    Fintype.card ι = ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank := by
  rw [hx.rank_two_add_adjMatrix X, ← finrank_span_eq_card (hx.linearIndependent_lattice_basis b),
    b.span_real_eq_span_lattice, span_span_of_tower]

-- Section 2 [Exc]
/-- Section `sec:lattices` (Section 2) of [Exc]:
every representation lattice has positive determinant,
including the zero-rank lattice, whose determinant is one. -/
theorem IsRepresentation.latticeDet_pos (hx : X.IsRepresentation x) : 0 < X.latticeDet := by
  have hh := Matrix.posDef_gram_iff_linearIndependent.mpr
    (hx.linearIndependent_lattice_basis (spanIntBasis x))
  have hd := hh.det_pos
  rw [← hx.latticeDet_eq_det_gram (spanIntBasis x)] at hd
  exact_mod_cast hd

end SimpleGraph
