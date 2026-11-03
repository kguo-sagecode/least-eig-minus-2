/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.TraceRank
import LineGraphs.Spectral.Positivity

/-!
# Rectangular products

Theorem 6.1 of the spectral toolkit. Mathlib supplies the rectangular
characteristic-polynomial identity; this file extracts multiplicities and the
eigenspace equivalence and specializes to the two Gram products.
-/

open Polynomial Module.End

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A positive semidefinite spectrum consists of its positive entries and its zero modes. -/
theorem PosSemidef.spectrumMultiset_eq_filter_pos_add_replicate_zero
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.spectrumMultiset = A.spectrumMultiset.filter (0 < ·) +
      Multiset.replicate (A.eigenvalueMultiplicity 0) 0 := by
  -- Step `mn-zeros`: separate the zero and positive members of the spectral multiset.
  have hnonneg := hA.isHermitian.posSemidef_iff_spectrumMultiset_nonneg.mp hA
  apply Multiset.ext.mpr
  intro μ
  by_cases hμ : μ = 0
  · subst μ
    simp only [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate,
      lt_self_iff_false, ite_false, ite_true, zero_add]
    rfl
  · by_cases hpos : 0 < μ
    · simp only [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate,
        hpos, Ne.symm hμ, ite_true, ite_false, add_zero]
    · have hnot : μ ∉ A.spectrumMultiset := fun h => hpos
        (lt_of_le_of_ne (hnonneg μ h) (Ne.symm hμ))
      simp only [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate,
        hpos, Ne.symm hμ, ite_false, zero_add, Multiset.count_eq_zero.mpr hnot]

/-- The root-multiset form of the rectangular characteristic-polynomial identity. -/
theorem spectrumMultiset_mul_comm_add_zeros (M : Matrix m n ℝ) (N : Matrix n m ℝ) :
    Multiset.replicate (Fintype.card n) 0 + (M * N).spectrumMultiset =
      Multiset.replicate (Fintype.card m) 0 + (N * M).spectrumMultiset := by
  -- Step `mn-polynomial`: Mathlib's rectangular characteristic-polynomial identity.
  have hp := charpoly_mul_comm' M N
  -- Steps `mn-nonzero-polys`, `mn-addmult`: roots of a nonzero product form a multiset sum.
  have hroots := congrArg Polynomial.roots hp
  rw [roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (charpoly_monic _).ne_zero),
    roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (charpoly_monic _).ne_zero),
    roots_X_pow, roots_X_pow] at hroots
  -- Step `mn-powerroots`: the power of X contributes only zero roots.
  simpa only [Multiset.nsmul_singleton, spectrumMultiset] using hroots

/-- Theorem 6.1 of the spectral toolkit: nonzero algebraic multiplicities agree for rectangular
products. -/
theorem eigenvalueMultiplicity_mul_comm_of_ne_zero (M : Matrix m n ℝ)
    (N : Matrix n m ℝ) {μ : ℝ} (hμ : μ ≠ 0) :
    (M * N).eigenvalueMultiplicity μ = (N * M).eigenvalueMultiplicity μ := by
  -- Step `mn-bothcounts`: count a nonzero root in the two augmented multisets.
  have hc := congrArg (Multiset.count μ) (spectrumMultiset_mul_comm_add_zeros M N)
  simpa only [Multiset.count_add, Multiset.count_replicate, hμ.symm, ite_false, zero_add,
    spectrumMultiset, eigenvalueMultiplicity] using hc

/-- Theorem 6.1 of the spectral toolkit: the excess zero multiplicities record the difference of
the orders. -/
theorem card_add_eigenvalueMultiplicity_zero_mul_comm (M : Matrix m n ℝ)
    (N : Matrix n m ℝ) :
    Fintype.card n + (M * N).eigenvalueMultiplicity 0 =
      Fintype.card m + (N * M).eigenvalueMultiplicity 0 := by
  -- Step `mn-bothcounts`: count zero instead.
  have hc := congrArg (Multiset.count (0 : ℝ)) (spectrumMultiset_mul_comm_add_zeros M N)
  simpa only [Multiset.count_add, Multiset.count_replicate, ite_true,
    spectrumMultiset, eigenvalueMultiplicity] using hc

/-- Theorem 6.1 of the spectral toolkit, step `mn-equiv`: multiplication by N identifies the nonzero
μ-eigenspaces of MN and NM, with inverse μ⁻¹M. -/
noncomputable def eigenspaceMulEquivOfNeZero (M : Matrix m n ℝ) (N : Matrix n m ℝ)
    (μ : ℝ) (hμ : μ ≠ 0) :
    eigenspace (M * N).toLin' μ ≃ₗ[ℝ] eigenspace (N * M).toLin' μ := by
  -- Step `mn-forward`: N intertwines the two products.
  have hf (x : eigenspace (M * N).toLin' μ) :
      N *ᵥ (x : m → ℝ) ∈ eigenspace (N * M).toLin' μ := by
    have hx : (M * N) *ᵥ (x : m → ℝ) = μ • (x : m → ℝ) :=
      mem_eigenspace_iff.mp x.property
    apply mem_eigenspace_iff.mpr
    change (N * M) *ᵥ (N *ᵥ (x : m → ℝ)) = _
    rw [mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, hx, mulVec_smul]
  -- Step `mn-backward`: μ⁻¹M intertwines in the other direction.
  have hg (y : eigenspace (N * M).toLin' μ) :
      μ⁻¹ • (M *ᵥ (y : n → ℝ)) ∈ eigenspace (M * N).toLin' μ := by
    have hy : (N * M) *ᵥ (y : n → ℝ) = μ • (y : n → ℝ) :=
      mem_eigenspace_iff.mp y.property
    apply mem_eigenspace_iff.mpr
    change (M * N) *ᵥ (μ⁻¹ • (M *ᵥ (y : n → ℝ))) = _
    rw [mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, hy,
      mulVec_smul, smul_comm μ⁻¹ μ]
  refine
    { toFun := fun x => ⟨N *ᵥ (x : m → ℝ), hf x⟩
      invFun := fun y => ⟨μ⁻¹ • (M *ᵥ (y : n → ℝ)), hg y⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply Subtype.ext
    exact mulVec_add N x y
  · intro a x
    apply Subtype.ext
    exact mulVec_smul N a x
  · intro x
    -- Step `mn-leftinv`: cancel μ in the MN eigenvector equation.
    have hx : (M * N) *ᵥ (x : m → ℝ) = μ • (x : m → ℝ) :=
      mem_eigenspace_iff.mp x.property
    apply Subtype.ext
    change μ⁻¹ • (M *ᵥ (N *ᵥ (x : m → ℝ))) = _
    rw [mulVec_mulVec, hx, inv_smul_smul₀ hμ]
  · intro y
    -- Step `mn-rightinv`: cancel μ in the NM eigenvector equation.
    have hy : (N * M) *ᵥ (y : n → ℝ) = μ • (y : n → ℝ) :=
      mem_eigenspace_iff.mp y.property
    apply Subtype.ext
    change N *ᵥ (μ⁻¹ • (M *ᵥ (y : n → ℝ))) = _
    rw [mulVec_smul, mulVec_mulVec, hy, inv_smul_smul₀ hμ]

/-- Theorem 6.1 of the spectral toolkit: the two Gram products are positive semidefinite, have equal
positive spectra with multiplicities, and have the stated zero multiplicities. -/
theorem spectrumMultiset_gram_products (B : Matrix m n ℝ) :
    (B * Bᵀ).PosSemidef ∧ (Bᵀ * B).PosSemidef ∧
      (B * Bᵀ).spectrumMultiset.filter (0 < ·) =
        (Bᵀ * B).spectrumMultiset.filter (0 < ·) ∧
      (B * Bᵀ).eigenvalueMultiplicity 0 = Fintype.card m - B.rank ∧
      (Bᵀ * B).eigenvalueMultiplicity 0 = Fintype.card n - B.rank := by
  -- Step `mn-grampos`: positivity and equality of ranks for the two Gram products.
  have hleft : (B * Bᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose B
  have hright : (Bᵀ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self B
  -- Step `mn-positives`: remove the zero roots from the augmented multiset identity.
  have hs : (B * Bᵀ).spectrumMultiset.filter (0 < ·) =
      (Bᵀ * B).spectrumMultiset.filter (0 < ·) := by
    apply Multiset.ext.mpr
    intro μ
    by_cases hμ : 0 < μ
    · simpa only [Multiset.count_filter, hμ, ite_true, spectrumMultiset,
        eigenvalueMultiplicity] using eigenvalueMultiplicity_mul_comm_of_ne_zero B Bᵀ hμ.ne'
    · simp only [Multiset.count_filter, hμ, ite_false]
  -- Step `mn-zeros`: subtract the common rank from each order.
  have hl := hleft.isHermitian.rank_add_eigenvalueMultiplicity_zero
  have hr := hright.isHermitian.rank_add_eigenvalueMultiplicity_zero
  rw [rank_self_mul_transpose] at hl
  rw [rank_transpose_mul_self] at hr
  exact ⟨hleft, hright, hs, by omega, by omega⟩

end Matrix
