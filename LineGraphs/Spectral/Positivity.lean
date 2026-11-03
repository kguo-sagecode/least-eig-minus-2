/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Multiplicity
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positivity and shifts

Theorem 3.3 (the first two assertions) and Corollary 3.4 of the spectral toolkit
(`cgss/proofs/spectraltools/spectraltools-lamport.tex`, `thm:psd` and `cor:minus-two`). The
matrix `2I + A` is written `(2 : ℝ) • 1 + G.adjMatrix ℝ`.

The toolkit obtains the spectrum of a shift `A - bI` from its polynomial calculus (Theorem 3.1).
Here it comes from the arbitrary-eigenbasis form of Theorem 2.2 instead: Mathlib's eigenvector
basis of `A` is an eigenbasis of `c I + d A`, with eigenvalues `c + d λᵢ`.
-/

open Module

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace IsHermitian

variable {A : Matrix n n ℝ}

/-- The spectrum of `c I + d A` is `{{c + d μ : μ ∈ Spec(A)}}` (the special case of Theorem 3.1
used in step `psd-shifts`, proved by Theorem 2.2, step `mul-anybasis`). -/
theorem spectrumMultiset_smul_one_add_smul (hA : A.IsHermitian) (c d : ℝ) :
    (c • (1 : Matrix n n ℝ) + d • A).spectrumMultiset =
      A.spectrumMultiset.map fun μ => c + d * μ := by
  rw [hA.spectrumMultiset_eq_eigenvalues, Multiset.map_map]
  refine spectrumMultiset_eq_of_orthonormal_eigenbasis hA.eigenvectorBasis _ fun j => ?_
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hA.mulVec_eigenvectorBasis, smul_smul,
    ← add_smul]
  rfl

omit [Fintype n] in
/-- `c I + d A` is symmetric. -/
theorem smul_one_add_smul (hA : A.IsHermitian) (c d : ℝ) :
    (c • (1 : Matrix n n ℝ) + d • A).IsHermitian :=
  (isHermitian_one.smul (IsSelfAdjoint.all c)).add (hA.smul (IsSelfAdjoint.all d))

/-- The determinant is the product of the spectrum. -/
theorem det_eq_prod_spectrumMultiset (hA : A.IsHermitian) :
    A.det = A.spectrumMultiset.prod := by
  rw [hA.det_eq_prod_eigenvalues, hA.spectrumMultiset_eq_eigenvalues, Finset.prod_eq_multiset_prod]
  rfl

/-- Theorem 3.3 of the spectral toolkit, step `psd-nonneg`: `A ⪰ 0` iff every member of `Spec(A)`
is nonnegative. This is Mathlib's `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`, read
through Theorem 2.2. -/
theorem posSemidef_iff_spectrumMultiset_nonneg (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ μ ∈ A.spectrumMultiset, 0 ≤ μ := by
  -- Theorem 2.2: `Spec(A)` is the multiset of the `hA.eigenvalues i`.
  have hspec := hA.spectrumMultiset_eq_eigenvalues
  -- Step `psd-nonneg`: Mathlib's criterion.
  have hpsd := hA.posSemidef_iff_eigenvalues_nonneg
  rw [hpsd, hspec]
  simp [Pi.le_def]

/-- Theorem 3.3 of the spectral toolkit, step `psd-positive`: `A` is positive definite iff every
member of `Spec(A)` is positive (Mathlib's `Matrix.IsHermitian.posDef_iff_eigenvalues_pos`). -/
theorem posDef_iff_spectrumMultiset_pos (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ μ ∈ A.spectrumMultiset, 0 < μ := by
  -- Theorem 2.2: `Spec(A)` is the multiset of the `hA.eigenvalues i`.
  have hspec := hA.spectrumMultiset_eq_eigenvalues
  -- Step `psd-positive`: Mathlib's criterion.
  have hpd := hA.posDef_iff_eigenvalues_pos
  rw [hpd, hspec]
  simp

/-- Theorem 3.3 of the spectral toolkit, step `psd-shifts`: `A - bI ⪰ 0` iff `b ≤ μ` for every
`μ ∈ Spec(A)`. -/
theorem posSemidef_sub_smul_one_iff (hA : A.IsHermitian) (b : ℝ) :
    (A - b • (1 : Matrix n n ℝ)).PosSemidef ↔ ∀ μ ∈ A.spectrumMultiset, b ≤ μ := by
  -- `A - bI = (-b) I + 1 A`, with spectrum `{{μ - b}}`.
  have heq : A - b • (1 : Matrix n n ℝ) = (-b) • (1 : Matrix n n ℝ) + (1 : ℝ) • A := by
    rw [one_smul, neg_smul, neg_add_eq_sub]
  have hspec := hA.spectrumMultiset_smul_one_add_smul (-b) 1
  -- Step `psd-nonneg` for the symmetric matrix `A - bI`.
  have hpsd := (hA.smul_one_add_smul (-b) 1).posSemidef_iff_spectrumMultiset_nonneg
  rw [heq, hpsd, hspec]
  simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun μ _ => by constructor <;> intro h <;> linarith

/-- Theorem 3.3 of the spectral toolkit, step `psd-shifts`: `bI - A ⪰ 0` iff `μ ≤ b` for every
`μ ∈ Spec(A)`. -/
theorem posSemidef_smul_one_sub_iff (hA : A.IsHermitian) (b : ℝ) :
    (b • (1 : Matrix n n ℝ) - A).PosSemidef ↔ ∀ μ ∈ A.spectrumMultiset, μ ≤ b := by
  -- `bI - A = b I + (-1) A`, with spectrum `{{b - μ}}`.
  have heq : b • (1 : Matrix n n ℝ) - A = b • (1 : Matrix n n ℝ) + (-1 : ℝ) • A := by
    rw [neg_one_smul, sub_eq_add_neg]
  have hspec := hA.spectrumMultiset_smul_one_add_smul b (-1)
  -- Step `psd-nonneg` for the symmetric matrix `bI - A`.
  have hpsd := (hA.smul_one_add_smul b (-1)).posSemidef_iff_spectrumMultiset_nonneg
  rw [heq, hpsd, hspec]
  simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun μ _ => by constructor <;> intro h <;> linarith

/-- `μ ∈ Spec(A)` iff `det(A - μ I) = 0`, for a symmetric `A` (steps `minus-det`, `minus-root` of
Corollary 3.4, for an arbitrary shift). -/
theorem mem_spectrumMultiset_iff_det_eq_zero (hA : A.IsHermitian) (μ : ℝ) :
    μ ∈ A.spectrumMultiset ↔ ((-μ) • (1 : Matrix n n ℝ) + A).det = 0 := by
  -- Step `minus-det`: the determinant is the product of the shifted spectrum.
  have hdet : ((-μ) • (1 : Matrix n n ℝ) + A).det =
      (A.spectrumMultiset.map fun ν => -μ + 1 * ν).prod := by
    have h1 : (-μ) • (1 : Matrix n n ℝ) + A = (-μ) • (1 : Matrix n n ℝ) + (1 : ℝ) • A := by
      rw [one_smul]
    rw [h1, (hA.smul_one_add_smul (-μ) 1).det_eq_prod_spectrumMultiset,
      hA.spectrumMultiset_smul_one_add_smul]
  -- Step `minus-root`: a finite real product vanishes iff a factor vanishes.
  have hroot : (A.spectrumMultiset.map fun ν => -μ + 1 * ν).prod = 0 ↔ μ ∈ A.spectrumMultiset := by
    rw [Multiset.prod_eq_zero_iff, Multiset.mem_map]
    constructor
    · rintro ⟨ν, hν, h⟩
      have : ν = μ := by linarith
      exact this ▸ hν
    · intro h
      exact ⟨μ, h, by ring⟩
  rw [hdet, hroot]

variable [Nonempty n]

/-- The least-element property of Lemma 2.4: `b ≤ λmin(A)` iff `b ≤ μ` for all `μ ∈ Spec(A)`. -/
theorem le_leastEigenvalue_iff (hA : A.IsHermitian) (b : ℝ) :
    b ≤ hA.leastEigenvalue ↔ ∀ μ ∈ A.spectrumMultiset, b ≤ μ :=
  ⟨fun h _ hμ => h.trans (hA.leastEigenvalue_le_of_mem hμ),
    fun h => h _ hA.leastEigenvalue_mem_spectrumMultiset⟩

/-- The greatest-element property of Lemma 2.4: `λmax(A) ≤ b` iff `μ ≤ b` for all
`μ ∈ Spec(A)`. -/
theorem largestEigenvalue_le_iff (hA : A.IsHermitian) (b : ℝ) :
    hA.largestEigenvalue ≤ b ↔ ∀ μ ∈ A.spectrumMultiset, μ ≤ b :=
  ⟨fun h _ hμ => (hA.le_largestEigenvalue_of_mem hμ).trans h,
    fun h => h _ hA.largestEigenvalue_mem_spectrumMultiset⟩

end IsHermitian

end Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Corollary 3.4 of the spectral toolkit, step `minus-psd`: `2I + A ⪰ 0` iff every eigenvalue of
`X` is at least `-2`. -/
theorem posSemidef_two_add_adjMatrix_iff :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ).PosSemidef ↔
      ∀ μ ∈ G.spectrumMultiset, -2 ≤ μ := by
  -- Theorem 3.3 with `b = -2`.
  have h := (G.isHermitian_adjMatrix ℝ).posSemidef_sub_smul_one_iff (-2)
  rwa [sub_eq_add_neg, ← neg_smul, neg_neg, add_comm] at h

/-- Corollary 3.4 of the spectral toolkit, steps `minus-det`, `minus-root` and `minus-empty`:
`-2 ∈ Spec(X)` iff `det(2I + A) = 0`. -/
theorem neg_two_mem_spectrumMultiset_iff_det_eq_zero :
    -2 ∈ G.spectrumMultiset ↔ ((2 : ℝ) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ).det = 0 := by
  have h := (G.isHermitian_adjMatrix ℝ).mem_spectrumMultiset_iff_det_eq_zero (-2)
  rwa [neg_neg] at h

variable [Nonempty V]

/-- Corollary 3.4 of the spectral toolkit, step `minus-min`: for a graph with a vertex,
`2I + A ⪰ 0` iff `λmin(X) ≥ -2`. -/
theorem posSemidef_two_add_adjMatrix_iff_neg_two_le_leastEigenvalue :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ).PosSemidef ↔ -2 ≤ G.leastEigenvalue := by
  rw [G.posSemidef_two_add_adjMatrix_iff]
  exact ((G.isHermitian_adjMatrix ℝ).le_leastEigenvalue_iff (-2)).symm

/-- Corollary 3.4 of the spectral toolkit, step `minus-eq`: `λmin(X) = -2` iff `2I + A ⪰ 0` and
`det(2I + A) = 0`. -/
theorem leastEigenvalue_eq_neg_two_iff :
    G.leastEigenvalue = -2 ↔
      ((2 : ℝ) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ).PosSemidef ∧
        ((2 : ℝ) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ).det = 0 := by
  rw [G.posSemidef_two_add_adjMatrix_iff_neg_two_le_leastEigenvalue,
    ← G.neg_two_mem_spectrumMultiset_iff_det_eq_zero]
  constructor
  · intro h
    exact ⟨h.ge, h ▸ (G.isHermitian_adjMatrix ℝ).leastEigenvalue_mem_spectrumMultiset⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm ((G.isHermitian_adjMatrix ℝ).leastEigenvalue_le_of_mem h2) h1

/-- Corollary 3.4 of the spectral toolkit, step `minus-max`: `2I - A ⪰ 0` iff `λmax(X) ≤ 2`. -/
theorem posSemidef_two_sub_adjMatrix_iff :
    ((2 : ℝ) • (1 : Matrix V V ℝ) - G.adjMatrix ℝ).PosSemidef ↔ G.largestEigenvalue ≤ 2 := by
  rw [(G.isHermitian_adjMatrix ℝ).posSemidef_smul_one_sub_iff]
  exact ((G.isHermitian_adjMatrix ℝ).largestEigenvalue_le_iff 2).symm

end SimpleGraph
