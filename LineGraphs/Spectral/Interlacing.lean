/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Rayleigh
import Mathlib.Order.Interval.Finset.Fin

/-!
# Rayleigh subspaces and Cauchy interlacing

Lemma 4.2 and Theorem 4.3 of the spectral toolkit. The proof uses the sorted
orthonormal eigenbasis, dimension of intersections, and extension by zero.
-/

open Matrix Module

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
  (hA : A.IsHermitian)

/-- The span of a specified finite set of sorted eigendirections. -/
noncomputable def eigenvectorSpan (s : Finset (Fin (Fintype.card n))) :
    Submodule ℝ (EuclideanSpace ℝ n) :=
  Submodule.span ℝ (Set.range fun j : s => hA.sortedEigenvectorBasis j)

/-- The sorted eigenvectors are independent, so a selected span has the expected dimension. -/
theorem finrank_eigenvectorSpan (s : Finset (Fin (Fintype.card n))) :
    finrank ℝ (hA.eigenvectorSpan s) = s.card := by
  -- Steps `witness-head`, `witness-tail`: count the independent selected basis vectors.
  have hind : LinearIndependent ℝ (fun j : s => hA.sortedEigenvectorBasis j) :=
    hA.sortedEigenvectorBasis.orthonormal.linearIndependent.comp
      (fun j : s => (j : Fin (Fintype.card n))) Subtype.val_injective
  exact (finrank_span_eq_card hind).trans (Fintype.card_coe s)

private theorem repr_eq_zero_of_mem_eigenvectorSpan
    {s : Finset (Fin (Fintype.card n))} {x : EuclideanSpace ℝ n}
    (hx : x ∈ hA.eigenvectorSpan s) {j : Fin (Fintype.card n)} (hj : j ∉ s) :
    hA.sortedEigenvectorBasis.repr x j = 0 := by
  have hspan : x ∈ Submodule.span ℝ (hA.sortedEigenvectorBasis.toBasis '' (s : Set _)) := by
    apply Submodule.span_mono (s := Set.range fun j : s => hA.sortedEigenvectorBasis j) ?_ hx
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    exact ⟨j, hj, rfl⟩
  have hs := hA.sortedEigenvectorBasis.toBasis.mem_span_image.mp hspan
  rw [← OrthonormalBasis.coe_toBasis_repr_apply]
  by_contra h
  exact hj (hs (Finsupp.mem_support_iff.mpr h))

/-- Lemma 4.2 of the spectral toolkit, steps `witness-head` and `witness-tail`: the head and tail
have
dimensions `i+1` and `n-i`, and their quadratic forms lie on the corresponding
sides of the ith eigenvalue. The inequalities include the zero vector. -/
theorem rayleigh_head_tail (i : Fin (Fintype.card n)) :
    finrank ℝ (hA.eigenvectorSpan (Finset.Iic i)) = i.val + 1 ∧
    finrank ℝ (hA.eigenvectorSpan (Finset.Ici i)) = Fintype.card n - i.val ∧
    (∀ x ∈ hA.eigenvectorSpan (Finset.Iic i),
      hA.eigenvalues₀ i * (x.ofLp ⬝ᵥ x.ofLp) ≤ x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)) ∧
    (∀ x ∈ hA.eigenvectorSpan (Finset.Ici i),
      x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) ≤ hA.eigenvalues₀ i * (x.ofLp ⬝ᵥ x.ofLp)) := by
  -- Steps `witness-head`, `witness-tail`: dimensions follow from independence.
  have hdhead : finrank ℝ (hA.eigenvectorSpan (Finset.Iic i)) = i.val + 1 := by
    rw [hA.finrank_eigenvectorSpan, Fin.card_Iic]
  have hdtail : finrank ℝ (hA.eigenvectorSpan (Finset.Ici i)) = Fintype.card n - i.val := by
    rw [hA.finrank_eigenvectorSpan, Fin.card_Ici]
  -- Step `witness-head`: only coordinates j ≤ i contribute to the weighted average.
  have hhead (x : EuclideanSpace ℝ n) (hx : x ∈ hA.eigenvectorSpan (Finset.Iic i)) :
      hA.eigenvalues₀ i * (x.ofLp ⬝ᵥ x.ofLp) ≤ x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
    rw [dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis hA.sortedEigenvectorBasis
      hA.eigenvalues₀ hA.mulVec_sortedEigenvectorBasis,
      dotProduct_self_eq_sum_of_orthonormal_basis hA.sortedEigenvectorBasis, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hj) (sq_nonneg _)
    · have hz := hA.repr_eq_zero_of_mem_eigenvectorSpan hx (by simpa using hj)
      simp only [WithLp.toLp_ofLp, hz, zero_pow two_ne_zero, mul_zero, le_refl]
  -- Step `witness-tail`: only coordinates j ≥ i contribute.
  have htail (x : EuclideanSpace ℝ n) (hx : x ∈ hA.eigenvectorSpan (Finset.Ici i)) :
      x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) ≤ hA.eigenvalues₀ i * (x.ofLp ⬝ᵥ x.ofLp) := by
    rw [dotProduct_mulVec_eq_sum_of_orthonormal_eigenbasis hA.sortedEigenvectorBasis
      hA.eigenvalues₀ hA.mulVec_sortedEigenvectorBasis,
      dotProduct_self_eq_sum_of_orthonormal_basis hA.sortedEigenvectorBasis, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hj) (sq_nonneg _)
    · have hz := hA.repr_eq_zero_of_mem_eigenvectorSpan hx (by simpa using hj)
      simp only [WithLp.toLp_ofLp, hz, zero_pow two_ne_zero, mul_zero, le_refl]
  exact ⟨hdhead, hdtail, hhead, htail⟩

omit [DecidableEq n] in
private theorem exists_ne_zero_mem_inf_of_finrank
    (P Q : Submodule ℝ (EuclideanSpace ℝ n))
    (h : Fintype.card n < finrank ℝ P + finrank ℝ Q) :
    ∃ x : EuclideanSpace ℝ n, x ∈ P ∧ x ∈ Q ∧ x ≠ 0 := by
  -- Step `witness-dimensioneq`: dimension formula for the sum and intersection.
  have heq := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hle : finrank ℝ ↥(P ⊔ Q) ≤ Fintype.card n := by
    simpa using Submodule.finrank_le (P ⊔ Q)
  -- Step `witness-intersectionpos`: the intersection has positive dimension.
  have hpos : 0 < finrank ℝ ↥(P ⊓ Q) := by omega
  -- Step `witness-witness`: a positive-dimensional subspace contains a nonzero vector.
  have hne : P ⊓ Q ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact (Nat.lt_irrefl 0) hpos
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨x, hx.1, hx.2, hx0⟩

/-- Lemma 4.2 of the spectral toolkit, step `witness-low-witness`: every subspace of dimension at
least
`i+1` meets the spectral tail in a nonzero vector. -/
theorem exists_rayleigh_le_of_finrank (i : Fin (Fintype.card n))
    (P : Submodule ℝ (EuclideanSpace ℝ n)) (hP : i.val + 1 ≤ finrank ℝ P) :
    ∃ x ∈ P, x ≠ 0 ∧ x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) ≤
      hA.eigenvalues₀ i * (x.ofLp ⬝ᵥ x.ofLp) := by
  have ht := hA.rayleigh_head_tail i
  have hdim : Fintype.card n < finrank ℝ P +
      finrank ℝ (hA.eigenvectorSpan (Finset.Ici i)) := by rw [ht.2.1]; omega
  obtain ⟨x, hx, hxt, hx0⟩ := exists_ne_zero_mem_inf_of_finrank P _ hdim
  exact ⟨x, hx, hx0, ht.2.2.2 x hxt⟩

/-- Lemma 4.2 of the spectral toolkit, step `witness-high-witness`: every subspace of dimension at
least
`n-i` meets the spectral head in a nonzero vector. -/
theorem exists_le_rayleigh_of_finrank (i : Fin (Fintype.card n))
    (P : Submodule ℝ (EuclideanSpace ℝ n))
    (hP : Fintype.card n - i.val ≤ finrank ℝ P) :
    ∃ x ∈ P, x ≠ 0 ∧ hA.eigenvalues₀ i * (x.ofLp ⬝ᵥ x.ofLp) ≤
      x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
  have ht := hA.rayleigh_head_tail i
  have hdim : Fintype.card n < finrank ℝ P +
      finrank ℝ (hA.eigenvectorSpan (Finset.Iic i)) := by rw [ht.1]; omega
  obtain ⟨x, hx, hxh, hx0⟩ := exists_ne_zero_mem_inf_of_finrank P _ hdim
  exact ⟨x, hx, hx0, ht.2.2.1 x hxh⟩

omit [DecidableEq n] in
/-- Extension by zero along an injection preserves the squared norm and the
quadratic form of a principal submatrix, and has the stated coordinate values. -/
theorem _root_.Matrix.exists_principal_submatrix_extension {m : Type*} [Fintype m]
    (f : m ↪ n) (A : Matrix n n ℝ) :
    ∃ E : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ n,
      Function.Injective E ∧
      (∀ x, (E x).ofLp ⬝ᵥ (E x).ofLp = x.ofLp ⬝ᵥ x.ofLp) ∧
      (∀ x, (E x).ofLp ⬝ᵥ (A *ᵥ (E x).ofLp) =
        x.ofLp ⬝ᵥ (A.submatrix f f *ᵥ x.ofLp)) ∧
      (∀ x u, (E x).ofLp (f u) = x.ofLp u) ∧
      (∀ x v, (∀ u, f u ≠ v) → (E x).ofLp v = 0) := by
  classical
  let Z : Matrix n m ℝ := (1 : Matrix n n ℝ).submatrix id f
  -- Step `int-inj`: restriction is a left inverse of extension by zero.
  have hgram : Zᵀ * Z = 1 := by
    ext i j
    simp [Z, mul_apply, one_apply, f.injective.eq_iff]
  have hleft (x : m → ℝ) : Zᵀ *ᵥ (Z *ᵥ x) = x := by
    rw [mulVec_mulVec, hgram, one_mulVec]
  have hinj : Function.Injective Z.toEuclideanLin := by
    intro x y hxy
    apply WithLp.ofLp_injective 2
    have hh := congrArg (fun z : EuclideanSpace ℝ n => Zᵀ *ᵥ z.ofLp) hxy
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, hleft] using hh
  -- Step `int-norm`: the embedding preserves the sum of coordinate squares.
  have hnorm (x : EuclideanSpace ℝ m) :
      (Z.toEuclideanLin x).ofLp ⬝ᵥ (Z.toEuclideanLin x).ofLp = x.ofLp ⬝ᵥ x.ofLp := by
    change (Z *ᵥ x.ofLp) ⬝ᵥ (Z *ᵥ x.ofLp) = _
    rw [← dotProduct_transpose_mulVec Z x.ofLp (Z *ᵥ x.ofLp), hleft]
  -- Step `int-form`: compression by the coordinate embedding is the principal submatrix.
  have hcompress : Zᵀ * A * Z = A.submatrix f f := by
    ext i j
    simp [Z, mul_apply, one_apply]
  have hform (x : EuclideanSpace ℝ m) :
      (Z.toEuclideanLin x).ofLp ⬝ᵥ (A *ᵥ (Z.toEuclideanLin x).ofLp) =
        x.ofLp ⬝ᵥ (A.submatrix f f *ᵥ x.ofLp) := by
    change (Z *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ (Z *ᵥ x.ofLp)) = _
    rw [dotProduct_comm, ← dotProduct_transpose_mulVec, mulVec_mulVec,
      mulVec_mulVec, hcompress]
  have hvalue (x : EuclideanSpace ℝ m) (u : m) :
      (Z.toEuclideanLin x).ofLp (f u) = x.ofLp u := by
    simp [toLpLin_apply, Z, mulVec, dotProduct, one_apply, f.injective.eq_iff]
  have hout (x : EuclideanSpace ℝ m) (v : n) (hv : ∀ u, f u ≠ v) :
      (Z.toEuclideanLin x).ofLp v = 0 := by
    change ∑ u, Z v u * x.ofLp u = 0
    apply Finset.sum_eq_zero
    intro u _
    simp [Z, (hv u).symm]
  exact ⟨Z.toEuclideanLin, hinj, hnorm, hform, hvalue, hout⟩

/-- Theorem 4.3 of the spectral toolkit, the upper Cauchy interlacing inequality, in decreasing
order. -/
theorem eigenvalues_principal_submatrix_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : m ↪ n) (i : Fin (Fintype.card m)) :
    (hA.submatrix f).eigenvalues₀ i ≤
      hA.eigenvalues₀ ⟨i.val, lt_of_lt_of_le i.isLt
        (Fintype.card_le_of_injective f f.injective)⟩ := by
  -- Step `int-symmetric`: a principal submatrix is symmetric.
  have hB := hA.submatrix f
  -- Step `int-extension`: extend by zero, preserving norm and form.
  obtain ⟨E, hinj, hnorm, hform, _, _⟩ := Matrix.exists_principal_submatrix_extension f A
  let P := hB.eigenvectorSpan (Finset.Iic i)
  -- Step `int-Bhead`: the extended head has dimension i+1.
  have hdim : finrank ℝ (P.map E) = i.val + 1 := by
    rw [← (Submodule.equivMapOfInjective E hinj P).finrank_eq]
    exact (hB.rayleigh_head_tail i).1
  let j : Fin (Fintype.card n) :=
    ⟨i.val, lt_of_lt_of_le i.isLt (Fintype.card_le_of_injective f f.injective)⟩
  -- Step `int-compareupper`: the subspace witness lies below the ith eigenvalue of A.
  obtain ⟨y, hy, hy0, hupper⟩ := hA.exists_rayleigh_le_of_finrank j (P.map E) (by dsimp [j]; omega)
  obtain ⟨x, hx, rfl⟩ := hy
  have hlower := (hB.rayleigh_head_tail i).2.2.1 x hx
  rw [hform, hnorm] at hupper
  have hx0 : x.ofLp ≠ 0 := by
    intro hx0
    apply hy0
    have hx' : x = 0 := WithLp.ofLp_injective 2 hx0
    rw [hx', map_zero]
  have hpos : 0 < x.ofLp ⬝ᵥ x.ofLp := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx0
  exact (mul_le_mul_iff_left₀ hpos).mp (hlower.trans hupper)

/-- Theorem 4.3 of the spectral toolkit, the lower Cauchy interlacing inequality, in decreasing
order. -/
theorem le_eigenvalues_principal_submatrix {m : Type*} [Fintype m] [DecidableEq m]
    (f : m ↪ n) (i : Fin (Fintype.card m)) :
    hA.eigenvalues₀ ⟨i.val + (Fintype.card n - Fintype.card m), by
      have := Fintype.card_le_of_injective f f.injective
      omega⟩ ≤ (hA.submatrix f).eigenvalues₀ i := by
  -- Steps `int-symmetric`, `int-extension`.
  have hB := hA.submatrix f
  obtain ⟨E, hinj, hnorm, hform, _, _⟩ := Matrix.exists_principal_submatrix_extension f A
  let P := hB.eigenvectorSpan (Finset.Ici i)
  -- Step `int-Btail`: the extended tail has dimension m-i.
  have hdim : finrank ℝ (P.map E) = Fintype.card m - i.val := by
    rw [← (Submodule.equivMapOfInjective E hinj P).finrank_eq]
    exact (hB.rayleigh_head_tail i).2.1
  have hmn := Fintype.card_le_of_injective f f.injective
  let j : Fin (Fintype.card n) := ⟨i.val + (Fintype.card n - Fintype.card m), by omega⟩
  -- Step `int-comparedown`: use the head of A at index i+n-m.
  obtain ⟨y, hy, hy0, hlower⟩ := hA.exists_le_rayleigh_of_finrank j (P.map E) (by
    dsimp [j]; omega)
  obtain ⟨x, hx, rfl⟩ := hy
  have hupper := (hB.rayleigh_head_tail i).2.2.2 x hx
  rw [hform, hnorm] at hlower
  have hx0 : x.ofLp ≠ 0 := by
    intro hx0
    apply hy0
    have hx' : x = 0 := WithLp.ofLp_injective 2 hx0
    rw [hx', map_zero]
  have hpos : 0 < x.ofLp ⬝ᵥ x.ofLp := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx0
  exact (mul_le_mul_iff_left₀ hpos).mp (hlower.trans hupper)

/-- Theorem 4.3 of the spectral toolkit, step `int-ends`: a nonempty principal submatrix has no
larger
largest eigenvalue. -/
theorem largestEigenvalue_principal_submatrix_le [Nonempty n]
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m] (f : m ↪ n) :
    (hA.submatrix f).largestEigenvalue ≤ hA.largestEigenvalue :=
  hA.eigenvalues_principal_submatrix_le f ⟨0, Fintype.card_pos⟩

/-- Theorem 4.3 of the spectral toolkit, step `int-ends`: a nonempty principal submatrix has no
smaller
least eigenvalue. -/
theorem leastEigenvalue_le_principal_submatrix [Nonempty n]
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m] (f : m ↪ n) :
    hA.leastEigenvalue ≤ (hA.submatrix f).leastEigenvalue := by
  have h := hA.le_eigenvalues_principal_submatrix f (lastIndex m)
  have hi : (lastIndex m).val + (Fintype.card n - Fintype.card m) = (lastIndex n).val := by
    have hmn := Fintype.card_le_of_injective f f.injective
    have hm := Fintype.card_pos (α := m)
    dsimp [lastIndex]
    omega
  simpa only [leastEigenvalue, hi] using h

end Matrix.IsHermitian
