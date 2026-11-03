/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.TraceRank
import LineGraphs.Spectral.Regular

/-!
# Separating the all-ones direction

Theorem 5.7 of the spectral toolkit, including the complement and Seidel formulas.
Erasing one copy of the row sum handles disconnected regular graphs without a simplicity
assumption on that eigenvalue.
-/

open scoped BigOperators InnerProductSpace

namespace Matrix

private theorem exists_eigenbasis_starting_with
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {v : E} (hv : ‖v‖ = 1)
    {k : ℝ} (hk : T v = k • v) :
    ∃ (d : ℕ) (u : OrthonormalBasis (Unit ⊕ Fin d) ℝ E) (μ : Fin d → ℝ),
      u (Sum.inl ()) = v ∧
      (∀ i, T (u (Sum.inr i)) = μ i • u (Sum.inr i)) ∧
      (∀ i, ⟪v, u (Sum.inr i)⟫_ℝ = 0) := by
  classical
  let Q := (ℝ ∙ v)ᗮ
  -- Step `ones-invariant`: symmetry preserves the orthogonal complement.
  have hQ : ∀ x ∈ Q, T x ∈ Q := by
    intro x hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
    rw [← hT v x, hk, real_inner_smul_left, hx, mul_zero]
  -- Step `ones-restrict`: diagonalize the symmetric restriction.
  have hS := hT.restrict_invariant hQ
  let q := hS.eigenvectorBasis rfl
  let w : Unit ⊕ Fin (Module.finrank ℝ Q) → E :=
    Sum.elim (fun _ => v) (fun i => (q i : E))
  -- Step `ones-basis`: the extra vector is orthogonal to every restricted basis vector.
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [w, hv]
      | inr j =>
        simpa [w] using
          (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (q j).property)
    | inr i =>
      cases j with
      | inl j =>
        simpa [w] using
          (Submodule.mem_orthogonal_singleton_iff_inner_left.mp (q i).property)
      | inr j => simpa [w] using orthonormal_iff_ite.mp q.orthonormal i j
  -- Step `ones-split`: a vector orthogonal to the proposed basis must vanish.
  have hspan : (Submodule.span ℝ (Set.range w))ᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have horth : ∀ i, ⟪w i, x⟫_ℝ = 0 := by
      intro i
      exact Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range_self i)) hx
    have hxQ : x ∈ Q :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (horth (Sum.inl ()))
    have hz : q.repr ⟨x, hxQ⟩ = 0 := by
      ext i
      simpa [OrthonormalBasis.repr_apply_apply, w] using horth (Sum.inr i)
    have : (⟨x, hxQ⟩ : Q) = 0 := q.repr.injective (by simpa using hz)
    simpa using congrArg Subtype.val this
  let u := OrthonormalBasis.mkOfOrthogonalEqBot hw hspan
  have hu : ⇑u = w := OrthonormalBasis.coe_of_orthogonal_eq_bot_mk hw hspan
  refine ⟨_, u, hS.eigenvalues rfl, ?_, ?_, ?_⟩
  · rw [hu]; rfl
  · intro i
    rw [hu]
    exact congrArg Subtype.val (hS.apply_eigenvectorBasis rfl i)
  · intro i
    simpa [hu, w] using
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (q i).property)

private theorem map_univ_sum_unit {d : ℕ} (k : ℝ) (μ : Fin d → ℝ) :
    Finset.univ.val.map (Sum.elim (fun _ : Unit => k) μ) =
      {k} + Finset.univ.val.map μ := by
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
  simp

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Theorem 5.7 of the spectral toolkit: one constant eigenvector is separated from the remaining
spectrum,
including when its eigenvalue has multiplicity greater than one. -/
theorem IsHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {k : ℝ}
    (hk : A *ᵥ (fun _ => 1) = k • (fun _ => 1)) (b s t : ℝ) :
    (s • A + b • 1 + t • (of fun (_ : n) (_ : n) => 1)).spectrumMultiset =
      {b + s * k + t * Fintype.card n} + (A.spectrumMultiset.erase k).map (b + s * ·) := by
  classical
  let j : EuclideanSpace ℝ n := WithLp.toLp 2 (fun _ => 1)
  have hj : j ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ n => x (Classical.arbitrary n)) h
    simp [j] at this
  let c : ℝ := ‖j‖⁻¹
  have hc : c ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hj)
  let v := c • j
  have hv : ‖v‖ = 1 := by simp [v, c, norm_smul, norm_ne_zero_iff.mpr hj]
  have hvA : A.toEuclideanLin v = k • v := by
    apply WithLp.ofLp_injective
    change A *ᵥ (c • (fun _ => 1)) = k • (c • (fun _ => 1))
    rw [mulVec_smul, hk, smul_comm]
  -- Step `ones-decompose`: extend the normalized constant eigenvector.
  have hb := exists_eigenbasis_starting_with (isSymmetric_toEuclideanLin_iff.mpr hA) hv hvA
  obtain ⟨d, u, μ, huv, huA, huorth⟩ := hb
  have hAeig (i : Unit ⊕ Fin d) :
      A *ᵥ ⇑(u i) = Sum.elim (fun _ => k) μ i • ⇑(u i) := by
    cases i with
    | inl i => cases i; rw [huv]; exact congrArg WithLp.ofLp hvA
    | inr i => exact congrArg WithLp.ofLp (huA i)
  have hAspec : A.spectrumMultiset = {k} + Finset.univ.val.map μ := by
    rw [spectrumMultiset_eq_of_orthonormal_eigenbasis u _ hAeig, map_univ_sum_unit]
  -- Step `ones-J`: multiplication by J is the constant coordinate sum.
  have hJ (x : n → ℝ) : (of fun (_ : n) (_ : n) => (1 : ℝ)) *ᵥ x =
      (∑ i, x i) • (fun _ => 1) := by
    ext i
    simp [mulVec, dotProduct]
  -- Step `ones-perp`: J kills the remaining basis vectors.
  have hJperp (i : Fin d) : (of fun (_ : n) (_ : n) => (1 : ℝ)) *ᵥ ⇑(u (Sum.inr i)) = 0 := by
    have ho := huorth i
    rw [real_inner_smul_left] at ho
    have hjorth : ⟪j, u (Sum.inr i)⟫_ℝ = 0 := (mul_eq_zero.mp ho).resolve_left hc
    have hsum : ∑ a, u (Sum.inr i) a = 0 := by
      simpa [j, PiLp.inner_apply, RCLike.inner_apply] using hjorth
    rw [hJ, hsum, zero_smul]
  -- Step `ones-constant`: J acts on the first vector by the matrix order.
  have hJv : (of fun (_ : n) (_ : n) => (1 : ℝ)) *ᵥ ⇑v = (Fintype.card n : ℝ) • ⇑v := by
    ext i
    simp [v, j, mulVec, dotProduct, mul_comm]
  let ν : Unit ⊕ Fin d → ℝ :=
    Sum.elim (fun _ => b + s * k + t * Fintype.card n) (fun i => b + s * μ i)
  have hnew (i : Unit ⊕ Fin d) :
      (s • A + b • 1 + t • (of fun (_ : n) (_ : n) => 1)) *ᵥ ⇑(u i) = ν i • ⇑(u i) := by
    rw [add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hAeig]
    cases i with
    | inl i =>
      cases i
      rw [huv, hJv]
      simp only [ν, Sum.elim_inl, smul_smul]
      rw [← add_smul, ← add_smul]
      congr 1
      ring
    | inr i =>
      rw [hJperp, smul_zero, add_zero]
      simp only [ν, Sum.elim_inr, smul_smul]
      rw [← add_smul, add_comm]
  -- Step `ones-list`: the arbitrary orthonormal eigenbasis counts multiplicities.
  have hlist := spectrumMultiset_eq_of_orthonormal_eigenbasis u ν hnew
  rw [hlist, hAspec]
  simp only [Multiset.singleton_add, Multiset.erase_cons_head]
  simpa [ν, Multiset.map_map, Function.comp_def, Multiset.singleton_add] using
    map_univ_sum_unit (b + s * k + t * Fintype.card n) (fun i => b + s * μ i)

omit [DecidableEq n] in
/-- Corollary 5.8 of the spectral toolkit: removing the positive constant eigenvalue preserves
positivity
and lowers the rank by one. -/
theorem PosSemidef.rank_sub_allOnes {G : Matrix n n ℝ} (hG : G.PosSemidef)
    {b : ℝ} (hb : 0 < b) (hk : G *ᵥ (fun _ => 1) = b • (fun _ => 1)) :
    (G - (b / Fintype.card n) • (of fun _ _ => 1)).PosSemidef ∧
      (G - (b / Fintype.card n) • (of fun _ _ => 1)).rank = G.rank - 1 := by
  classical
  let H := G - (b / Fintype.card n) • (of fun (_ : n) (_ : n) => (1 : ℝ))
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJ : (of fun (_ : n) (_ : n) => (1 : ℝ)).IsHermitian := by ext i j; rfl
  have hH : H.IsHermitian := hG.isHermitian.sub (hJ.smul (IsSelfAdjoint.all _))
  -- Step `remove-list`: the correction replaces exactly one copy of b by zero.
  have hs : H.spectrumMultiset = {0} + G.spectrumMultiset.erase b := by
    have h := hG.isHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
      hk 0 1 (-(b / Fintype.card n))
    simpa [H, sub_eq_add_neg, neg_smul, hn] using h
  -- Step `remove-positive`: all unchanged eigenvalues remain nonnegative.
  have hp : H.PosSemidef := hH.posSemidef_iff_spectrumMultiset_nonneg.mpr (by
    intro μ hμ
    rw [hs, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · exact le_rfl
    · exact hG.isHermitian.posSemidef_iff_spectrumMultiset_nonneg.mp hG μ
        (Multiset.mem_of_mem_erase hμ))
  -- Step `remove-rank`: zero multiplicity increases by one.
  have hm : H.eigenvalueMultiplicity 0 = G.eigenvalueMultiplicity 0 + 1 := by
    change H.spectrumMultiset.count 0 = G.spectrumMultiset.count 0 + 1
    rw [hs, Multiset.count_add, Multiset.count_erase_of_ne (ne_of_lt hb)]
    simp [Nat.add_comm]
  have hr := hH.rank_add_eigenvalueMultiplicity_zero
  have hg := hG.isHermitian.rank_add_eigenvalueMultiplicity_zero
  refine ⟨hp, ?_⟩
  change H.rank = G.rank - 1
  omega

/-- Corollary 5.9 of the spectral toolkit: the spectrum of a scalar matrix plus a multiple of J. -/
theorem spectrumMultiset_smul_one_add_smul_allOnes (b t : ℝ) :
    (b • (1 : Matrix n n ℝ) + t • (of fun _ _ => 1)).spectrumMultiset =
      {b + t * Fintype.card n} + Multiset.replicate (Fintype.card n - 1) b := by
  -- Step `scalar-actions`: the zero matrix has row sum zero.
  have hz : (0 : Matrix n n ℝ) *ᵥ (fun _ => 1) = (0 : ℝ) • (fun _ => 1) := by simp
  -- Step `scalar-multiset`: separate its constant direction.
  have hs := IsHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
    isHermitian_zero hz b 0 t
  simpa [spectrumMultiset, charpoly_zero, Polynomial.roots_X_pow] using hs

/-- Corollary 5.9 of the spectral toolkit: the characteristic polynomial, including coincident
values. -/
theorem charpoly_smul_one_add_smul_allOnes (b t : ℝ) :
    (b • (1 : Matrix n n ℝ) + t • (of fun _ _ => 1)).charpoly =
      (Polynomial.X - Polynomial.C (b + t * Fintype.card n)) *
        (Polynomial.X - Polynomial.C b) ^ (Fintype.card n - 1) := by
  have hJ : (of fun (_ : n) (_ : n) => (1 : ℝ)).IsHermitian := by ext i j; rfl
  have hH := hJ.smul_one_add_smul b t
  -- Step `scalar-charpoly`: reconstruct the monic split polynomial from its roots.
  have hr := hH.splits_charpoly.eq_prod_roots_of_monic
    (charpoly_monic (b • (1 : Matrix n n ℝ) + t • (of fun _ _ => 1)))
  rw [hr]
  change ((b • (1 : Matrix n n ℝ) + t • (of fun _ _ => 1)).spectrumMultiset.map
    (fun a => Polynomial.X - Polynomial.C a)).prod = _
  rw [spectrumMultiset_smul_one_add_smul_allOnes]
  simp

/-- Corollary 5.9 of the spectral toolkit: the determinant of a scalar matrix plus a multiple of
J. -/
theorem det_smul_one_add_smul_allOnes (b t : ℝ) :
    (b • (1 : Matrix n n ℝ) + t • (of fun _ _ => 1)).det =
      (b + t * Fintype.card n) * b ^ (Fintype.card n - 1) := by
  have hJ : (of fun (_ : n) (_ : n) => (1 : ℝ)).IsHermitian := by ext i j; rfl
  -- Step `scalar-det`: take the product of all eigenvalues.
  have hd := (hJ.smul_one_add_smul b t).det_eq_prod_spectrumMultiset
  rw [hd, spectrumMultiset_smul_one_add_smul_allOnes]
  simp

end Matrix

namespace SimpleGraph

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {k : ℕ}

/-- The complement spectrum of a regular graph, removing one copy of its degree. -/
theorem IsRegularOfDegree.spectrumMultiset_compl (h : X.IsRegularOfDegree k) :
    Xᶜ.spectrumMultiset =
      {(Fintype.card V : ℝ) - 1 - k} + (X.spectrumMultiset.erase k).map (-1 - ·) := by
  -- Step `ones-complement`: the complementary adjacency matrix is J - I - A.
  have hc : Xᶜ.adjMatrix ℝ = (-1 : ℝ) • X.adjMatrix ℝ + (-1 : ℝ) • 1 +
      (of fun (_ : V) (_ : V) => (1 : ℝ)) := by
    have hh := X.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    rw [X.compl_adjMatrix_eq_adjMatrix_compl ℝ] at hh
    change _ = (of fun (_ : V) (_ : V) => (1 : ℝ)) at hh
    rw [neg_one_smul, neg_one_smul]
    rw [← hh]
    abel
  have hk : X.adjMatrix ℝ *ᵥ (fun _ => 1) = (k : ℝ) • (fun _ => 1) := by
    ext v
    simpa using X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) h (a := 1) (v := v)
  -- Step `ones-substitute`: use coefficients b = -1, s = -1, t = 1.
  have hs := Matrix.IsHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
    (X.isHermitian_adjMatrix ℝ) hk (-1) (-1) 1
  rw [spectrumMultiset, hc]
  convert hs using 1 <;>
    simp [SimpleGraph.spectrumMultiset, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The Seidel spectrum of a regular graph, with multiplicities. -/
theorem IsRegularOfDegree.spectrumMultiset_seidelMatrix (h : X.IsRegularOfDegree k) :
    X.seidelMatrix.spectrumMultiset =
      {(Fintype.card V : ℝ) - 1 - 2 * k} + (X.spectrumMultiset.erase k).map (-1 - 2 * ·) := by
  -- Step `ones-Seidel`: the Seidel matrix is J - I - 2A.
  have hc : X.seidelMatrix = (-2 : ℝ) • X.adjMatrix ℝ + (-1 : ℝ) • 1 +
      (of fun (_ : V) (_ : V) => (1 : ℝ)) := by
    simp [seidelMatrix, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hk : X.adjMatrix ℝ *ᵥ (fun _ => 1) = (k : ℝ) • (fun _ => 1) := by
    ext v
    simpa using X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) h (a := 1) (v := v)
  -- Step `ones-substitute`: use coefficients b = -1, s = -2, t = 1.
  have hs := Matrix.IsHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
    (X.isHermitian_adjMatrix ℝ) hk (-1) (-2) 1
  rw [hc]
  convert hs using 1 <;>
    simp [SimpleGraph.spectrumMultiset, sub_eq_add_neg, add_comm, add_assoc]

end SimpleGraph
