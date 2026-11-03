/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Interlacing
import LineGraphs.Spectral.TraceRank
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gram representations with rank control

The matrix assertions of Theorem 3.5 of the spectral toolkit. The factor has
exactly rank-many rows; the family form works even in an infinite-dimensional
ambient inner product space, since the given family is finite.
-/

open Module
open scoped InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Theorem 3.5 of the spectral toolkit: Gram rank equals the dimension of the span of the vector
family. -/
theorem rank_gram_eq_finrank_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : n → E) : (gram ℝ v).rank = finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  classical
  let F : (n → ℝ) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, x i • v i
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.smul_sum, smul_smul] }
  -- Step `gram-family`: the coefficient map has image exactly the vector span.
  have hrange : F.range = Submodule.span ℝ (Set.range v) := by
    ext x
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).symm
  -- Steps `gram-square`, `gram-kerforward`, `gram-kerback`: the two maps have the same kernel.
  have hker : (gram ℝ v).toLin'.ker = F.ker := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, toLin'_apply,
      ← (posSemidef_gram ℝ v).dotProduct_mulVec_zero_iff,
      star_dotProduct_gram_mulVec, inner_self_eq_zero]
    rfl
  -- Step `gram-familyrank`: compare the two rank-nullity formulas.
  have hG := LinearMap.finrank_range_add_finrank_ker (gram ℝ v).toLin'
  have hF := LinearMap.finrank_range_add_finrank_ker F
  have hrank : (gram ℝ v).rank = finrank ℝ (gram ℝ v).toLin'.range :=
    (gram ℝ v).rank_eq_finrank_range_toLin (Pi.basisFun ℝ n) (Pi.basisFun ℝ n)
  rw [hker, ← hrank] at hG
  rw [hrange] at hF
  omega

omit [DecidableEq n] in
/-- Theorem 3.5 of the spectral toolkit: a positive semidefinite matrix has a Gram factor with
exactly
rank-many rows, whose columns span the whole coordinate space. -/
theorem IsHermitian.exists_gram_rank {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hpos : A.PosSemidef) :
    ∃ B : Matrix (Fin A.rank) n ℝ, Bᵀ * B = A ∧
      Submodule.span ℝ (Set.range B.col) = ⊤ := by
  classical
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let D : Matrix n n ℝ := diagonal fun i => Real.sqrt (hA.eigenvalues i)
  let F : Matrix n n ℝ := D * Uᴴ
  -- Steps `gram-eigenbasis`, `gram-positive`: take square roots of nonnegative eigenvalues.
  have hnonneg : ∀ i, 0 ≤ hA.eigenvalues i := hpos.eigenvalues_nonneg
  have hD : Dᴴ * D = diagonal hA.eigenvalues := by
    rw [show Dᴴ = D by simp [D], diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hnonneg i)
  -- Step `gram-construct`: the full square-root factor gives A.
  have hF : Fᵀ * F = A := by
    rw [← conjTranspose_eq_transpose_of_trivial F]
    simp only [F, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Dᴴ D Uᴴ, hD]
    simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq, Matrix.mul_assoc, star_eq_conjTranspose] using hA.spectral_theorem.symm
  let P := {i : n // hA.eigenvalues i ≠ 0}
  have hcard : Fintype.card P = A.rank := hA.rank_eq_card_non_zero_eigs.symm
  let e : P ≃ Fin A.rank := Fintype.equivFinOfCardEq hcard
  let B : Matrix (Fin A.rank) n ℝ := F.submatrix (fun i => (e.symm i).val) id
  -- Step `gram-construct`: remove precisely the zero rows and reindex the remaining rows.
  have hB : Bᵀ * B = A := by
    apply Eq.trans (b := Fᵀ * F) ?_ hF
    ext u v
    change (∑ i : Fin A.rank, F (e.symm i) u * F (e.symm i) v) = ∑ i, F i u * F i v
    rw [e.symm.sum_comp (fun i : P => F i u * F i v)]
    symm
    apply Finset.sum_congr_set {i | hA.eigenvalues i ≠ 0}
      (fun i => F i u * F i v) (fun i => F i u * F i v)
    · intro i _; rfl
    · intro i hi
      have hz : hA.eigenvalues i = 0 := by simpa using hi
      simp [F, D, diagonal_mul, hz]
  -- Steps `gram-rows`, `gram-span`: full row rank implies that the columns span.
  have hrank : B.rank = A.rank := (rank_transpose_mul_self B).symm.trans
    (congrArg (fun C : Matrix n n ℝ => C.rank) hB)
  have hspan : Submodule.span ℝ (Set.range B.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← B.rank_eq_finrank_span_cols, hrank, finrank_pi, Fintype.card_fin]
  exact ⟨B, hB, hspan⟩

omit [DecidableEq n] in
/-- A positive semidefinite matrix of rank at most r is the Gram matrix of vectors
in ℝʳ, including r = 0 and the empty matrix. -/
theorem PosSemidef.exists_gram_euclideanSpace {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {r : ℕ} (hr : A.rank ≤ r) :
    ∃ v : n → EuclideanSpace ℝ (Fin r), gram ℝ v = A := by
  classical
  obtain ⟨B, hB, _⟩ := hA.isHermitian.exists_gram_rank hA
  let f : Fin A.rank ↪ Fin r := ⟨Fin.castLE hr, Fin.castLE_injective hr⟩
  -- Step `gram-boundrank`: pad the rank-dimensional coordinates by zeros.
  obtain ⟨E, _, hnorm, _⟩ := exists_principal_submatrix_extension f
    (1 : Matrix (Fin r) (Fin r) ℝ)
  let L : EuclideanSpace ℝ (Fin A.rank) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) :=
    { toLinearMap := E
      norm_map' := fun x => by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
        simpa only [dotProduct, pow_two] using hnorm x }
  -- Step `gram-construct`: isometries preserve all inner products of the columns.
  have hgram : gram ℝ (fun u => L (WithLp.toLp 2 (B.col u))) = A := by
    apply Eq.trans (b := Bᵀ * B) ?_ hB
    ext u v
    rw [gram_apply, L.inner_map_map]
    simp only [EuclideanSpace.inner_toLp_toLp, star_trivial, mul_apply, transpose_apply,
      dotProduct, col_apply, mul_comm]
  exact ⟨_, hgram⟩

end Matrix
