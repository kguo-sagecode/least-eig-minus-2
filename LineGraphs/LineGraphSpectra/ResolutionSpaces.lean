/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.ResolutionSpectrum

/-!
# The blueprint's three nonconstant spaces

Example 5.13 (`ex:5.13`) of [CGSS], steps `s5exv1`–`s5exd3p`.
These are the spaces defined by class indicators, transposed incidence, and
the two kernels. Their identification with the explicit spectral projections
connects the dimension computation to the blueprint's geometric definitions.
-/

open Matrix
open scoped BigOperators

namespace Design.Resolution

attribute [local instance] Classical.propDecidable

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {k : ℕ} {D : Design P B (k * (2 * k - 1)) k (4 * k ^ 2 - 1) (2 * k + 1) 1}
  (R : D.Resolution (2 * k + 1))

/-- The zero-sum hyperplane used in `s5exd12`, Example 5.13 of [CGSS]. -/
def zeroSum (I : Type*) [Fintype I] : Submodule ℝ (I → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simpa [Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy
  smul_mem' := by
    intro a x hx
    change ∑ i, a * x i = 0
    rw [← Finset.mul_sum, (show ∑ i, x i = 0 from hx), mul_zero]

/-- The space `W₁` in `s5exv1`, Example 5.13 of [CGSS]. -/
noncomputable def W₁ : Submodule ℝ (B → ℝ) :=
  (zeroSum (Fin (2 * k + 1))).map R.classMatrixᵀ.toLin'

/-- The space `W₂` in `s5exv2`, Example 5.13 of [CGSS]. -/
noncomputable def W₂ : Submodule ℝ (B → ℝ) := (zeroSum P).map D.realIncMatrixᵀ.toLin'

/-- The space `W₃` in `s5exv3`, Example 5.13 of [CGSS]. -/
noncomputable def W₃ : Submodule ℝ (B → ℝ) :=
  LinearMap.ker D.realIncMatrix.toLin' ⊓ LinearMap.ker R.classMatrix.toLin'

/-- The explicit projections are the spectral projections (`s5exspecH`,
Example 5.13 of [CGSS]). -/
theorem projections_eq_spectralIdempotent (i : Fin 4) :
    R.projections i = (R.graph.isHermitian_adjMatrix ℝ).spectralIdempotent
      (Matrix.resolutionEigenvalues k i) :=
  (R.graph.isHermitian_adjMatrix ℝ).eq_spectralIdempotent_of_eigenprojections
    R.projections (Matrix.resolutionEigenvalues k)
    (Matrix.resolutionEigenvalues_injective D.one_lt_k) R.isHermitian_projections
    R.sum_projections R.mul_projections i

/-- Projection actions on the four spaces (`s5exvalues`, Example 5.13 of [CGSS]). -/
theorem projections_mulVec_of_eigenvector (i j : Fin 4) {x : B → ℝ}
    (hx : R.graph.adjMatrix ℝ *ᵥ x = Matrix.resolutionEigenvalues k j • x) :
    R.projections i *ᵥ x = if j = i then x else 0 := by
  rw [R.projections_eq_spectralIdempotent,
    (R.graph.isHermitian_adjMatrix ℝ).spectralIdempotent_mulVec_of_eigenvector _ hx]
  simp only [(Matrix.resolutionEigenvalues_injective D.one_lt_k).eq_iff]
  split_ifs <;> simp

/-- Fixed vectors of a projection lie in the indicated space (`s5exvalues`,
Example 5.13 of [CGSS]). -/
theorem eigenvector_of_projection_fixed (i : Fin 4) {x : B → ℝ}
    (hx : R.projections i *ᵥ x = x) :
    R.graph.adjMatrix ℝ *ᵥ x = Matrix.resolutionEigenvalues k i • x := by
  have he := congrArg (fun M : Matrix B B ℝ ↦ M *ᵥ x) (R.mul_projections i)
  rwa [← Matrix.mulVec_mulVec, hx, Matrix.smul_mulVec, hx] at he

/-- The coordinate sum of `Cx` (`s5exclass`, Example 5.13 of [CGSS]). -/
theorem sum_classMatrix_mulVec (x : B → ℝ) :
    ∑ i, (R.classMatrix *ᵥ x) i = ∑ a, x a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, R.sum_classMatrix, one_mul]

/-- The coordinate sum of `Nx` (`s5exd3p`, Example 5.13 of [CGSS]). -/
theorem sum_realIncMatrix_mulVec (x : B → ℝ) :
    ∑ p, (D.realIncMatrix *ᵥ x) p = (k : ℝ) * ∑ a, x a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, D.realIncMatrix_col_sum]
  rw [Finset.mul_sum]

/-- Multiplication by all ones in `s5exvalues`, Example 5.13 of [CGSS]. -/
theorem allOnes_mulVec {I J : Type*} [Fintype J] (x : J → ℝ) :
    Matrix.of (fun (_ : I) (_ : J) ↦ (1 : ℝ)) *ᵥ x = (∑ j, x j) • (fun _ ↦ 1) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- The nonprincipal spaces have zero coordinate sum (`s5exv1`–`s5exv3`,
Example 5.13 of [CGSS]). -/
theorem sum_eq_zero_of_eigenvector {i : Fin 4} (hi : i ≠ 0) {x : B → ℝ}
    (hx : R.graph.adjMatrix ℝ *ᵥ x = Matrix.resolutionEigenvalues k i • x) :
    ∑ a, x a = 0 := by
  have he := R.projections_mulVec_of_eigenvector 0 i hx
  rw [ite_eq_right hi] at he
  dsimp [projections, Matrix.resolutionProjections] at he
  simp only [← Matrix.smul_of] at he
  rw [Matrix.smul_mulVec, allOnes_mulVec] at he
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast D.one_lt_k
  have hn : 4 * (k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have : Nonempty B := Fintype.card_pos_iff.mp (by rw [D.card_blocks]; exact D.b_pos)
  have hj : (fun _ : B ↦ (1 : ℝ)) ≠ 0 := by
    intro h
    simpa using congrFun h (Classical.arbitrary B)
  exact (smul_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (inv_ne_zero hn))).resolve_right hj

/-- The coordinate sum of `Nᵀy` (`s5exv2`, Example 5.13 of [CGSS]). -/
theorem sum_transpose_realIncMatrix_mulVec (y : P → ℝ) :
    ∑ a, (D.realIncMatrixᵀ *ᵥ y) a = ((2 * k + 1 : ℕ) : ℝ) * ∑ p, y p := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, D.realIncMatrix_row_sum]
  rw [Finset.mul_sum]

/-- The class-indicator space is the `-(k-1)` eigenspace (`s5exv1`,
Example 5.13 of [CGSS]). -/
theorem W₁_eq_eigenspace :
    R.W₁ = Module.End.eigenspace (R.graph.adjMatrix ℝ).toLin'
      (Matrix.resolutionEigenvalues k 1) := by
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast D.one_lt_k
  have hq : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have hqcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := D.one_lt_k; omega), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ∑ i, a i = 0 at ha
    have hCa : R.classMatrix *ᵥ (R.classMatrixᵀ *ᵥ a) = (2 * (k : ℝ) - 1) • a := by
      rw [Matrix.mulVec_mulVec, R.classMatrix_mul_transpose, Matrix.smul_mulVec,
        Matrix.one_mulVec, hqcast]
    have hsum : ∑ b, (R.classMatrixᵀ *ᵥ a) b = 0 := by
      rw [← R.sum_classMatrix_mulVec, hCa]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ha, mul_zero]
    apply Module.End.mem_eigenspace_iff.mpr
    apply R.eigenvector_of_projection_fixed 1
    dsimp [projections, Matrix.resolutionProjections]
    simp only [← Matrix.smul_of]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, allOnes_mulVec,
      hsum, zero_smul, smul_zero, sub_zero, ← Matrix.mulVec_mulVec, hCa,
      Matrix.mulVec_smul, inv_smul_smul₀ hq]
  · intro hx
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    have hsum := R.sum_eq_zero_of_eigenvector (by decide : (1 : Fin 4) ≠ 0) hx'
    have he := R.projections_mulVec_of_eigenvector 1 1 hx'
    rw [ite_eq_left rfl] at he
    dsimp [projections, Matrix.resolutionProjections] at he
    simp only [← Matrix.smul_of] at he
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, allOnes_mulVec,
      hsum, zero_smul, smul_zero, sub_zero] at he
    refine ⟨(2 * (k : ℝ) - 1)⁻¹ • (R.classMatrix *ᵥ x), ?_, ?_⟩
    · change ∑ i, ((2 * (k : ℝ) - 1)⁻¹ • (R.classMatrix *ᵥ x)) i = 0
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        R.sum_classMatrix_mulVec, hsum, mul_zero]
    · change R.classMatrixᵀ *ᵥ ((2 * (k : ℝ) - 1)⁻¹ • (R.classMatrix *ᵥ x)) = x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      exact he

/-- The incidence-image space is the `-k` eigenspace (`s5exv2`,
Example 5.13 of [CGSS]). -/
theorem W₂_eq_eigenspace :
    W₂ (D := D) = Module.End.eigenspace (R.graph.adjMatrix ℝ).toLin'
      (Matrix.resolutionEigenvalues k 2) := by
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast D.one_lt_k
  have hz : 2 * (k : ℝ) ≠ 0 := by linarith
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ∑ p, y p = 0 at hy
    have hNy : D.realIncMatrix *ᵥ (D.realIncMatrixᵀ *ᵥ y) = (2 * k : ℝ) • y := by
      rw [Matrix.mulVec_mulVec, realIncMatrix_mul_transpose (D := D), Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, allOnes_mulVec, hy, zero_smul, add_zero]
    have hsum : ∑ b, (D.realIncMatrixᵀ *ᵥ y) b = 0 := by
      rw [sum_transpose_realIncMatrix_mulVec, hy, mul_zero]
    apply Module.End.mem_eigenspace_iff.mpr
    apply R.eigenvector_of_projection_fixed 2
    dsimp [projections, Matrix.resolutionProjections]
    simp only [← Matrix.smul_of]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, allOnes_mulVec,
      hsum, zero_smul, smul_zero, sub_zero, ← Matrix.mulVec_mulVec, hNy,
      Matrix.mulVec_smul, inv_smul_smul₀ hz]
  · intro hx
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    have hsum := R.sum_eq_zero_of_eigenvector (by decide : (2 : Fin 4) ≠ 0) hx'
    have he := R.projections_mulVec_of_eigenvector 2 2 hx'
    rw [ite_eq_left rfl] at he
    dsimp [projections, Matrix.resolutionProjections] at he
    simp only [← Matrix.smul_of] at he
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, allOnes_mulVec,
      hsum, zero_smul, smul_zero, sub_zero] at he
    refine ⟨(2 * (k : ℝ))⁻¹ • (D.realIncMatrix *ᵥ x), ?_, ?_⟩
    · change ∑ p, ((2 * (k : ℝ))⁻¹ • (D.realIncMatrix *ᵥ x)) p = 0
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        sum_realIncMatrix_mulVec, hsum, mul_zero]
    · change D.realIncMatrixᵀ *ᵥ ((2 * (k : ℝ))⁻¹ • (D.realIncMatrix *ᵥ x)) = x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      exact he

/-- The common kernel is the `k` eigenspace (`s5exv3`, Example 5.13 of [CGSS]). -/
theorem W₃_eq_eigenspace :
    R.W₃ = Module.End.eigenspace (R.graph.adjMatrix ℝ).toLin'
      (Matrix.resolutionEigenvalues k 3) := by
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast D.one_lt_k
  have hq : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have hz : 2 * (k : ℝ) ≠ 0 := by linarith
  ext x
  constructor
  · rintro ⟨hN, hC⟩
    change D.realIncMatrix *ᵥ x = 0 at hN
    change R.classMatrix *ᵥ x = 0 at hC
    have hsum : ∑ a, x a = 0 := by rw [← R.sum_classMatrix_mulVec, hC]; simp
    apply Module.End.mem_eigenspace_iff.mpr
    apply R.eigenvector_of_projection_fixed 3
    dsimp [projections, Matrix.resolutionProjections]
    simp only [← Matrix.smul_of]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hN, hC, Matrix.mulVec_zero, allOnes_mulVec, hsum,
      zero_smul, smul_zero, sub_zero]
  · intro hx
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    have hsum := R.sum_eq_zero_of_eigenvector (by decide : (3 : Fin 4) ≠ 0) hx'
    have hC := R.projections_mulVec_of_eigenvector 1 3 hx'
    have hN := R.projections_mulVec_of_eigenvector 2 3 hx'
    norm_num only [show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide,
      ite_false] at hC hN
    dsimp [projections, Matrix.resolutionProjections] at hC hN
    simp only [← Matrix.smul_of] at hC hN
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, allOnes_mulVec, hsum,
      zero_smul, smul_zero, sub_zero] at hC hN
    have hQ := (smul_eq_zero.mp hC).resolve_left (inv_ne_zero hq)
    have hG := (smul_eq_zero.mp hN).resolve_left (inv_ne_zero hz)
    constructor
    · have hxK : x ∈ LinearMap.ker (D.realIncMatrixᵀ * D.realIncMatrix).mulVecLin := hG
      rw [Matrix.ker_mulVecLin_transpose_mul_self] at hxK
      exact hxK
    · have hxK : x ∈ LinearMap.ker (R.classMatrixᵀ * R.classMatrix).mulVecLin := hQ
      rw [Matrix.ker_mulVecLin_transpose_mul_self] at hxK
      exact hxK

/-- The class indicators are independent (`s5exd12`, Example 5.13 of [CGSS]). -/
theorem classMatrix_transpose_mulVec_injective :
    Function.Injective (R.classMatrixᵀ.mulVec) := by
  have hq : ((2 * k - 1 : ℕ) : ℝ) ≠ 0 := by
    have := D.one_lt_k
    exact_mod_cast (show 2 * k - 1 ≠ 0 by omega)
  intro a b hab
  have he := congrArg (fun x ↦ (((2 * k - 1 : ℕ) : ℝ)⁻¹) •
    (R.classMatrix *ᵥ x)) hab
  simpa only [Matrix.mulVec_mulVec, R.classMatrix_mul_transpose,
    Matrix.smul_mulVec, Matrix.one_mulVec, inv_smul_smul₀ hq] using he

/-- The kernel dimension in `s5exd3k`, Example 5.13 of [CGSS]. -/
theorem finrank_ker_realIncMatrix :
    Module.finrank ℝ (LinearMap.ker D.realIncMatrix.toLin') =
      (4 * k ^ 2 - 1) - k * (2 * k - 1) := by
  have h := D.realIncMatrix.toLin'.finrank_range_add_finrank_ker
  change D.realIncMatrix.rank + Module.finrank ℝ (LinearMap.ker D.realIncMatrix.toLin') =
    Module.finrank ℝ (B → ℝ) at h
  rw [rank_realIncMatrix, Module.finrank_pi, D.card_blocks] at h
  omega

/-- Transposed incidence is injective (`s5exd12`, Example 5.13 of [CGSS]). -/
theorem realIncMatrix_transpose_mulVec_injective :
    Function.Injective D.realIncMatrixᵀ.mulVec := by
  change Function.Injective D.realIncMatrixᵀ.toLin'
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := D.realIncMatrixᵀ.toLin'.finrank_range_add_finrank_ker
  change D.realIncMatrixᵀ.rank +
    Module.finrank ℝ (LinearMap.ker D.realIncMatrixᵀ.toLin') =
      Module.finrank ℝ (P → ℝ) at h
  rw [Matrix.rank_transpose, rank_realIncMatrix, Module.finrank_pi, D.card_points] at h
  omega

/-- The inclusion in `s5exd3w`, Example 5.13 of [CGSS]. -/
theorem W₁_le_ker_realIncMatrix : R.W₁ ≤ LinearMap.ker D.realIncMatrix.toLin' := by
  rintro x ⟨a, ha, rfl⟩
  change ∑ i, a i = 0 at ha
  change D.realIncMatrix *ᵥ (R.classMatrixᵀ *ᵥ a) = 0
  rw [Matrix.mulVec_mulVec, R.realIncMatrix_mul_classMatrix_transpose,
    allOnes_mulVec, ha, zero_smul]

/-- The orthogonal-complement description in `s5exd3p`, Example 5.13 of [CGSS].
`W₃` is the complement of `W₁` inside `ker N`, with the real dot product. -/
theorem mem_W₃_iff_ker_and_orthogonal {x : B → ℝ} :
    x ∈ R.W₃ ↔ D.realIncMatrix *ᵥ x = 0 ∧ ∀ y ∈ R.W₁, y ⬝ᵥ x = 0 := by
  constructor
  · rintro ⟨hN, hC⟩
    refine ⟨hN, ?_⟩
    rintro y ⟨a, _, rfl⟩
    change (R.classMatrixᵀ *ᵥ a) ⬝ᵥ x = 0
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec,
      (show R.classMatrix *ᵥ x = 0 from hC), dotProduct_zero]
  · rintro ⟨hN, ho⟩
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by have := D.one_lt_k; omega : k ≠ 0)
    have hsum : ∑ a, x a = 0 := by
      have he := sum_realIncMatrix_mulVec (D := D) x
      rw [hN] at he
      simp only [Pi.zero_apply, Finset.sum_const_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hk
    have hCx : R.classMatrix *ᵥ x ∈ zeroSum (Fin (2 * k + 1)) := by
      change ∑ i, (R.classMatrix *ᵥ x) i = 0
      rw [R.sum_classMatrix_mulVec, hsum]
    have he := ho (R.classMatrixᵀ *ᵥ (R.classMatrix *ᵥ x))
      ⟨R.classMatrix *ᵥ x, hCx, rfl⟩
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec,
      dotProduct_self_eq_zero] at he
    exact ⟨hN, he⟩

/-- The three dimensions in `s5exdims`, Example 5.13 of [CGSS]. -/
theorem finrank_W₁_W₂_W₃ :
    Module.finrank ℝ R.W₁ = 2 * k ∧
      Module.finrank ℝ (W₂ (D := D)) = (k - 1) * (2 * k + 1) ∧
      Module.finrank ℝ R.W₃ = (k - 1) * (2 * k + 1) := by
  rw [R.W₁_eq_eigenspace, R.W₂_eq_eigenspace, R.W₃_eq_eigenspace]
  exact ⟨R.finrank_eigenspace 1, R.finrank_eigenspace 2, R.finrank_eigenspace 3⟩

end Design.Resolution
