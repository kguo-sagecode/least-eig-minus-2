/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.DenseEmbedding

/-!
# Integer and real positivity

The null-form lemma and Lemma (integer positivity), `lem:integer-positive` of
`cgss/proofs/remark311/remark311.tex`.
The latter follows the determinant proof in `blueprint/sec3-remark311.tex`: clear rational
denominators, use density for nonnegativity, and descend a zero determinant to the integers.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- A null vector of a nonnegative real symmetric quadratic form lies in its kernel
(`lem:rem-null` in the Remark 3.11 blueprint). -/
theorem mulVec_eq_zero_of_quadratic_eq_zero {Q : Matrix ι ι ℝ}
    (hQ : Q.IsSymm) (hnonneg : ∀ x, 0 ≤ x ⬝ᵥ (Q *ᵥ x))
    {y : ι → ℝ} (hy : y ⬝ᵥ (Q *ᵥ y) = 0) : Q *ᵥ y = 0 := by
  have hpos : Q.PosSemidef := .of_dotProduct_mulVec_nonneg
    (isHermitian_iff_isSymm.mpr hQ) (by simpa only [star_trivial] using hnonneg)
  exact (hpos.dotProduct_mulVec_zero_iff y).mp (by simpa only [star_trivial] using hy)

/-- Clearing denominators extends nonnegativity of an integer quadratic form to rational
vectors, viewed in the reals. This is step `riclear` of Lemma (integer positivity),
`lem:integer-positive`. -/
theorem quadratic_nonneg_rat_of_posSemidef_int {H : Matrix ι ι ℤ}
    (hH : H.PosSemidef) (v : ι → ℚ) :
    0 ≤ (fun i => (v i : ℝ)) ⬝ᵥ (H.map (Int.castRingHom ℝ) *ᵥ
      (fun i => (v i : ℝ))) := by
  classical
  obtain ⟨⟨k, hk⟩, hz⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
  choose z hz using hz
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hk
  have hzr (i : ι) : (z i : ℝ) = (k : ℝ) * (v i : ℝ) := by
    have hi : (z i : ℚ) = (k : ℚ) * v i := by
      simpa only [Algebra.smul_def, eq_intCast, Subtype.coe_mk] using hz i
    exact_mod_cast hi
  have hp : (0 : ℝ) ≤ (z ⬝ᵥ (H *ᵥ z) : ℤ) := by
    exact_mod_cast (show (0 : ℤ) ≤ z ⬝ᵥ (H *ᵥ z) by
      simpa only [star_trivial] using hH.dotProduct_mulVec_nonneg z)
  have heq : (z ⬝ᵥ (H *ᵥ z) : ℤ) =
      (k : ℝ) ^ 2 * ((fun i => (v i : ℝ)) ⬝ᵥ
        (H.map (Int.castRingHom ℝ) *ᵥ (fun i => (v i : ℝ)))) := by
    simp only [dotProduct, mulVec, Int.cast_sum, Int.cast_mul, map_apply,
      Int.coe_castRingHom, hzr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hp
  exact nonneg_of_mul_nonneg_right hp (sq_pos_of_ne_zero hk0)

omit [Fintype ι] in
/-- Step `riposr` of Lemma (integer positivity), `lem:integer-positive`: the real cast of an
integer positive semidefinite matrix
is positive semidefinite, by density of rational vectors. -/
theorem posSemidef_real_of_posSemidef_int [Finite ι] {H : Matrix ι ι ℤ} (hH : H.PosSemidef) :
    (H.map (Int.castRingHom ℝ)).PosSemidef := by
  let := Fintype.ofFinite ι
  refine .of_dotProduct_mulVec_nonneg
    (hH.isHermitian.map _ (by intro x; simp)) ?_
  simp only [star_trivial]
  have hdense : DenseRange (fun v : ι → ℚ => fun i => (v i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  intro x
  refine hdense.induction_on x ?_ (quadratic_nonneg_rat_of_posSemidef_int hH)
  apply isClosed_le continuous_const
  unfold dotProduct mulVec
  fun_prop

omit [Fintype ι] in
/-- Lemma (integer positivity), `lem:integer-positive` of the blueprint for Remark 3.11 of [CGSS]:
positive definiteness over the integers extends
to the reals. The exclusion of a null vector uses the determinant over both domains. -/
theorem posDef_real_of_posDef_int [Finite ι] {H : Matrix ι ι ℤ} (hH : H.PosDef) :
    (H.map (Int.castRingHom ℝ)).PosDef := by
  classical
  let := Fintype.ofFinite ι
  have hnonneg := posSemidef_real_of_posSemidef_int hH.posSemidef
  refine .of_dotProduct_mulVec_pos hnonneg.isHermitian ?_
  intro y hy
  have hge := hnonneg.dotProduct_mulVec_nonneg y
  refine lt_of_le_of_ne hge ?_
  intro hzero
  have hker := (hnonneg.dotProduct_mulVec_zero_iff y).mp hzero.symm
  have hdet := exists_mulVec_eq_zero_iff.mp ⟨y, hy, hker⟩
  have hdetZ : H.det = 0 := by
    change ((Int.castRingHom ℝ).mapMatrix H).det = 0 at hdet
    rw [← RingHom.map_det] at hdet
    change (H.det : ℝ) = 0 at hdet
    exact_mod_cast hdet
  obtain ⟨z, hz, hHz⟩ := exists_mulVec_eq_zero_iff.mpr hdetZ
  have hp := hH.dotProduct_mulVec_pos hz
  simp only [hHz, dotProduct_zero, lt_self_iff_false] at hp

end Matrix
