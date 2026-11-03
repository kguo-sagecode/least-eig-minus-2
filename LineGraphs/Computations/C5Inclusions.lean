/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Inclusions
import LineGraphs.LineSystem.ModelSpans
import LineGraphs.Computations.ModelTables

/-!
# Computation C5: the three inclusions of equal rank

Steps `s3c5Aeight`, `s3c5Deight` and `s3c5Aseven` of `blueprint/sec3-rootsystems.tex`: proper
isometric inclusions `A₈ ⊂ E₈`, `D₈ ⊂ E₈` and `A₇ ⊂ E₇` of equal rank, into the default models
`E₈ = E₈viaD₈` and `E₇ = E₈ ∩ (e₇ - e₈)^⊥`. (`A₈ ⊂ E₈viaA₈` is literal as well.)

`D₈ ⊂ E₈` is literal. The other two are explicit linear maps `x ↦ ∑ᵢ xᵢ dᵢ` with `d₀ = 0`,
checked on the roots by `decide +kernel`, in doubled coordinates:
* `A₈ ⊂ E₈`: `dᵢ = e₀ + eᵢ` for `1 ≤ i ≤ 7` and `d₈ = ½𝟙`;
* `A₇ ⊂ E₇`: `dᵢ = e₀ + eᵢ` for `1 ≤ i ≤ 5`, `d₆ = ½𝟙`, `d₇ = ½(1,1,1,1,1,1,-1,-1)`.
Each `dᵢ` has squared norm 2, the `dᵢ` have pairwise inner product 1, and all differences are roots,
so `eᵢ - eⱼ ↦ dᵢ - dⱼ` preserves inner products. This replaces the paper's embedding of marked
graphs (errata Error 5) and the blueprint's automorphism of `E₈` carrying `½𝟙` to `e₇ - e₈` by an
explicit coordinate inclusion.
-/

open scoped RealInnerProductSpace
open Finset Module Submodule

namespace LineSystem

/-- The number of roots of an integer model. -/
theorem IntegerModel.ncard_Φ {n : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin n))}
    (M : IntegerModel S) : S.Φ.ncard = Fintype.card M.ι := by
  rw [M.Φ_eq, Set.ncard_range_of_injective ((integerVector_injective M.c_ne_zero).comp M.inj),
    Nat.card_eq_fintype_card]

/-- The real linear map `x ↦ c · ∑ᵢ xᵢ Aᵢ` given by integer rows `Aᵢ`. -/
noncomputable def intLin {m n : ℕ} (c : ℝ) (A : Fin m → Fin n → ℤ) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 fun k => c * ∑ i, x i * (A i k : ℝ)
  map_add' x y := by
    ext k
    simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a x := by
    ext k
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem intLin_integerVector {m n : ℕ} (c d : ℝ) (A : Fin m → Fin n → ℤ) (v : Fin m → ℤ) :
    intLin c A (integerVector d v) = integerVector (c * d) fun k => ∑ i, v i * A i k := by
  ext k
  simp only [intLin, LinearMap.coe_mk, AddHom.coe_mk, integerVector_apply,
    Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The inner products of images under `intLin` are given by the Gram matrix of the rows. -/
theorem inner_intLin {m n : ℕ} (c : ℝ) (A : Fin m → Fin n → ℤ) (x y : EuclideanSpace ℝ (Fin m)) :
    ⟪intLin c A x, intLin c A y⟫ =
      c * c * ∑ i, ∑ j, x i * y j * (integerInner (A i) (A j) : ℝ) := by
  simp only [intLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, integerInner, dotProduct, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- If the Gram matrix of the rows is `4I + f 𝟙ᵀ + 𝟙 fᵀ`, then at scale `1/2` the map preserves
inner products of coordinate-sum-zero vectors. -/
theorem inner_intLin_half_of_gram {m n : ℕ} (A : Fin m → Fin n → ℤ) (f : Fin m → ℤ)
    (hG : ∀ i j, integerInner (A i) (A j) = 4 * (if i = j then 1 else 0) + f i + f j)
    {x y : EuclideanSpace ℝ (Fin m)} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    ⟪intLin (1 / 2) A x, intLin (1 / 2) A y⟫ = ⟪x, y⟫ := by
  rw [inner_intLin]
  simp only [hG]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have h1 : ∑ i, ∑ j, x i * y j * (f i : ℝ) = 0 := by
    simp only [mul_comm (x _) (y _), mul_assoc, ← Finset.sum_mul, hy, zero_mul,
      Finset.sum_const_zero]
  have h2 : ∑ i, ∑ j, x i * y j * (f j : ℝ) = 0 := by
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hx, zero_mul]
  rw [h1, h2, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Finset.mul_sum, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The image of the difference root `eᵢ - eⱼ`. -/
theorem sum_pairVector_mul {m n : ℕ} (A : Fin m → Fin n → ℤ) (i j : Fin m) (k : Fin n) :
    ∑ l, pairVector i j 1 (-1) l * A l k = A i k - A j k := by
  simp [pairVector, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]

/-- An inclusion of `Aₙ` given by rows `dᵢ` (doubled) with Gram matrix `4I + f 𝟙ᵀ + 𝟙 fᵀ`, whose
differences are (doubled) roots of the target. -/
noncomputable def IsometricInclusion.ofRows {n d : ℕ} {T : LineSystem (EuclideanSpace ℝ (Fin d))}
    (A : Fin (n + 1) → Fin d → ℤ) (f : Fin (n + 1) → ℤ)
    (hG : ∀ i j, integerInner (A i) (A j) = 4 * (if i = j then 1 else 0) + f i + f j)
    (hmem : ∀ i j, i ≠ j → integerVector (1 / 2) (A i - A j) ∈ T.Φ) :
    IsometricInclusion (An n) T :=
  IsometricInclusion.ofLinearMap (intLin (1 / 2) A)
    (fun r hr s hs => inner_intLin_half_of_gram A f hG
      (span_An_le_ker_coordinateSum n (subset_span hr))
      (span_An_le_ker_coordinateSum n (subset_span hs)))
    (by
      rintro _ ⟨a, rfl⟩
      change intLin (1 / 2) A (integerVector 1 (pairVector a.val.1 a.val.2 1 (-1))) ∈ T.Φ
      rw [intLin_integerVector, mul_one]
      convert hmem a.val.1 a.val.2 a.property using 2
      funext k
      rw [sum_pairVector_mul]
      rfl)

/-- The rows `dᵢ` (doubled) of the inclusion `A₈ ⊂ E₈`: `d₀ = 0`, `dᵢ = e₀ + eᵢ` (`1 ≤ i ≤ 7`),
`d₈ = ½𝟙`. -/
def a₈Rows : Fin 9 → Fin 8 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0], ![2, 0, 2, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 2, 0, 0, 0], ![2, 0, 0, 0, 0, 2, 0, 0],
    ![2, 0, 0, 0, 0, 0, 2, 0], ![2, 0, 0, 0, 0, 0, 0, 2], ![1, 1, 1, 1, 1, 1, 1, 1]]

/-- The rows `dᵢ` (doubled) of the inclusion `A₇ ⊂ E₇`: `d₀ = 0`, `dᵢ = e₀ + eᵢ` (`1 ≤ i ≤ 5`),
`d₆ = ½𝟙`, `d₇ = ½(1,1,1,1,1,1,-1,-1)`. -/
def a₇Rows : Fin 8 → Fin 8 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![2, 2, 0, 0, 0, 0, 0, 0], ![2, 0, 2, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 0, 0, 0, 0], ![2, 0, 0, 0, 2, 0, 0, 0], ![2, 0, 0, 0, 0, 2, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, -1, -1]]

end LineSystem

namespace Computations.C5

open LineSystem

-- Computation C5, step s3c5Aeight
/-- C5: the Gram matrix of the rows of `A₈ ⊂ E₈`. -/
theorem a₈_rows_gram : ∀ i j : Fin 9, integerInner (a₈Rows i) (a₈Rows j) =
    4 * (if i = j then 1 else 0) + (if i = 0 then -2 else 2) + (if j = 0 then -2 else 2) := by
  decide +kernel

-- Computation C5, step s3c5Aeight
/-- C5: the differences of the rows of `A₈ ⊂ E₈` are (doubled) roots of `E₈`. -/
theorem a₈_rows_mem : ∀ i j : Fin 9, i ≠ j → isE₈Root (a₈Rows i - a₈Rows j) = true := by
  decide +kernel

-- Computation C5, step s3c5Aseven
/-- C5: the Gram matrix of the rows of `A₇ ⊂ E₇`. -/
theorem a₇_rows_gram : ∀ i j : Fin 8, integerInner (a₇Rows i) (a₇Rows j) =
    4 * (if i = j then 1 else 0) + (if i = 0 then -2 else 2) + (if j = 0 then -2 else 2) := by
  decide +kernel

-- Computation C5, step s3c5Aseven
/-- C5: the differences of the rows of `A₇ ⊂ E₇` are (doubled) roots of `E₇`. -/
theorem a₇_rows_mem : ∀ i j : Fin 8, i ≠ j → isE₇Root (a₇Rows i - a₇Rows j) = true := by
  decide +kernel

end Computations.C5

namespace LineSystem

open Computations.C5

-- Computation C5, step s3c5Aeight
/-- C5: an isometric inclusion `A₈ ⊂ E₈` (into the default model (ii)). -/
noncomputable def An.inclusionE₈ : IsometricInclusion (An 8) E₈ :=
  IsometricInclusion.ofRows a₈Rows _ a₈_rows_gram
    fun i j h => (integerVector_mem_E₈_iff _).mpr (a₈_rows_mem i j h)

-- Computation C5, step s3c5Aseven
/-- C5: an isometric inclusion `A₇ ⊂ E₇`. -/
noncomputable def An.inclusionE₇ : IsometricInclusion (An 7) E₇ :=
  IsometricInclusion.ofRows a₇Rows _ a₇_rows_gram
    fun i j h => (integerVector_mem_E₇_iff _).mpr (a₇_rows_mem i j h)

-- Computation C5, step s3c5Deight
/-- C5: the literal isometric inclusion `D₈ ⊂ E₈`. -/
noncomputable def Dn.inclusionE₈ : IsometricInclusion (Dn 8) E₈ :=
  IsometricInclusion.ofSubset Dn_Φ_subset_E₈

/-- The literal isometric inclusion `A₈ ⊂ E₈viaA₈` (model (i)). -/
noncomputable def An.inclusionE₈viaA₈ : IsometricInclusion (An 8) E₈viaA₈ :=
  IsometricInclusion.ofSubset An_Φ_subset_E₈viaA₈

theorem ncard_Φ_An (n : ℕ) : (An n).Φ.ncard = n * (n + 1) := by
  rw [(An.integerModel n).ncard_Φ]
  exact card_AnIndex n

theorem ncard_Φ_Dn (n : ℕ) : (Dn n).Φ.ncard = n.choose 2 * 4 := by
  rw [(Dn.integerModel n).ncard_Φ]
  exact card_DnIndex n

theorem ncard_Φ_E₈ : E₈.Φ.ncard = 240 := by
  rw [E₈viaD₈.integerModel.ncard_Φ]
  exact card_E₈Index

theorem ncard_Φ_E₈viaA₈ : E₈viaA₈.Φ.ncard = 240 := by
  rw [E₈viaA₈.integerModel.ncard_Φ]
  exact card_E₈AIndex

theorem ncard_Φ_E₇ : E₇.Φ.ncard = 126 := by
  rw [E₇.integerModel.ncard_Φ]
  exact card_E₇Index

-- Computation C5, step s3c5Aeight
/-- C5: `A₈ ⊂ E₈` is proper (72 < 240 roots). -/
theorem An.inclusionE₈_isProper : An.inclusionE₈.IsProper :=
  IsometricInclusion.isProper_of_ncard_lt _ (by rw [ncard_Φ_An, ncard_Φ_E₈]; norm_num)

-- Computation C5, step s3c5Aseven
/-- C5: `A₇ ⊂ E₇` is proper (56 < 126 roots). -/
theorem An.inclusionE₇_isProper : An.inclusionE₇.IsProper :=
  IsometricInclusion.isProper_of_ncard_lt _ (by rw [ncard_Φ_An, ncard_Φ_E₇]; norm_num)

-- Computation C5, step s3c5Deight
/-- C5: `D₈ ⊂ E₈` is proper (112 < 240 roots). -/
theorem Dn.inclusionE₈_isProper : Dn.inclusionE₈.IsProper :=
  IsometricInclusion.isProper_of_ncard_lt _ (by rw [ncard_Φ_Dn, ncard_Φ_E₈]; decide)

/-- `A₈ ⊂ E₈viaA₈` is proper (72 < 240 roots). -/
theorem An.inclusionE₈viaA₈_isProper : An.inclusionE₈viaA₈.IsProper :=
  IsometricInclusion.isProper_of_ncard_lt _ (by rw [ncard_Φ_An, ncard_Φ_E₈viaA₈]; norm_num)

-- Theorem 3.6, step s336excluded
/-- Theorem 3.6, step `s336exclAseven`: `A₇` is not maximal within its span. -/
theorem An.not_isMaximal_seven : ¬ (An 7).IsMaximal :=
  not_isMaximal_of_proper_isometric_inclusion An.inclusionE₇
    (by rw [finrank_span_An, finrank_span_E₇]) An.inclusionE₇_isProper

-- Theorem 3.6, step s336excluded
/-- Theorem 3.6, step `s336exclAeight`: `A₈` is not maximal within its span. -/
theorem An.not_isMaximal_eight : ¬ (An 8).IsMaximal :=
  not_isMaximal_of_proper_isometric_inclusion An.inclusionE₈
    (by rw [finrank_span_An, finrank_span_E₈]) An.inclusionE₈_isProper

-- Theorem 3.6, step s336excluded
/-- Theorem 3.6, step `s336exclDeight`: `D₈` is not maximal within its span. -/
theorem Dn.not_isMaximal_eight : ¬ (Dn 8).IsMaximal :=
  not_isMaximal_of_proper_isometric_inclusion Dn.inclusionE₈
    (by rw [finrank_span_Dn (by norm_num), finrank_span_E₈]) Dn.inclusionE₈_isProper

end LineSystem
