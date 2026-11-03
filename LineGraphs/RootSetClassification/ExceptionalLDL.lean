/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Converse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Rational positivity certificates for the exceptional matrices

`comp:rem-ldl` of the blueprint for Remark 3.11 of [CGSS]: for `M` one of `E₆`, `E₇`,
`E₈`, `F₄`, `G₂` and `H = diag(d) M` with the symmetrizer `d` of `eq:symmetrizers`, a unit
lower triangular rational `L` and positive rational pivots `q` with `H = L diag(q) Lᵀ`.
The identity `xᵀ H x = ∑ᵢ q i ((Lᵀ x) i)²` and the injectivity of `Lᵀ` then make `H`
positive definite (`Matrix.posDef_of_ldl`).
-/

open Matrix

namespace Matrix

variable {n : ℕ}

/-- Step `rldlform` of Remark 3.11: the quadratic form of `L diag(q) Lᵀ` is a weighted sum
of squares of the coordinates of `Lᵀ x`. -/
theorem dotProduct_ldl_mulVec (L : Matrix (Fin n) (Fin n) ℚ) (q : Fin n → ℚ)
    (x : Fin n → ℚ) :
    x ⬝ᵥ ((L * diagonal q * Lᵀ) *ᵥ x) = ∑ i, q i * ((Lᵀ *ᵥ x) i) ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Step `rldlinjective` of Remark 3.11: the transpose of a unit lower triangular matrix
has trivial kernel. -/
theorem transpose_mulVec_injective_of_unitLower (L : Matrix (Fin n) (Fin n) ℚ)
    (hL : ∀ i j, i < j → L i j = 0) (hL1 : ∀ i, L i i = 1) :
    Function.Injective Lᵀ.mulVec := by
  have hdet : Lᵀ.det = 1 := by
    rw [det_of_isUpperTriangular (M := Lᵀ) (fun i j hij ↦ hL j i hij)]
    simp [hL1]
  exact mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (by simp [hdet]))

/-- The conclusion of `comp:rem-ldl` in Remark 3.11: an integer matrix with a rational
factorization `L diag(q) Lᵀ`, for a unit lower triangular `L` and positive pivots `q`, is
positive definite. -/
theorem posDef_of_ldl (H : Matrix (Fin n) (Fin n) ℤ) (L : Matrix (Fin n) (Fin n) ℚ)
    (q : Fin n → ℚ) (hL : ∀ i j, i < j → L i j = 0) (hL1 : ∀ i, L i i = 1)
    (hq : ∀ i, 0 < q i) (hH : H.map (Int.cast : ℤ → ℚ) = L * diagonal q * Lᵀ) :
    H.PosDef := by
  have hsymm : Hᵀ = H := by
    apply map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
    dsimp only
    rw [transpose_map, hH]
    simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hsymm]
  · rw [star_trivial]
    have hcast : ((x ⬝ᵥ (H *ᵥ x) : ℤ) : ℚ) =
        (fun i ↦ (x i : ℚ)) ⬝ᵥ ((H.map (Int.cast : ℤ → ℚ)) *ᵥ fun i ↦ (x i : ℚ)) := by
      simp [dotProduct, mulVec, map_apply]
    have hne : (fun i ↦ (x i : ℚ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      simpa using congrFun h i
    have hy : Lᵀ *ᵥ (fun i ↦ (x i : ℚ)) ≠ 0 := by
      intro h
      apply hne
      apply transpose_mulVec_injective_of_unitLower L hL hL1
      rw [h, mulVec_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have hi' : (Lᵀ *ᵥ fun i ↦ (x i : ℚ)) i ≠ 0 := by simpa using hi
    have hpos : (0 : ℚ) < ∑ j, q j * ((Lᵀ *ᵥ fun i ↦ (x i : ℚ)) j) ^ 2 :=
      Finset.sum_pos' (fun j _ ↦ mul_nonneg (hq j).le (sq_nonneg _))
        ⟨i, Finset.mem_univ i,
          mul_pos (hq i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi')))⟩
    rw [← dotProduct_ldl_mulVec, ← hH, ← hcast] at hpos
    exact_mod_cast hpos

end Matrix

namespace RootSetModel

open CartanMatrix

/-- The exceptional types of `comp:rem-ldl` in Remark 3.11. -/
def IsExceptional {n : ℕ} : FiniteType n → Prop
  | .e₆ | .e₇ | .e₈ | .f₄ | .g₂ => True
  | _ => False

/-- The integer symmetrizers of `eq:symmetrizers` in Remark 3.11. -/
def symmetrizer {n : ℕ} : FiniteType n → Fin n → ℤ
  | .b n _ => fun i ↦ if i.val + 1 = n then 2 else 1
  | .c n _ => fun i ↦ if i.val + 1 = n then 1 else 2
  | .f₄ => ![1, 1, 2, 2]
  | .g₂ => ![1, 3]
  | _ => fun _ ↦ 1

/-- The symmetrizer of `comp:rem-ldl` is the one in Theorem A of the blueprint for Remark 3.11 of
[CGSS]
(`eq:symmetrizers` and `def:rem-matrices`). -/
theorem symmetrizer_eq_modelSymmetrizer {n : ℕ} (t : FiniteType n) :
    symmetrizer t = modelSymmetrizer t := by
  cases t with
  | b n hn | c n hn =>
    funext i
    have h : i.val + 1 = n ↔ i.val = n - 1 := by omega
    simp only [symmetrizer, modelSymmetrizer, h]
  | a _ _ | d _ _ | e₆ | e₇ | e₈ | f₄ | g₂ => rfl

/-- The eight-row unit lower triangular certificate for `E₈` in `comp:rem-ldl`. -/
def e₈Lower : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     -1/2, 0, 1, 0, 0, 0, 0, 0;
     0, -1/2, -2/3, 1, 0, 0, 0, 0;
     0, 0, 0, -6/5, 1, 0, 0, 0;
     0, 0, 0, 0, -5/4, 1, 0, 0;
     0, 0, 0, 0, 0, -4/3, 1, 0;
     0, 0, 0, 0, 0, 0, -3/2, 1]

/-- The eight positive pivots for `E₈` in `comp:rem-ldl`. -/
def e₈Pivots : Fin 8 → ℚ := ![2, 2, 3/2, 5/6, 4/5, 3/4, 2/3, 1/2]

/-- The unit lower triangular factors of `comp:rem-ldl`; for `E₆` and `E₇` the leading
rows of the `E₈` data. The other types are not used. -/
def ldlLower {n : ℕ} : FiniteType n → Matrix (Fin n) (Fin n) ℚ
  | .e₆ => e₈Lower.submatrix (Fin.castLE (by norm_num)) (Fin.castLE (by norm_num))
  | .e₇ => e₈Lower.submatrix (Fin.castLE (by norm_num)) (Fin.castLE (by norm_num))
  | .e₈ => e₈Lower
  | .f₄ => !![1, 0, 0, 0; -1/2, 1, 0, 0; 0, -4/3, 1, 0; 0, 0, -3/2, 1]
  | .g₂ => !![1, 0; -3/2, 1]
  | _ => 1

/-- The positive pivots of `comp:rem-ldl`; for `E₆` and `E₇` the leading entries of the
`E₈` data. The other types are not used. -/
def ldlPivots {n : ℕ} : FiniteType n → Fin n → ℚ
  | .e₆ => fun i ↦ e₈Pivots (Fin.castLE (by norm_num) i)
  | .e₇ => fun i ↦ e₈Pivots (Fin.castLE (by norm_num) i)
  | .e₈ => e₈Pivots
  | .f₄ => ![2, 3/2, 4/3, 1]
  | .g₂ => ![2, 3/2]
  | _ => fun _ ↦ 1

/-- Steps `rldlE`--`rldlG` of Remark 3.11: the finite entry identities
`H(i, j) = ∑ₖ L(i, k) q(k) L(j, k)`. -/
theorem ldl_eq {n : ℕ} (t : FiniteType n) (ht : IsExceptional t) :
    (diagonal (symmetrizer t) * modelEntries t).map (Int.cast : ℤ → ℚ) =
      ldlLower t * diagonal (ldlPivots t) * (ldlLower t)ᵀ := by
  cases t with
  | a _ _ | b _ _ | c _ _ | d _ _ => exact ht.elim
  | e₆ | e₇ | e₈ | f₄ | g₂ => decide +kernel

-- Remark 3.11, comp:rem-ldl
/-- The rational positivity certificates of `comp:rem-ldl` in Remark 3.11 of [CGSS]: for
`M` one of `E₆`, `E₇`, `E₈`, `F₄`, `G₂` and `H = diag(d) M`, the matrix `L = ldlLower t` is
unit lower triangular, the pivots `q = ldlPivots t` are positive, `H = L diag(q) Lᵀ`,
`xᵀ H x = ∑ᵢ q i ((Lᵀ x) i)²`, and `H` is positive definite. -/
theorem exceptional_ldl {n : ℕ} (t : FiniteType n) (ht : IsExceptional t) :
    (∀ i j, i < j → ldlLower t i j = 0) ∧ (∀ i, ldlLower t i i = 1) ∧
    (∀ i, 0 < ldlPivots t i) ∧
    (diagonal (symmetrizer t) * modelEntries t).map (Int.cast : ℤ → ℚ) =
      ldlLower t * diagonal (ldlPivots t) * (ldlLower t)ᵀ ∧
    (∀ x : Fin n → ℚ,
      x ⬝ᵥ ((diagonal (symmetrizer t) * modelEntries t).map (Int.cast : ℤ → ℚ) *ᵥ x) =
        ∑ i, ldlPivots t i * (((ldlLower t)ᵀ *ᵥ x) i) ^ 2) ∧
    (diagonal (symmetrizer t) * modelEntries t).PosDef := by
  have hL : ∀ i j, i < j → ldlLower t i j = 0 := by
    cases t with
    | a _ _ | b _ _ | c _ _ | d _ _ => exact ht.elim
    | e₆ =>
      exact fun i j hij ↦ (by decide +kernel : ∀ p : Fin 6 × Fin 6, p.1 < p.2 →
        ldlLower .e₆ p.1 p.2 = 0) (i, j) hij
    | e₇ =>
      exact fun i j hij ↦ (by decide +kernel : ∀ p : Fin 7 × Fin 7, p.1 < p.2 →
        ldlLower .e₇ p.1 p.2 = 0) (i, j) hij
    | e₈ =>
      exact fun i j hij ↦ (by decide +kernel : ∀ p : Fin 8 × Fin 8, p.1 < p.2 →
        ldlLower .e₈ p.1 p.2 = 0) (i, j) hij
    | f₄ =>
      exact fun i j hij ↦ (by decide +kernel : ∀ p : Fin 4 × Fin 4, p.1 < p.2 →
        ldlLower .f₄ p.1 p.2 = 0) (i, j) hij
    | g₂ =>
      exact fun i j hij ↦ (by decide +kernel : ∀ p : Fin 2 × Fin 2, p.1 < p.2 →
        ldlLower .g₂ p.1 p.2 = 0) (i, j) hij
  have hL1 : ∀ i, ldlLower t i i = 1 := by
    cases t with
    | a _ _ | b _ _ | c _ _ | d _ _ => exact ht.elim
    | e₆ | e₇ | e₈ | f₄ | g₂ => decide +kernel
  have hq : ∀ i, 0 < ldlPivots t i := by
    cases t with
    | a _ _ | b _ _ | c _ _ | d _ _ => exact ht.elim
    | e₆ | e₇ | e₈ | f₄ | g₂ => decide +kernel
  have hH := ldl_eq t ht
  refine ⟨hL, hL1, hq, hH, fun x ↦ ?_, posDef_of_ldl _ _ _ hL hL1 hq hH⟩
  rw [hH, dotProduct_ldl_mulVec]

end RootSetModel
