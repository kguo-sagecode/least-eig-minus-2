/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LeafDeterminant
import LineGraphs.Cartan.Models
import Mathlib.Tactic.IntervalCases

/-!
# The leading principal determinants of the model matrices

`comp:rem-minors` of the blueprint for Remark 3.11 of [CGSS]: the table `eq:minors` of the
leading `k × k` principal determinants `Δₖ` of the named Cartan matrices, with `Δ₀ = 1`.
The classical families follow from the leaf expansion `Matrix.det_eq_of_leaf` at the last
vertex (`rmdpath`, `rmdA`, `rmdBC`, `rmdD`). The E values from `k = 3` on are Mathlib's
`CartanMatrix.E_det` (in place of steps `rmdE3`, `rmdE4`, and for `rmdErest`); those at
`k = 0, 1, 2` and the F₄ and G₂ prefixes are finite evaluations.
-/

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Reindexing a principal submatrix onto a leading block, for `comp:rem-minors` of
Remark 3.11: an injective map onto the indices below `k` gives the leading `k × k` block. -/
theorem det_submatrix_eq_castLE {ι : Type*} [Fintype ι] [DecidableEq ι] {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) R) (f : ι → Fin N) (hf : Function.Injective f) (hk : k ≤ N)
    (hrange : ∀ i : Fin N, (∃ x, f x = i) ↔ i.val < k) :
    (M.submatrix f f).det = (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  have hg (j : Fin k) : ∃ x, f x = Fin.castLE hk j := (hrange _).mpr j.2
  let e : Fin k ≃ ι :=
    { toFun := fun j ↦ Classical.choose (hg j)
      invFun := fun x ↦ ⟨(f x).val, (hrange _).mp ⟨x, rfl⟩⟩
      left_inv := fun j ↦ Fin.ext (by simp [Classical.choose_spec (hg j)])
      right_inv := fun x ↦ hf (by
        rw [Classical.choose_spec (hg ⟨(f x).val, (hrange _).mp ⟨x, rfl⟩⟩)]
        rfl) }
  have he (j : Fin k) : f (e j) = Fin.castLE hk j := Classical.choose_spec (hg j)
  rw [← det_submatrix_equiv_self e]
  congr 1
  ext i j
  simp only [submatrix_apply, he]

/-- Step `rmdpath` of Remark 3.11: the leaf expansion at the last vertex of a path
extension, with the two deletions as leading blocks. -/
theorem det_eq_of_last_leaf {k : ℕ} (M : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hv : M (Fin.last (k + 1)) (Fin.last (k + 1)) = 2)
    (hrow : ∀ j : Fin (k + 2), j.val < k → M (Fin.last (k + 1)) j = 0)
    (hcol : ∀ i : Fin (k + 2), i.val < k → M i (Fin.last (k + 1)) = 0) :
    M.det = 2 * (M.submatrix (Fin.castLE (by omega : k + 1 ≤ k + 2))
        (Fin.castLE (by omega : k + 1 ≤ k + 2))).det -
      M (Fin.last (k + 1)) ⟨k, by omega⟩ * M ⟨k, by omega⟩ (Fin.last (k + 1)) *
        (M.submatrix (Fin.castLE (by omega : k ≤ k + 2))
          (Fin.castLE (by omega : k ≤ k + 2))).det := by
  have hvw : Fin.last (k + 1) ≠ ⟨k, by omega⟩ := by simp [Fin.ext_iff]
  rw [M.det_eq_of_leaf hvw hv
    (fun j hj hj' ↦ hrow j (by simp [Fin.ext_iff] at hj hj'; omega))
    (fun i hi hi' ↦ hcol i (by simp [Fin.ext_iff] at hi hi'; omega)),
    det_submatrix_eq_castLE (ι := {i // i ≠ Fin.last (k + 1)}) (k := k + 1) M Subtype.val
      Subtype.val_injective (by omega) (fun i ↦ by
        have := i.isLt
        simp only [Subtype.exists, exists_prop, exists_eq_right]
        simp [Fin.ext_iff]
        omega),
    det_submatrix_eq_castLE (ι := {i // i ≠ Fin.last (k + 1) ∧ i ≠ ⟨k, by omega⟩}) (k := k) M
      Subtype.val Subtype.val_injective (by omega) (fun i ↦ by
        have := i.isLt
        simp only [Subtype.exists, exists_prop, exists_eq_right]
        simp [Fin.ext_iff]
        omega)]

end Matrix

namespace CartanMatrix

open Matrix

/-- The leading blocks of `A N` are the matrices `A k` (step `rmdA`). -/
theorem A_castLE {N k : ℕ} (hk : k ≤ N) :
    (A N).submatrix (Fin.castLE hk) (Fin.castLE hk) = A k := by
  ext i j
  simp only [A, submatrix_apply, of_apply, Fin.ext_iff, Fin.val_castLE]

/-- Step `rmdBC`: the proper leading blocks of `B N` are unit paths. -/
theorem B_castLE_of_lt {N k : ℕ} (hk : k < N) :
    (B N).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le) = A k := by
  ext i j
  have := i.isLt
  have := j.isLt
  simp only [A, B, submatrix_apply, of_apply, Fin.ext_iff, Fin.val_castLE]
  split_ifs <;> omega

/-- Step `rmdBC`: the proper leading blocks of `C N` are unit paths. -/
theorem C_castLE_of_lt {N k : ℕ} (hk : k < N) :
    (C N).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le) = A k := by
  ext i j
  have := i.isLt
  have := j.isLt
  simp only [A, C, submatrix_apply, of_apply, Fin.ext_iff, Fin.val_castLE]
  split_ifs <;> omega

/-- Step `rmdDleaf`: the proper leading blocks of `D N` are unit paths. -/
theorem D_castLE_of_lt {N k : ℕ} (hN : 3 ≤ N) (hk : k < N) :
    (D N).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le) = A k := by
  ext i j
  have := i.isLt
  have := j.isLt
  simp only [A, D, submatrix_apply, of_apply, Fin.ext_iff, Fin.val_castLE]
  split_ifs <;> omega

/-- The leading blocks of `E N` are the matrices `E k` (step `rmdErest`). -/
theorem E_castLE {N k : ℕ} (hk : k ≤ N) :
    (E N).submatrix (Fin.castLE hk) (Fin.castLE hk) = E k := by
  ext i j
  simp only [E, submatrix_apply, of_apply, Fin.ext_iff, Fin.val_castLE]

/-- Step `rmdA` of Remark 3.11: the unit-path determinants are `k + 1`. -/
theorem det_A (k : ℕ) : (A k).det = k + 1 := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => decide
  | more k h₀ h₁ =>
    rw [det_eq_of_last_leaf (A (k + 2)) (by simp [A])
      (fun j hj ↦ by simp [A, Fin.ext_iff]; omega) (fun i hi ↦ by simp [A, Fin.ext_iff]; omega),
      A_castLE, A_castLE, h₀, h₁]
    have h₂ : A (k + 2) (Fin.last (k + 1)) ⟨k, by omega⟩ = -1 := by simp [A, Fin.ext_iff]
    have h₃ : A (k + 2) ⟨k, by omega⟩ (Fin.last (k + 1)) = -1 := by simp [A, Fin.ext_iff]
    rw [h₂, h₃]
    push_cast
    ring

/-- Step `rmdBC` of Remark 3.11: the final B determinant is 2. -/
theorem det_B (k : ℕ) : (B (k + 2)).det = 2 := by
  rw [det_eq_of_last_leaf (B (k + 2)) (by simp [B])
    (fun j hj ↦ by simp only [B, of_apply, Fin.ext_iff, Fin.val_last]; split_ifs <;> omega)
    (fun i hi ↦ by simp only [B, of_apply, Fin.ext_iff, Fin.val_last]; split_ifs <;> omega),
    B_castLE_of_lt (by omega), B_castLE_of_lt (by omega), det_A, det_A]
  have h₂ : B (k + 2) (Fin.last (k + 1)) ⟨k, by omega⟩ = -1 := by simp [B, Fin.ext_iff]
  have h₃ : B (k + 2) ⟨k, by omega⟩ (Fin.last (k + 1)) = -2 := by simp [B, Fin.ext_iff]
  rw [h₂, h₃]
  push_cast
  ring

/-- Step `rmdBC` of Remark 3.11: the final C determinant is 2. -/
theorem det_C (k : ℕ) : (C (k + 2)).det = 2 := by
  rw [det_eq_of_last_leaf (C (k + 2)) (by simp [C])
    (fun j hj ↦ by simp only [C, of_apply, Fin.ext_iff, Fin.val_last]; split_ifs <;> omega)
    (fun i hi ↦ by simp only [C, of_apply, Fin.ext_iff, Fin.val_last]; split_ifs <;> omega),
    C_castLE_of_lt (by omega), C_castLE_of_lt (by omega), det_A, det_A]
  have h₂ : C (k + 2) (Fin.last (k + 1)) ⟨k, by omega⟩ = -2 := by
    simp only [C, of_apply, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  have h₃ : C (k + 2) ⟨k, by omega⟩ (Fin.last (k + 1)) = -1 := by simp [C, Fin.ext_iff]
  rw [h₂, h₃]
  push_cast
  ring

/-- The edge `ℓ - 1`, `ℓ - 3` of `D ℓ` has entry `-1` (step `rmdD`). -/
theorem D_last_entry (k : ℕ) : D (k + 4) (Fin.last (k + 3)) ⟨k + 1, by omega⟩ = -1 := by
  simp only [D, of_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> simp_all

/-- The edge `ℓ - 3`, `ℓ - 1` of `D ℓ` has entry `-1` (step `rmdD`). -/
theorem D_entry_last (k : ℕ) : D (k + 4) ⟨k + 1, by omega⟩ (Fin.last (k + 3)) = -1 := by
  simp only [D, of_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> simp_all

/-- Step `rmdD` of Remark 3.11: deleting the leaf `ℓ - 1` leaves a unit path
(`rmdDleaf`), and deleting also its neighbour `ℓ - 3` leaves a path and an isolated
vertex (`rmdDneighbour`); the final D determinant is 4. -/
theorem det_D (k : ℕ) : (D (k + 4)).det = 4 := by
  have hvw : Fin.last (k + 3) ≠ ⟨k + 1, by omega⟩ := by simp [Fin.ext_iff]
  have hent (i j : Fin (k + 4)) : D (k + 4) i j = if i = j then 2
      else if i.val + 1 = j.val ∧ j.val + 2 < k + 4 then -1
      else if j.val + 1 = i.val ∧ i.val + 2 < k + 4 then -1
      else if i.val + 3 = k + 4 ∧ (j.val + 2 = k + 4 ∨ j.val + 1 = k + 4) then -1
      else if j.val + 3 = k + 4 ∧ (i.val + 2 = k + 4 ∨ i.val + 1 = k + 4) then -1
      else 0 := by
    simp only [D, of_apply]
    rw [ite_eq_right (by omega : ¬k + 4 ≤ 2)]
  rw [(D (k + 4)).det_eq_of_leaf hvw (by simp [D])
    (fun j hj hj' ↦ by
      have := j.isLt
      simp only [ne_eq, Fin.ext_iff, Fin.val_last] at hj hj'
      rw [hent]
      simp only [Fin.ext_iff, Fin.val_last]
      split_ifs <;> omega)
    (fun i hi hi' ↦ by
      have := i.isLt
      simp only [ne_eq, Fin.ext_iff, Fin.val_last] at hi hi'
      rw [hent]
      simp only [Fin.ext_iff, Fin.val_last]
      split_ifs <;> omega),
    det_submatrix_eq_castLE (ι := {i // i ≠ Fin.last (k + 3)}) (k := k + 3) _ Subtype.val
      Subtype.val_injective (by omega) (fun i ↦ by
        have := i.isLt
        simp only [Subtype.exists, exists_prop, exists_eq_right]
        simp [Fin.ext_iff]
        omega),
    D_castLE_of_lt (by omega) (by omega), det_A]
  -- the isolated vertex `ℓ - 2` of the double deletion
  let u : {i : Fin (k + 4) // i ≠ Fin.last (k + 3) ∧ i ≠ ⟨k + 1, by omega⟩} :=
    ⟨⟨k + 2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff]⟩
  rw [det_eq_mul_det_of_row_eq_zero _ u (fun j hj ↦ by
      have h₁ := j.2.1
      have h₂ := j.2.2
      have h₃ : (j : Fin (k + 4)) ≠ ⟨k + 2, by omega⟩ := fun h ↦ hj (Subtype.ext h)
      have := (j : Fin (k + 4)).isLt
      simp only [ne_eq, Fin.ext_iff, Fin.val_last] at h₁ h₂ h₃
      simp only [submatrix_apply, u]
      rw [hent]
      simp only [Fin.ext_iff]
      split_ifs <;> omega),
    submatrix_submatrix,
    det_submatrix_eq_castLE (k := k + 1) _ _ (Subtype.val_injective.comp Subtype.val_injective)
      (by omega) (fun i ↦ by
        have := i.isLt
        constructor
        · rintro ⟨⟨⟨x, hx₁, hx₂⟩, hx₃⟩, rfl⟩
          have h₃ : x ≠ ⟨k + 2, by omega⟩ := fun h ↦ hx₃ (Subtype.ext h)
          have := x.isLt
          simp only [ne_eq, Fin.ext_iff, Fin.val_last] at hx₁ hx₂ h₃
          simp only [Function.comp_apply]
          omega
        · intro hi
          refine ⟨⟨⟨i, ?_, ?_⟩, ?_⟩, rfl⟩
          · simp [Fin.ext_iff]
            omega
          · simp [Fin.ext_iff]
            omega
          · intro h
            have := congrArg (fun x ↦ x.1.val) h
            simp [u] at this
            omega),
    D_castLE_of_lt (by omega) (by omega), det_A]
  have h₄ : (D (k + 4)).submatrix
      (Subtype.val : {i : Fin (k + 4) // i ≠ Fin.last (k + 3) ∧ i ≠ ⟨k + 1, by omega⟩} → _)
      Subtype.val u u = 2 := by
    simp [u, D]
  rw [D_last_entry, D_entry_last, h₄]
  push_cast
  ring

/-- Steps `rmdE1`--`rmdErest` of Remark 3.11: the determinants of the matrices `E k`,
namely 1, 2, 4 for `k = 0, 1, 2` and `9 - k` from `k = 3` on. -/
theorem det_E_leading (k : ℕ) :
    (E k).det = if k = 0 then (1 : ℤ) else if k = 1 then 2 else if k = 2 then 4 else 9 - k := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> decide
  · rw [E_det hk, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The leading principal determinants in the table `eq:minors` of `comp:rem-minors` of
Remark 3.11: entry `k` is the determinant of the leading `k × k` block, with `Δ₀ = 1`. -/
def leadingDet {n : ℕ} : FiniteType n → ℕ → ℤ
  | .a _ _, k => k + 1
  | .b n _, k | .c n _, k => if k < n then k + 1 else 2
  | .d n _, k => if k < n then k + 1 else 4
  | .e₆, k | .e₇, k | .e₈, k =>
    if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 4 else 9 - k
  | .f₄, k => [1, 2, 3, 2, 1].getD k 0
  | .g₂, k => [1, 2, 1].getD k 0

-- Remark 3.11, comp:rem-minors
/-- The leading determinants of `comp:rem-minors` in Remark 3.11 of [CGSS]: for every named
matrix in the list `eq:list`, the leading `k × k` principal determinant is `leadingDet t k`
(`Aₗ`: `k + 1`; `Bₗ`, `Cₗ`: `k + 1` for `k < ℓ` and 2 at `ℓ`; `Dₗ`: `k + 1` for `k < ℓ`
and 4 at `ℓ`; `E`: `2, 4, 6, 5, 4, 3, 2, 1`; `F₄`: `2, 3, 2, 1`; `G₂`: `2, 1`). -/
theorem model_leading_determinants {n : ℕ} (t : FiniteType n) {k : ℕ} (hk : k ≤ n) :
    ((modelEntries t).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = leadingDet t k := by
  cases t with
  | a n _ =>
    change ((A n).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = k + 1
    rw [A_castLE, det_A]
  | b n hn =>
    change ((B n).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      if k < n then (k : ℤ) + 1 else 2
    by_cases hkn : k < n
    · rw [ite_eq_left hkn, B_castLE_of_lt hkn, det_A]
    · obtain rfl : k = n := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      rw [ite_eq_right hkn, Fin.castLE_rfl, submatrix_id_id, det_B]
  | c n hn =>
    change ((C n).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      if k < n then (k : ℤ) + 1 else 2
    by_cases hkn : k < n
    · rw [ite_eq_left hkn, C_castLE_of_lt hkn, det_A]
    · obtain rfl : k = n := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      rw [ite_eq_right hkn, Fin.castLE_rfl, submatrix_id_id, det_C]
  | d n hn =>
    change ((D n).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      if k < n then (k : ℤ) + 1 else 4
    by_cases hkn : k < n
    · rw [ite_eq_left hkn, D_castLE_of_lt (by omega) hkn, det_A]
    · obtain rfl : k = n := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
      rw [ite_eq_right hkn, Fin.castLE_rfl, submatrix_id_id, det_D]
  | e₆ =>
    change ((E 6).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = _
    rw [E_castLE, det_E_leading]
    rfl
  | e₇ =>
    change ((E 7).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = _
    rw [E_castLE, det_E_leading]
    rfl
  | e₈ =>
    change ((E 8).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = _
    rw [E_castLE, det_E_leading]
    rfl
  | f₄ =>
    change ((F₄).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = [1, 2, 3, 2, 1].getD k 0
    interval_cases k <;> decide +revert
  | g₂ =>
    change ((G₂).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = [1, 2, 1].getD k 0
    interval_cases k <;> decide +revert

end CartanMatrix
