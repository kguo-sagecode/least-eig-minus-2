import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Computation C12 for [CGSS], Corollary 5.9

The bordering construction, with the literal constant diagonal `-1` of the blueprint.
-/

open scoped BigOperators Matrix

namespace Computations.C12

-- Corollary 5.9 (step s559st, C12)
/-- C12, [CGSS] Corollary 5.9, `s559st`: the parameters when every block is full.
The integer parameters and their bounds come from case (iii) of Theorem 5.8; `hc` is its
definition of the squared nonprincipal eigenvalue. Fractions are evaluated over `ℚ`. -/
theorem full_block_parameters (s t : ℤ) (c : ℚ) (hs : 2 ≤ s) (ht : 1 ≤ t)
    (h : (s : ℚ) * (s + 1) / 2 = s * t)
    (hc : c = t * (s + 1) * (s - t) / (s - 1)) :
    s = 2 * t - 1 ∧ (s : ℚ) * (s + 1) / 2 = 2 * (t : ℚ) ^ 2 - t ∧
      ((s : ℚ) + 1) * (s + 2) / 2 = 2 * (t : ℚ) ^ 2 + t ∧
      (s : ℚ) * (s + 2) = 4 * (t : ℚ) ^ 2 - 1 ∧ 2 ≤ t ∧ c = (t : ℚ) ^ 2 := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have he : (s : ℚ) + 1 = 2 * t := by
    apply mul_left_cancel₀ hsQ
    linarith
  have hstQ : (s : ℚ) = 2 * t - 1 := by linarith
  have hst : s = 2 * t - 1 := by exact_mod_cast hstQ
  have ht2 : 2 ≤ t := by
    rcases lt_or_eq_of_le ht with ht' | ht' <;> omega
  refine ⟨hst, ?_, ?_, ?_, ht2, ?_⟩
  · rw [hstQ]
    ring
  · rw [hstQ]
    ring
  · rw [hstQ]
    ring
  · rw [hc, hstQ]
    have hden : 2 * (t : ℚ) - 1 - 1 ≠ 0 := by
      have htQ : (2 : ℚ) ≤ t := by exact_mod_cast ht2
      linarith
    apply (div_eq_iff hden).2
    ring

/-- C12, [CGSS] Corollary 5.9: the matrix `2A - J`. -/
def core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ 2 * A i j - 1

/-- C12, [CGSS] Corollary 5.9: border a core by a row and column of `-1`. -/
def border {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ
  | some i, some j => S i j
  | _, _ => -1

/-- C12, [CGSS] Corollary 5.9, `s559S`: the core has row sum one. -/
theorem core_row_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hn : (n : ℝ) + 1 = 4 * t ^ 2) (hr : ∀ i, ∑ j, A i j = 2 * t ^ 2) (i : Fin n) :
    ∑ j, core A i j = 1 := by
  simp only [core, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

/-- C12, [CGSS] Corollary 5.9, `s559S`: the square of the core. -/
theorem core_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hn : (n : ℝ) + 1 = 4 * t ^ 2) (hs : A.IsSymm)
    (hr : ∀ i, ∑ j, A i j = 2 * t ^ 2)
    (hq : A * A = t ^ 2 • (1 + Matrix.of (fun _ _ ↦ (1 : ℝ)))) :
    core A * core A = (4 * t ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  have hc (j : Fin n) : ∑ i, A i j = 2 * t ^ 2 := by
    simpa only [hs.apply] using hr j
  ext i j
  have hentry := congrFun (congrFun hq i) j
  change (∑ k, A i k * A k j) = t ^ 2 * ((1 : Matrix _ _ ℝ) i j + 1) at hentry
  change (∑ k, (2 * A i k - 1) * (2 * A k j - 1)) =
    4 * t ^ 2 * (1 : Matrix _ _ ℝ) i j - 1
  calc
    _ = 4 * (∑ k, A i k * A k j) - 2 * (∑ k, A i k) -
        2 * (∑ k, A k j) + n := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      have he : (n : ℝ) = ∑ _ : Fin n, (1 : ℝ) := by simp
      rw [he, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hentry, hr, hc]; nlinarith

/-- C12, [CGSS] Corollary 5.9, `s559H`: the symmetric border is Hadamard. -/
theorem border_isHadamard {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hs : S.IsSymm) (he : ∀ i j, S i j = 1 ∨ S i j = -1)
    (hr : ∀ i, ∑ j, S i j = 1)
    (hq : S * S = ((n : ℝ) + 1) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      Matrix.of (fun _ _ ↦ (1 : ℝ))) :
    (border S).IsSymm ∧ (border S).IsHadamard := by
  have hb : (border S).IsSymm := by
    ext (_ | i) (_ | j) <;> simp [Matrix.transpose_apply, border, hs.apply]
  have hc (j : Fin n) : ∑ i, S i j = 1 := by simpa only [hs.apply] using hr j
  have hmul : border S * border S =
      (Fintype.card (Option (Fin n)) : ℝ) • (1 : Matrix _ _ ℝ) := by
    ext (_ | i) (_ | j)
    · simp [Matrix.mul_apply, border]
    · simp [Matrix.mul_apply, border, Fintype.sum_option, hc]
    · simp [Matrix.mul_apply, border, Fintype.sum_option, hr]
    · have hij := congrFun (congrFun hq i) j
      simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.of_apply, Matrix.one_apply] at hij
      simpa [Matrix.mul_apply, border, Fintype.sum_option, Matrix.one_apply] using
        (show 1 + ∑ k, S i k * S k j = ((n : ℝ) + 1) * (if i = j then 1 else 0) by
          linarith)
  have hconj : (border S).conjTranspose = border S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hb.eq
  refine ⟨hb, ?_⟩
  constructor
  · intro i j
    have hem : border S i j = 1 ∨ border S i j = -1 := by
      cases i with
      | none => simp [border]
      | some i =>
        cases j with
        | none => simp [border]
        | some j => exact he i j
    rcases hem with h | h <;> simp [h, unitary, Submonoid.mem_mk]
  · rwa [hconj]
  · rwa [hconj]

/-- C12, [CGSS] Corollary 5.9, `s559H`: the complete construction and constant diagonal. -/
theorem hadamard_border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hn : (n : ℝ) + 1 = 4 * t ^ 2) (hs : A.IsSymm)
    (he : ∀ i j, A i j = 0 ∨ A i j = 1) (hd : ∀ i, A i i = 0)
    (hr : ∀ i, ∑ j, A i j = 2 * t ^ 2)
    (hq : A * A = t ^ 2 • (1 + Matrix.of (fun _ _ ↦ (1 : ℝ)))) :
    (border (core A)).IsSymm ∧ (border (core A)).IsHadamard ∧
      (∀ i, border (core A) i i = -1) ∧
      (Fintype.card (Option (Fin n)) : ℝ) = 4 * t ^ 2 := by
  have hs' : (core A).IsSymm := by
    ext i j
    simp [Matrix.transpose_apply, core, hs.apply]
  obtain ⟨hsym, hhad⟩ := border_isHadamard (core A) hs'
    (fun i j ↦ by rcases he i j with h | h <;> norm_num [core, h])
    (core_row_sum A t hn hr) (by simpa only [hn] using core_mul A t hn hs hr hq)
  refine ⟨hsym, hhad, ?_, ?_⟩
  · rintro (_ | i) <;> simp [border, core, hd]
  · simpa using hn

end Computations.C12
