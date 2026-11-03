/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Eigenprojections

/-!
# The four projections for a resolved design

Example 5.13 (`ex:5.13`) of [CGSS], steps `s5exvalues`–`s5exspecH`.
Here `J` is all ones, `Q = I + R` is the class Gram matrix, and `G = N'ᵀN'`.
The four projections have ranges the constant vectors, `W₁`, `W₂`, and `W₃`.
-/

open scoped BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Explicit projections for `s5exvalues` and `s5exdims`, Example 5.13 of [CGSS].
The third component projects onto `W₂`, the fourth onto `W₃`. -/
noncomputable def resolutionProjections (k : ℕ) (J Q G : Matrix n n ℝ) :
    Fin 4 → Matrix n n ℝ :=
  let E₀ := (4 * (k : ℝ) ^ 2 - 1)⁻¹ • J
  let E₁ := (2 * (k : ℝ) - 1)⁻¹ • Q - E₀
  let E₂ := (2 * (k : ℝ))⁻¹ • G -
    ((2 * (k : ℝ) + 1) / (2 * (4 * (k : ℝ) ^ 2 - 1))) • J
  ![E₀, E₁, E₂, 1 - E₀ - E₁ - E₂]

/-- The four eigenvalues in `s5exvalues`, Example 5.13 of [CGSS]. -/
def resolutionEigenvalues (k : ℕ) : Fin 4 → ℝ :=
  ![2 * (k : ℝ) * (k - 1), -(k - 1), -k, k]

/-- The four multiplicities in `s5exdims`, Example 5.13 of [CGSS]. -/
def resolutionMultiplicities (k : ℕ) : Fin 4 → ℕ :=
  ![1, 2 * k, (k - 1) * (2 * k + 1), (k - 1) * (2 * k + 1)]

/-- Distinctness in `s5exspecH`, Example 5.13 of [CGSS]. -/
theorem resolutionEigenvalues_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (resolutionEigenvalues k) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  intro i j he
  fin_cases i <;> fin_cases j <;> simp [resolutionEigenvalues] at he ⊢ <;> nlinarith

/-- Projection form of steps `s5exvj`–`s5exv3`, Example 5.13 of [CGSS].
The hypotheses are the products computed from the incidence and class identities. -/
theorem mul_resolutionProjections {k : ℕ} (hk : 2 ≤ k)
    {A J Q G : Matrix n n ℝ}
    (hA : A = J - Q - G + (k : ℝ) • 1)
    (hAJ : A * J = (2 * (k : ℝ) * (k - 1)) • J)
    (hAQ : A * Q = (k - 1 : ℝ) • J - (k - 1 : ℝ) • Q)
    (hAG : A * G = (k : ℝ) ^ 2 • J - (k : ℝ) • G) (i : Fin 4) :
    A * resolutionProjections k J Q G i =
      resolutionEigenvalues k i • resolutionProjections k J Q G i := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : 4 * (k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hq : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have hz : (k : ℝ) ≠ 0 := by linarith
  fin_cases i <;> dsimp [resolutionProjections, resolutionEigenvalues]
  all_goals simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hAJ, hAQ, hAG]
  all_goals try rw [hA]
  all_goals ext a b
  all_goals simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  all_goals field_simp (disch := first | positivity | nlinarith)
  all_goals ring

omit [Fintype n] in
/-- Symmetry of the projections in `s5exdims`, Example 5.13 of [CGSS]. -/
theorem isHermitian_resolutionProjections (k : ℕ) {J Q G : Matrix n n ℝ}
    (hJ : J.IsHermitian) (hQ : Q.IsHermitian) (hG : G.IsHermitian) (i : Fin 4) :
    (resolutionProjections k J Q G i).IsHermitian := by
  have h₀ := hJ.smul (IsSelfAdjoint.all (4 * (k : ℝ) ^ 2 - 1)⁻¹)
  have h₁ := (hQ.smul (IsSelfAdjoint.all (2 * (k : ℝ) - 1)⁻¹)).sub h₀
  have h₂ := (hG.smul (IsSelfAdjoint.all (2 * (k : ℝ))⁻¹)).sub
    (hJ.smul (IsSelfAdjoint.all ((2 * (k : ℝ) + 1) / (2 * (4 * (k : ℝ) ^ 2 - 1)))))
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact ((isHermitian_one.sub h₀).sub h₁).sub h₂

omit [Fintype n] in
/-- The four spaces exhaust the ambient space (`s5exd3p` and `s5exspecH`,
Example 5.13 of [CGSS]). -/
theorem sum_resolutionProjections (k : ℕ) (J Q G : Matrix n n ℝ) :
    ∑ i, resolutionProjections k J Q G i = 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, resolutionProjections,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  abel

/-- The dimensions in `s5exd12` and `s5exd3`, Example 5.13 of [CGSS],
computed as traces of the four orthogonal projections. -/
theorem trace_resolutionProjections {k : ℕ} (hk : 2 ≤ k)
    {J Q G : Matrix n n ℝ} (hn : Fintype.card n = 4 * k ^ 2 - 1)
    (hJ : J.trace = 4 * (k : ℝ) ^ 2 - 1)
    (hQ : Q.trace = 4 * (k : ℝ) ^ 2 - 1)
    (hG : G.trace = (k : ℝ) * (4 * k ^ 2 - 1)) (i : Fin 4) :
    (resolutionProjections k J Q G i).trace = (resolutionMultiplicities k i : ℝ) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : 4 * (k : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hq : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
  have hz : (k : ℝ) ≠ 0 := by linarith
  have hn1 : 1 ≤ 4 * k ^ 2 := by nlinarith
  fin_cases i <;> dsimp [resolutionProjections, resolutionMultiplicities]
  all_goals simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hJ, hQ, hG, hn,
    Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub hn1, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, smul_eq_mul]
  all_goals field_simp (disch := first | positivity | nlinarith)
  all_goals ring

end Matrix
