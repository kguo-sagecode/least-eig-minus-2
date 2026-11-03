/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.SmallOrders
import LineGraphs.Hadamard.FixedRow
import LineGraphs.LineSystem.Frame

/-!
# Normalized Hadamard products

The roots `√(2/n) p` in blueprint Lemma `lem:6-lines` for [CGSS], Section 6.
The scaling identities also apply to the order-12 example of computation C16.
-/

open scoped BigOperators RealInnerProductSpace

namespace Matrix

/-- The normalized root of blueprint Lemma `lem:6-lines`, of squared norm two. -/
noncomputable def hadamardRoot {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (p : HadamardPair n) : EuclideanSpace ℝ (Fin n) :=
  Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct p.1.1 p.1.2

/-- Scaling of inner products, step `s6ltwo` of blueprint Lemma `lem:6-lines`. -/
theorem inner_hadamardRoot {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (p q : HadamardPair n) :
    ⟪H.hadamardRoot p, H.hadamardRoot q⟫ =
      (2 / (n : ℝ)) * ⟪H.hadamardRowProduct p.1.1 p.1.2,
        H.hadamardRowProduct q.1.1 q.1.2⟫ := by
  rw [hadamardRoot, hadamardRoot, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, Real.mul_self_sqrt (by positivity)]

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Blueprint Lemma `lem:6-lines`, part 2: each root has squared norm two. -/
theorem inner_hadamardRoot_self (hn : 0 < n) (p : HadamardPair n) :
    ⟪H.hadamardRoot p, H.hadamardRoot p⟫ = 2 := by
  rw [inner_hadamardRoot, hH.inner_hadamardPairs_self]
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

/-- Blueprint Lemma `lem:6-lines`, part 6: every coordinate has the prescribed magnitude. -/
theorem hadamardRoot_apply_mem (p : HadamardPair n) (c : Fin n) :
    H.hadamardRoot p c = Real.sqrt (2 / (n : ℝ)) ∨
      H.hadamardRoot p c = -Real.sqrt (2 / (n : ℝ)) := by
  have hp := hH.hadamardPairs_apply_mem p c
  change Real.sqrt (2 / (n : ℝ)) * H.hadamardPairs p c = _ ∨
    Real.sqrt (2 / (n : ℝ)) * H.hadamardPairs p c = _
  rcases hp with hp | hp <;> simp [hp]

/-- Blueprint Lemma `lem:6-lines`, part 6: the roots lie in `jᗮ`. -/
theorem inner_hadamardRoot_one (p : HadamardPair n) :
    ⟪H.hadamardRoot p, WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ))⟫ = 0 := by
  rw [hadamardRoot, real_inner_smul_left,
    hH.inner_hadamardPairs_one p.1.1 p.1.2 p.2.ne, mul_zero]

omit hH in
/-- Arithmetic in step `s6lone`: the parameter `d` is two. -/
theorem div_half_eq_two (_hH : H.IsHadamard) (hn : 16 ∣ n) (hn16 : 16 ≤ n) :
    (n : ℝ) / (n / 2 : ℕ) = 2 := by
  have hh := Nat.div_mul_cancel (dvd_trans (by decide : 2 ∣ 16) hn)
  have hh' : ((n / 2 : ℕ) : ℝ) * 2 = n := by exact_mod_cast hh
  have hx : ((n / 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n / 2 ≠ 0 by omega)
  exact (div_eq_iff hx).mpr (by linarith)

omit hH in
/-- Blueprint Lemma `lem:6-lines`, part 2: off-diagonal root products are entries of `C_H`. -/
theorem inner_hadamardRoot_eq_signedAdj (_hH : H.IsHadamard) (hn : 16 ∣ n) (hn16 : 16 ≤ n)
    (p q : HadamardPair n) (hpq : p ≠ q) :
    ⟪H.hadamardRoot p, H.hadamardRoot q⟫ = H.hadamardSignedAdj (n / 2) p q := by
  have hh := Nat.div_mul_cancel (dvd_trans (by decide : 2 ∣ 16) hn)
  have hh' : ((n / 2 : ℕ) : ℝ) * 2 = n := by exact_mod_cast hh
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hx : ((n / 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n / 2 ≠ 0 by omega)
  have hs : 2 / (n : ℝ) = ((n / 2 : ℕ) : ℝ)⁻¹ := by
    field_simp
    linarith
  rw [inner_hadamardRoot, hs]
  simp only [hadamardSignedAdj, smul_apply, sub_apply, one_apply_ne hpq, smul_eq_mul,
    mul_zero, sub_zero, hadamardPairs_gram_apply]

/-- The allowed off-diagonal inner products in blueprint Lemma `lem:6-lines`. -/
theorem inner_hadamardRoot_mem (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)
    (p q : HadamardPair n) (hpq : p ≠ q) :
    ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ∈ ({0, 1, -1} : Set ℝ) := by
  rw [hH.inner_hadamardRoot_eq_signedAdj hn hn16 p q hpq]
  exact (hH.fourRowAgreement_half hn ha).hadamardSignedAdj_mem hH (by omega) p q

end IsHadamard
end Matrix
