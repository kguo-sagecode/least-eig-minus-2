import LineGraphs.Computations.C11Spectral

/-! # C11: the cubic diagonal in [CGSS], Theorem 5.8, `s558nbdiag`. -/

open Matrix

namespace Computations.C11

/-- C11, [CGSS] Theorem 5.8: extract the cubic diagonal from the matrix identity. -/
theorem cube_diagonal_eq {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (s t : ℝ) (hs : s ≠ 1) (u : V)
    (hd : A u u = 0) (hdeg : (A ^ 2) u u = (s + 1) * t)
    (hp : (A + t • 1) *
        (A ^ 2 - (t * (s + 1) * (s - t) / (s - 1)) • 1) =
      (t ^ 2 * (s + 1) * (s * t - 1) / (s - 1)) • of (fun _ _ ↦ (1 : ℝ))) :
    (A ^ 3) u u = t ^ 3 * (s + 1) := by
  have he : (A + t • 1) *
        (A ^ 2 - (t * (s + 1) * (s - t) / (s - 1)) • 1) =
      A ^ 3 + t • A ^ 2 - (t * (s + 1) * (s - t) / (s - 1)) • A -
        (t * (s + 1) * (s - t) / (s - 1) * t) • 1 := by
    simp only [add_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul,
      smul_smul]
    rw [show A * A ^ 2 = A ^ 3 by noncomm_ring]
    abel
  rw [he] at hp
  have hu := congrFun (congrFun hp u) u
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply_eq,
    of_apply, hd, hdeg, mul_zero, mul_one, sub_zero] at hu
  have hc := triangle_diagonal s t hs
  nlinarith [hu, hc]

/-- C11, [CGSS] Theorem 5.8: the first three moments of the proposed spectrum. -/
theorem spectral_moments (s t : ℝ) (hs : s ≠ 1) :
    ((s + 1) * t) - (s + 1) * t = 0 ∧
    ((s + 1) * t) ^ 2 + (s + 1) * t ^ 2 +
        (s - 1) * (s + 2) * (t * (s + 1) * (s - t) / (s - 1)) =
      s * (s + 2) * ((s + 1) * t) ∧
    ((s + 1) * t) ^ 3 - (s + 1) * t ^ 3 = s * (s + 2) * t ^ 3 * (s + 1) := by
  refine ⟨by ring, ?_, by ring⟩
  field_simp
  ring

end Computations.C11
