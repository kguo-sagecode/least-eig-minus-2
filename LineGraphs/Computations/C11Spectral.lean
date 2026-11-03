import LineGraphs.Computations.C11
import LineGraphs.Spectral.HoffmanPolynomial

/-!
# Computation C11: the cubic identity for [CGSS], Theorem 5.8

The scalar certificate is applied to the graph's nonprincipal spectral support. The diagonal
parity is proved directly, pairing the two orientations of each triangle.
-/

open scoped BigOperators Matrix
open Matrix Polynomial

namespace Computations.C11

/-- C11, [CGSS] Theorem 5.8, `s558nbhp`: the actual adjacency matrix identity. -/
theorem matrix_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (s t : ℝ) (hs : 2 ≤ s)
    (hk : G.IsRegularOfDegree k) (hc : G.Connected)
    (hdeg : (k : ℝ) = (s + 1) * t) (hn : (Fintype.card V : ℝ) = s * (s + 2))
    (hsp : ∀ μ ∈ G.spectrumMultiset, μ ≠ (k : ℝ) →
      μ = -t ∨ μ ^ 2 = t * (s + 1) * (s - t) / (s - 1)) :
    (G.adjMatrix ℝ + t • 1) *
        ((G.adjMatrix ℝ) ^ 2 - (t * (s + 1) * (s - t) / (s - 1)) • 1) =
      (t ^ 2 * (s + 1) * (s * t - 1) / (s - 1)) • of (fun _ _ ↦ (1 : ℝ)) := by
  let c := t * (s + 1) * (s - t) / (s - 1)
  let p : ℝ[X] := (X + C t) * (X ^ 2 - C c)
  have he := hk.aeval_eq_smul_allOnes_of_connected hc p (fun μ hμ hne ↦ ?_)
  · have hn0 : s * (s + 2) ≠ 0 := by positivity
    have hv : p.eval (k : ℝ) / (Fintype.card V : ℝ) = t ^ 2 * (s + 1) * (s * t - 1) / (s - 1) := by
      simp only [p, eval_mul, eval_add, eval_X, eval_C, eval_sub, eval_pow, hdeg, hn]
      rw [hoffman_value s t (by linarith), mul_div_cancel_left₀ _ hn0]
    rw [hv] at he
    simpa [p, c, Algebra.algebraMap_eq_smul_one] using he
  · rcases hsp μ hμ hne with h | h <;> simp [p, c, h]

/-- C11, [CGSS] Theorem 5.8, `s558nbeven`: each cubic diagonal is even. -/
theorem even_cube_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (hd : ∀ i, A i i = 0) (u : Fin n) : Even ((A ^ 3) u u) := by
  let f := fun i j ↦ A u i * A i j * A j u
  have hf (i j : Fin n) : f i j = f j i := by
    dsimp [f]
    rw [hs.apply i j, hs.apply u i, hs.apply u j]
    ring
  have hdiag (i : Fin n) : f i i = 0 := by simp [f, hd]
  have hsplit (i j : Fin n) :
      f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hdiag]
    · simp [h, not_lt_of_gt h]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
  refine ⟨∑ i, ∑ j, if i < j then f i j else 0, ?_⟩
  have hcube : (A ^ 3) u u = ∑ i, ∑ j, f i j := by
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hcube]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
  simp_rw [Finset.sum_add_distrib]
  rw [hswap]

/-- C11, [CGSS] Theorem 5.8: the cubic identity gives `t³(s+1)` even. -/
theorem even_parameter_cube {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.IsSymm) (hd : ∀ i, A i i = 0) (s t : ℤ) (u : Fin n)
    (hdiag : (A ^ 3) u u = t ^ 3 * (s + 1)) : Even (t ^ 3 * (s + 1)) := by
  rw [← hdiag]
  exact even_cube_diagonal A hs hd u

end Computations.C11
