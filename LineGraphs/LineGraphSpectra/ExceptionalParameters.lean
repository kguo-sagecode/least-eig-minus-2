/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignSpectrum
import LineGraphs.Computations.C11Spectrum
import LineGraphs.Computations.C11Diagonal

/-!
# Parameters of the nonbipartite alternative

Theorem 5.8 of [CGSS], steps `s558nbhand` through `s558nbeven`.
The positive integer parameters are represented by natural numbers. Point and block
counts are doubled to avoid division; the pair equation and divisibility are over ℤ.
-/

open Matrix SimpleGraph

namespace Design

/-- The parameter conclusions in case (iii) of `thm:5.8`, Theorem 5.8 of [CGSS].
The bound `2 * t ≤ s + 1` is Error 4's corrected inequality. -/
structure NonbipartiteParameters (v k b r lam s t : ℕ) : Prop where
  two_le_s : 2 ≤ s
  t_pos : 0 < t
  point_count : 2 * v = s * (s + 1)
  block_size : k = s * t
  block_count : 2 * b = (s + 1) * (s + 2)
  replication : r = (s + 2) * t
  pair_count : (lam : ℤ) * (s - 1) = 2 * t * (s * t - 1)
  bound : 2 * t ≤ s + 1
  dvd : ((s : ℤ) - 1) ∣ 2 * t * (t - 1)

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ} (D : Design P B v k b r lam)

include D

/-- Steps `s558nbv`–`s558nbineq`, Theorem 5.8 of [CGSS], assembled from C11. -/
theorem exists_nonbipartite_parameters (hkr : k < r) (heven : Even (r + k))
    (hhand : (r + k) * (v + b - 1) = 4 * v * r) :
    ∃ s t : ℕ, NonbipartiteParameters v k b r lam s t := by
  have hv := D.one_lt_v
  have hk := D.one_lt_k
  have hbk : (b : ℤ) * k = v * r := by exact_mod_cast D.b_mul_k_eq_v_mul_r
  have hh : ((r : ℤ) + k) * (v + b - 1) = 4 * v * r := by
    have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) hhand
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ v + b),
      Nat.cast_one, Nat.cast_ofNat] using hh
  have hpar := Computations.C11.parameter_equation v k b r hbk hh
  obtain ⟨t, ht, hrt⟩ := Computations.C11.exists_positive_half_difference r k
    (by exact_mod_cast hkr) (by exact_mod_cast heven)
  lift t to ℕ using (by omega : 0 ≤ t)
  have hvt := Computations.C11.two_mul_sq_mul_points v k r t hrt hpar
  have hbvt := Computations.C11.mul_blocks_sub_points v k b r t (by omega) hrt hbk hvt
  obtain ⟨s, hks⟩ := Computations.C11.dvd_block_size b v k t hbvt
  have hst : (k : ℤ) = s * t := by nlinarith [hks]
  have hspos : 0 < s := by
    have hkpos : (0 : ℤ) < k := by omega
    by_contra hs
    have : s * (t : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    omega
  lift s to ℕ using (le_of_lt hspos)
  obtain ⟨hvs, hbs, hrs⟩ := Computations.C11.parameters v k b r s t
    (by omega) (by omega) hst hrt hvt hbk
  have hs := Computations.C11.two_le_parameter v s (by omega) hspos hvs
  have hl : (r : ℤ) * (k - 1) = (lam : ℤ) * (v - 1) := by
    have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) D.r_mul_k_sub_one_eq
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 1 ≤ v), Nat.cast_one] using hh
  have hlst := Computations.C11.lambda_equation v k r s t lam hs hvs hst hrs hl
  have hbound := Computations.C11.two_mul_sub_one_le v k s t hspos hvs hst
    (by exact_mod_cast D.k_le_v)
  exact ⟨s, t, ⟨by omega, by omega, by exact_mod_cast hvs, by exact_mod_cast hst,
    by exact_mod_cast hbs, by exact_mod_cast hrs, hlst, by omega,
    Computations.C11.parameter_dvd s t lam hlst⟩⟩

omit D

namespace NonbipartiteParameters

variable {v k b r lam s t : ℕ} (h : NonbipartiteParameters v k b r lam s t)

include h

/-- Step `s558nbc`, Theorem 5.8 of [CGSS]: cast the pair equation into the spectral field. -/
theorem pair_count_real : (lam : ℝ) * (s - 1) = 2 * t * (s * t - 1) := by
  exact_mod_cast h.pair_count

/-- Step `s558nbY`, Theorem 5.8 of [CGSS]: the rival root's order. -/
theorem root_order : v + b - 1 = s * (s + 2) := by
  have : v + b = s * (s + 2) + 1 := by nlinarith [h.point_count, h.block_count]
  omega

/-- Step `s558nbY`, Theorem 5.8 of [CGSS]: the rival root's degree. -/
theorem root_degree {κ : ℕ} (hκ : 2 * κ = r + k) : κ = (s + 1) * t := by
  rw [h.replication, h.block_size] at hκ
  nlinarith

end NonbipartiteParameters

end Design

namespace SimpleGraph

/-- Steps `s558nbhp`–`s558nbeven`, Theorem 5.8 of [CGSS]: the real Hoffman identity
is cast back to the integer adjacency cube before C11's parity lemmas are applied. -/
theorem even_mul_of_nonbipartite_design_spectrum {W : Type*} [Fintype W] [DecidableEq W]
    (Y : SimpleGraph W) [DecidableRel Y.Adj] {s t : ℕ} (hs : 2 ≤ s)
    (hc : Y.Connected) (hr : Y.IsRegularOfDegree ((s + 1) * t))
    (hn : Fintype.card W = s * (s + 2))
    (hsp : ∀ μ ∈ Y.spectrumMultiset, μ ≠ (((s + 1) * t : ℕ) : ℝ) →
      μ = -(t : ℝ) ∨ μ ^ 2 = t * (s + 1) * ((s : ℝ) - t) / (s - 1)) :
    Even (t * (s + 1)) := by
  classical
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hpoly := Computations.C11.matrix_identity Y s t hsR hr hc
    (by push_cast; rfl) (by exact_mod_cast hn) hsp
  have hcube (u : W) : ((Y.adjMatrix ℝ) ^ 3) u u = (t : ℝ) ^ 3 * (s + 1) := by
    apply Computations.C11.cube_diagonal_eq (Y.adjMatrix ℝ) s t (by linarith) u
      (by simp) ?_ hpoly
    rw [pow_two, Y.adjMatrix_mul_self_apply_self, hr u]
    push_cast
    rfl
  -- C11's integer checker uses Fin indices; reindexing preserves matrix products.
  let e := (Fintype.equivFin W).symm
  let A : Matrix (Fin (Fintype.card W)) (Fin (Fintype.card W)) ℤ :=
    (Y.adjMatrix ℤ).submatrix e e
  have hA : A.IsSymm := by
    simp [A, Matrix.IsSymm, Matrix.transpose_submatrix]
  have hdiag (i) : A i i = 0 := by simp [A]
  have hpow : A ^ 3 = ((Y.adjMatrix ℤ) ^ 3).submatrix e e := by
    simp only [A, pow_succ, pow_zero, one_mul, Matrix.submatrix_mul_equiv]
  have hcast : (Y.adjMatrix ℤ).map (Int.castRingHom ℝ) = Y.adjMatrix ℝ := by
    ext i j
    simp [SimpleGraph.adjMatrix, Matrix.map_apply]
  have hcastpow : ((Y.adjMatrix ℤ) ^ 3).map (Int.castRingHom ℝ) =
      (Y.adjMatrix ℝ) ^ 3 := by rw [Matrix.map_pow, hcast]
  have : Nonempty W := hc.nonempty
  let i : Fin (Fintype.card W) := Fintype.equivFin W (Classical.arbitrary W)
  have hcubeZ : (A ^ 3) i i = (t : ℤ) ^ 3 * (s + 1) := by
    have hh := congrArg (fun M : Matrix W W ℝ ↦ M (e i) (e i)) hcastpow
    rw [hcube] at hh
    rw [hpow]
    simp only [Matrix.map_apply, Matrix.submatrix_apply] at hh ⊢
    change (((Y.adjMatrix ℤ) ^ 3) (e i) (e i) : ℝ) = (t : ℝ) ^ 3 * (s + 1) at hh
    exact_mod_cast hh
  have he := Computations.C11.even_parameter_cube A hA hdiag s t i hcubeZ
  have hh := Computations.C11.even_mul_of_even_cube s t he
  exact_mod_cast hh

end SimpleGraph
