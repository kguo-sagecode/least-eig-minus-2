/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Positivity
import LineGraphs.Cartan.Rayleigh

/-!
# Symmetrization of finite Cartan matrices

The symmetrization lemma of the Remark 3.11 blueprint. The integer symmetrizer is
transported to the reals using Lemma (integer positivity), `lem:integer-positive`, and an
invertible diagonal congruence gives
a positive definite symmetric matrix with diagonal 2.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal similarity `D^(1/2) M D^(-1/2)`, with an integer symmetrizer `d`. -/
noncomputable def cartanSymmetrization (M : Matrix ι ι ℤ) (d : ι → ℤ) : Matrix ι ι ℝ :=
  diagonal (fun i => Real.sqrt (d i : ℝ)) * M.map (Int.castRingHom ℝ) *
    diagonal (fun i => (Real.sqrt (d i : ℝ))⁻¹)

/-- The entry formula for diagonal Cartan symmetrization. -/
theorem cartanSymmetrization_apply (M : Matrix ι ι ℤ) (d : ι → ℤ) (i j : ι) :
    cartanSymmetrization M d i j =
      Real.sqrt (d i : ℝ) * (M i j : ℝ) * (Real.sqrt (d j : ℝ))⁻¹ := by
  simp [cartanSymmetrization, mul_diagonal, diagonal_mul]

/-- The symmetrization is positive definite by an invertible diagonal congruence. -/
theorem posDef_cartanSymmetrization {M : Matrix ι ι ℤ} {d : ι → ℤ}
    (hd : ∀ i, 0 < d i) (hH : (diagonal d * M).PosDef) :
    (cartanSymmetrization M d).PosDef := by
  have hdR (i : ι) : (0 : ℝ) < d i := by exact_mod_cast hd i
  have hs (i : ι) : Real.sqrt (d i : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (hdR i)).ne'
  let T : Matrix ι ι ℝ := diagonal (fun i => (Real.sqrt (d i : ℝ))⁻¹)
  have hT : Function.Injective T.mulVec := by
    intro x y hxy
    funext i
    have h := congr_fun hxy i
    simp only [T, mulVec_diagonal] at h
    exact mul_left_cancel₀ (inv_ne_zero (hs i)) h
  have hp := (posDef_real_of_posDef_int hH).conjTranspose_mul_mul_same hT
  convert hp using 1
  ext i j
  simp only [cartanSymmetrization_apply, T, diagonal_conjTranspose, star_trivial,
    mul_diagonal, diagonal_mul, map_apply, Int.coe_castRingHom, Int.cast_mul]
  field_simp [hs]
  rw [Real.sq_sqrt (hdR i).le]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The two-coordinate test in the symmetrization proof: a positive definite real
matrix with diagonal 2 has off-diagonal entry squares strictly below 4. -/
theorem PosDef.apply_sq_lt_four [Finite ι] {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (hdiag : ∀ i, S i i = 2) {i j : ι} (hij : i ≠ j) : S i j ^ 2 < 4 := by
  classical
  let := Fintype.ofFinite ι
  let x : ι → ℝ := Pi.single i 1 - Pi.single j (S i j / 2)
  have hx : x ≠ 0 := by
    intro h
    have hi := congr_fun h i
    simp [x, hij] at hi
  have hp := hS.dotProduct_mulVec_pos hx
  have hsym : S j i = S i j := (isHermitian_iff_isSymm.mp hS.isHermitian).apply i j
  simp only [star_trivial, x, mulVec_sub, sub_dotProduct, dotProduct_sub,
    mulVec_single, single_dotProduct, Pi.smul_apply, op_smul_eq_mul,
    col_apply, hdiag, hsym] at hp
  nlinarith

namespace IsFiniteCartan

variable {M : Matrix ι ι ℤ}

/-- The canonical weights of a Cartan matrix: the square roots of opposite-entry products. -/
noncomputable def weightedGraph (_hM : M.IsFiniteCartan) : WeightedGraph ι where
  weights i j := if i = j then 0 else Real.sqrt ((M i j * M j i : ℤ) : ℝ)
  symmetric := by
    apply IsSymm.ext
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij, mul_comm]
  nonneg i j := by split_ifs <;> positivity
  diag i := by simp

/-- A Cartan symmetrization has diagonal 2. -/
theorem cartanSymmetrization_diag (hM : M.IsFiniteCartan) {d : ι → ℤ}
    (hd : ∀ i, 0 < d i) (i : ι) : cartanSymmetrization M d i i = 2 := by
  have hs : Real.sqrt (d i : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast hd i
  rw [cartanSymmetrization_apply, hM.diag i]
  push_cast
  field_simp

/-- The square of an off-diagonal symmetrized entry is the integer opposite-entry product. -/
theorem cartanSymmetrization_sq (_hM : M.IsFiniteCartan) {d : ι → ℤ}
    (hd : ∀ i, 0 < d i) (hH : (diagonal d * M).PosDef) (i j : ι) :
    cartanSymmetrization M d i j ^ 2 = ((M i j * M j i : ℤ) : ℝ) := by
  have hs (i : ι) : Real.sqrt (d i : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast hd i
  have hsym := (isHermitian_iff_isSymm.mp (posDef_cartanSymmetrization hd hH).isHermitian)
  calc
    cartanSymmetrization M d i j ^ 2 =
        cartanSymmetrization M d i j * cartanSymmetrization M d j i := by
      rw [hsym.apply i j, pow_two]
    _ = ((M i j * M j i : ℤ) : ℝ) := by
      simp only [cartanSymmetrization_apply, Int.cast_mul]
      field_simp [hs]

/- The following bounds do not require indecomposability. -/

/-- The opposite off-diagonal entries of a finite Cartan matrix have product 0, 1, 2, or 3. -/
theorem edge_product_mem (hM : M.IsFiniteCartan) {i j : ι} (hij : i ≠ j) :
    M i j * M j i = 0 ∨ M i j * M j i = 1 ∨
      M i j * M j i = 2 ∨ M i j * M j i = 3 := by
  obtain ⟨d, hd, hH⟩ := hM.exists_posDef
  have hlt := (posDef_cartanSymmetrization hd hH).apply_sq_lt_four
    (hM.cartanSymmetrization_diag hd) hij
  rw [hM.cartanSymmetrization_sq hd hH] at hlt
  have hzlt : M i j * M j i < 4 := by exact_mod_cast hlt
  have hzge : 0 ≤ M i j * M j i :=
    mul_nonneg_of_nonpos_of_nonpos (hM.offDiag_nonpos i j hij)
      (hM.offDiag_nonpos j i hij.symm)
  omega

/-- The canonical weighted support is exactly the off-diagonal nonzero matrix support. -/
theorem weightedGraph_support (hM : M.IsFiniteCartan) :
    hM.weightedGraph.support = M.supportGraph hM.zero_comm := by
  ext i j
  change (0 < if i = j then (0 : ℝ) else Real.sqrt ((M i j * M j i : ℤ) : ℝ)) ↔
    i ≠ j ∧ M i j ≠ 0
  by_cases hij : i = j
  · subst j; simp
  · simp only [ite_eq_right hij, Real.sqrt_pos]
    rw [Int.cast_pos]
    constructor
    · intro h
      refine ⟨hij, ?_⟩
      intro hz
      simp [hz] at h
    · rintro ⟨_, h⟩
      have hi := lt_of_le_of_ne (hM.offDiag_nonpos i j hij) h
      have hj := lt_of_le_of_ne (hM.offDiag_nonpos j i (Ne.symm hij))
        (fun hz => h ((hM.zero_comm i j).mpr hz))
      exact mul_pos_of_neg_of_neg hi hj

/-- The diagonal similarity is `2I` minus the canonical weighted adjacency matrix. -/
theorem cartanSymmetrization_eq (hM : M.IsFiniteCartan) {d : ι → ℤ}
    (hd : ∀ i, 0 < d i) (hH : (diagonal d * M).PosDef) :
    cartanSymmetrization M d = (2 : ℝ) • (1 : Matrix ι ι ℝ) -
      hM.weightedGraph.weights := by
  ext i j
  change cartanSymmetrization M d i j =
    (2 : ℝ) * (if i = j then 1 else 0) -
      (if i = j then 0 else Real.sqrt ((M i j * M j i : ℤ) : ℝ))
  by_cases hij : i = j
  · subst j
    simp [hM.cartanSymmetrization_diag hd]
  · have hn : cartanSymmetrization M d i j ≤ 0 := by
      rw [cartanSymmetrization_apply]
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
        exact_mod_cast hM.offDiag_nonpos i j hij
      · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    simp only [ite_eq_right hij, mul_zero, zero_sub]
    rw [← hM.cartanSymmetrization_sq hd hH, Real.sqrt_sq_eq_abs, abs_of_nonpos hn, neg_neg]

/-- Every positive weight of a finite Cartan matrix is 1, √2, or √3. -/
theorem weightedGraph_weight_mem (hM : M.IsFiniteCartan) {i j : ι}
    (hij : hM.weightedGraph.support.Adj i j) :
    hM.weightedGraph.weights i j = 1 ∨
      hM.weightedGraph.weights i j = Real.sqrt 2 ∨
      hM.weightedGraph.weights i j = Real.sqrt 3 := by
  have hne : i ≠ j := hij.ne
  change (if i = j then (0 : ℝ) else Real.sqrt ((M i j * M j i : ℤ) : ℝ)) = 1 ∨ _
  rcases hM.edge_product_mem hne with h | h | h | h
  · change 0 < if i = j then (0 : ℝ) else Real.sqrt ((M i j * M j i : ℤ) : ℝ) at hij
    simp [h] at hij
  · left; simp [hne, h]
  · right; left
    change (if i = j then (0 : ℝ) else Real.sqrt ((M i j * M j i : ℤ) : ℝ)) = _
    rw [ite_eq_right hne, h]
    norm_num
  · right; right
    change (if i = j then (0 : ℝ) else Real.sqrt ((M i j * M j i : ℤ) : ℝ)) = _
    rw [ite_eq_right hne, h]
    norm_num

/-- The largest eigenvalue of the canonical weighted adjacency matrix is strictly below 2. -/
theorem maxRayleigh_weightedGraph_lt_two [Nonempty ι] (hM : M.IsFiniteCartan) :
    maxRayleigh hM.weightedGraph.isHermitian < 2 := by
  obtain ⟨d, hd, hH⟩ := hM.exists_posDef
  have hp := posDef_cartanSymmetrization hd hH
  rw [hM.cartanSymmetrization_eq hd hH] at hp
  obtain ⟨x, hnorm, heig⟩ := (hM.weightedGraph.isHermitian.maxRayleigh_eigenvalue).1
  have hx : x ≠ 0 := by intro h; simp [h] at hnorm
  have hval := hp.dotProduct_mulVec_pos hx
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, hnorm, heig, mul_one] at hval
  linarith

/-- The symmetrization lemma of Remark 3.11. For the given positive integer symmetrizer,
`S = D^(1/2) M D^(-1/2)` is positive definite, is `2I-B`, and the canonical weighted graph
is connected, has weights 1, √2, √3, and has maximum Rayleigh value below 2. -/
theorem symmetrization [Nonempty ι] (hM : M.IsFiniteCartan) (hind : M.IsIndecomposable)
    {d : ι → ℤ} (hd : ∀ i, 0 < d i) (hH : (diagonal d * M).PosDef) :
    (cartanSymmetrization M d).PosDef ∧
    cartanSymmetrization M d = (2 : ℝ) • (1 : Matrix ι ι ℝ) - hM.weightedGraph.weights ∧
    hM.weightedGraph.support.Connected ∧
    (∀ i j, hM.weightedGraph.support.Adj i j →
      hM.weightedGraph.weights i j = 1 ∨
      hM.weightedGraph.weights i j = Real.sqrt 2 ∨
      hM.weightedGraph.weights i j = Real.sqrt 3) ∧
    maxRayleigh hM.weightedGraph.isHermitian < 2 := by
  refine ⟨posDef_cartanSymmetrization hd hH, hM.cartanSymmetrization_eq hd hH,
    ?_, fun _ _ h => hM.weightedGraph_weight_mem h, hM.maxRayleigh_weightedGraph_lt_two⟩
  rw [hM.weightedGraph_support]
  exact (isIndecomposable_iff_connected_support M hM.zero_comm).mp hind

end IsFiniteCartan

end Matrix
