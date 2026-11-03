/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Recognition

/-!
# The converse for named finite Cartan matrices

Theorem A of Remark 3.11: the independent model weights and symmetrizers give
positive definiteness and indecomposability without assuming finite Cartan type.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maximum-eigenvalue bound alone makes `2I - B` positive definite
(the converse step of Theorem A, Remark 3.11). -/
theorem IsHermitian.posDef_two_smul_one_sub [Nonempty ι] {B : Matrix ι ι ℝ}
    (hB : B.IsHermitian) (hmax : maxRayleigh hB < 2) :
    ((2 : ℝ) • (1 : Matrix ι ι ℝ) - B).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos ((isHermitian_one.smul (by rfl)).sub hB)
  intro x hx
  have hnorm : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (dotProduct_self_star_pos_iff.mpr hx)
  have hbound := hB.quadratic_le_maxRayleigh x
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- Positive definiteness of the real cast implies integer positive definiteness
(the converse step of Theorem A, Remark 3.11). -/
theorem PosDef.posDef_int_of_posDef_real [Finite ι] {H : Matrix ι ι ℤ}
    (hH : (H.map (Int.castRingHom ℝ)).PosDef) : H.PosDef := by
  let _ := Fintype.ofFinite ι
  apply PosDef.of_dotProduct_mulVec_pos
  · apply isHermitian_iff_isSymm.mpr
    apply IsSymm.ext
    intro i j
    have h := (isHermitian_iff_isSymm.mp hH.isHermitian).apply i j
    change (H j i : ℝ) = (H i j : ℝ) at h
    exact_mod_cast h
  · intro x hx
    have hcast : (fun i ↦ (x i : ℝ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have hi := congr_fun h i
      change (x i : ℝ) = 0 at hi
      exact_mod_cast hi
    have hp := hH.dotProduct_mulVec_pos hcast
    simp only [star_trivial, dotProduct, mulVec, map_apply, Int.coe_castRingHom] at hp ⊢
    exact_mod_cast hp

/-- Balancing identities suffice for the diagonal similarity formula; no positivity
of the Cartan matrix is assumed (Theorem A, Remark 3.11). -/
theorem cartanSymmetrization_eq_of_balance {N : Matrix ι ι ℤ} {d : ι → ℤ}
    (hd : ∀ i, 0 < d i) (hdiag : ∀ i, N i i = 2)
    (hoff : ∀ i j, i ≠ j → N i j ≤ 0)
    (hb : ∀ i j, d i * N i j = d j * N j i) :
    cartanSymmetrization N d = (2 : ℝ) • (1 : Matrix ι ι ℝ) -
      (CartanMatrix.weightedGraph N).weights := by
  have hdR (i : ι) : (0 : ℝ) < d i := by exact_mod_cast hd i
  have hs (i : ι) : Real.sqrt (d i : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (hdR i)).ne'
  have hsym : (cartanSymmetrization N d).IsSymm := by
    apply IsSymm.ext
    intro i j
    have hbR : (d i : ℝ) * N i j = (d j : ℝ) * N j i := by exact_mod_cast hb i j
    simp only [cartanSymmetrization_apply]
    field_simp [hs]
    ring_nf
    rw [Real.sq_sqrt (hdR i).le, Real.sq_sqrt (hdR j).le]
    nlinarith only [hbR]
  ext i j
  change cartanSymmetrization N d i j =
    (2 : ℝ) * (if i = j then 1 else 0) -
      (if i = j then 0 else Real.sqrt ((N i j * N j i : ℤ) : ℝ))
  by_cases hij : i = j
  · subst j
    simp only [cartanSymmetrization_apply, hdiag, Int.cast_ofNat, ite_true, mul_one, sub_zero]
    field_simp [hs]
  · have hn : cartanSymmetrization N d i j ≤ 0 := by
      rw [cartanSymmetrization_apply]
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
        exact_mod_cast hoff i j hij
      · positivity
    have hsq : cartanSymmetrization N d i j ^ 2 = ((N i j * N j i : ℤ) : ℝ) := by
      calc
        _ = cartanSymmetrization N d i j * cartanSymmetrization N d j i := by
          rw [hsym.apply i j, pow_two]
        _ = _ := by
          simp only [cartanSymmetrization_apply, Int.cast_mul]
          field_simp [hs]
    simp only [ite_eq_right hij, mul_zero, zero_sub]
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonpos hn, neg_neg]

/-- A positive diagonal congruence recovers the integer symmetrized matrix
(the converse step of Theorem A, Remark 3.11). -/
theorem PosDef.posDef_diagonal_mul_of_cartanSymmetrization {N : Matrix ι ι ℤ} {d : ι → ℤ}
    (hd : ∀ i, 0 < d i) (hp : (cartanSymmetrization N d).PosDef) :
    (diagonal d * N).PosDef := by
  have hdR (i : ι) : (0 : ℝ) < d i := by exact_mod_cast hd i
  have hs (i : ι) : Real.sqrt (d i : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (hdR i)).ne'
  let T : Matrix ι ι ℝ := diagonal (fun i ↦ Real.sqrt (d i : ℝ))
  have hT : Function.Injective T.mulVec := by
    intro x y h
    funext i
    have hi := congr_fun h i
    simp only [T, mulVec_diagonal] at hi
    exact mul_left_cancel₀ (hs i) hi
  suffices hreal : ((diagonal d * N).map (Int.castRingHom ℝ)).PosDef from
    hreal.posDef_int_of_posDef_real
  convert hp.conjTranspose_mul_mul_same hT using 1
  ext i j
  simp only [T, diagonal_conjTranspose, star_trivial, mul_diagonal, diagonal_mul,
    cartanSymmetrization_apply, map_apply, Int.coe_castRingHom, Int.cast_mul]
  field_simp [hs]
  rw [Real.sq_sqrt (hdR i).le]
  ring

end Matrix

namespace CartanMatrix

open Matrix

/-- The positive integer symmetrizers in `def:rem-matrices`, Remark 3.11. -/
def modelSymmetrizer {n : ℕ} : FiniteType n → Fin n → ℤ
  | .a _ _ => fun _ ↦ 1
  | .b n _ => fun i ↦ if i.val = n - 1 then 2 else 1
  | .c n _ => fun i ↦ if i.val = n - 1 then 1 else 2
  | .d _ _ => fun _ ↦ 1
  | .e₆ => fun _ ↦ 1
  | .e₇ => fun _ ↦ 1
  | .e₈ => fun _ ↦ 1
  | .f₄ => ![1, 1, 2, 2]
  | .g₂ => ![1, 3]

/-- The displayed symmetrizers are positive (Theorem A, Remark 3.11). -/
theorem modelSymmetrizer_pos {n : ℕ} (t : FiniteType n) (i : Fin n) :
    0 < modelSymmetrizer t i := by
  cases t <;> simp only [modelSymmetrizer]
  all_goals first | positivity | (fin_cases i <;> norm_num)

/-- The displayed symmetrizers balance every ordered entry
(the converse step of Theorem A, Remark 3.11). -/
theorem modelSymmetrizer_balance {n : ℕ} (t : FiniteType n) (i j : Fin n) :
    modelSymmetrizer t i * modelEntries t i j =
      modelSymmetrizer t j * modelEntries t j i := by
  cases t with
  | a n _ => simpa [modelSymmetrizer, modelEntries] using (A_isSymm n).apply j i
  | b n _ =>
    have hi := i.isLt
    have hj := j.isLt
    simp only [modelSymmetrizer, modelEntries, B, of_apply]
    split_ifs <;> norm_num <;> omega
  | c n _ =>
    have hi := i.isLt
    have hj := j.isLt
    simp only [modelSymmetrizer, modelEntries, C, of_apply]
    split_ifs <;> norm_num <;> omega
  | d n _ => simpa [modelSymmetrizer, modelEntries] using (D_isSymm n).apply j i
  | e₆ | e₇ | e₈ =>
    simpa [modelSymmetrizer, modelEntries] using (E_isSymm _).apply j i
  | f₄ => fin_cases i <;> fin_cases j <;> norm_num [modelSymmetrizer, modelEntries, F₄]
  | g₂ => fin_cases i <;> fin_cases j <;> norm_num [modelSymmetrizer, modelEntries, G₂]

/-- Every named matrix is finite Cartan (the converse in Theorem A, Remark 3.11). -/
theorem IsFiniteTypeModel.isFiniteCartan {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}
    (hN : IsFiniteTypeModel N) : N.IsFiniteCartan := by
  obtain ⟨t, rfl⟩ := hN
  have : Nonempty (Fin n) := ⟨⟨0, t.rank_pos⟩⟩
  refine ⟨model_diag t, model_offDiag_nonpos t, model_zero_comm t,
    modelSymmetrizer t, modelSymmetrizer_pos t, ?_⟩
  have hp : (cartanSymmetrization (modelEntries t) (modelSymmetrizer t)).PosDef := by
    rw [cartanSymmetrization_eq_of_balance (modelSymmetrizer_pos t) (model_diag t)
      (model_offDiag_nonpos t) (modelSymmetrizer_balance t)]
    exact (weightedGraph (modelEntries t)).isHermitian.posDef_two_smul_one_sub
      (model_support_labelling t).maxRayleigh_lt_two
  exact hp.posDef_diagonal_mul_of_cartanSymmetrization (modelSymmetrizer_pos t)

/-- Every named matrix is indecomposable (the converse in Theorem A, Remark 3.11). -/
theorem IsFiniteTypeModel.isIndecomposable {n : ℕ} {N : Matrix (Fin n) (Fin n) ℤ}
    (hN : IsFiniteTypeModel N) : N.IsIndecomposable := by
  obtain ⟨t, rfl⟩ := hN
  have : Nonempty (Fin n) := ⟨⟨0, t.rank_pos⟩⟩
  have hN := (modelEntries_isFiniteTypeModel t).isFiniteCartan
  apply (isIndecomposable_iff_connected_support _ hN.zero_comm).mpr
  rw [← hN.weightedGraph_support, ← weightedGraph_eq hN]
  exact model_support_connected t

end CartanMatrix
