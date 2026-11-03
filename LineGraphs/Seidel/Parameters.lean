/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import LineGraphs.Seidel.Rank

/-!
# Parameters with eigenvalue minus two

Lemma `lem:414-srg` of the blueprint for Remark 4.14 of [CGSS]. The determinant
hypothesis supplies a null vector; no classification of root systems is used.
-/

open Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {n k a c : ℕ}

/-- The null vector step `s414srgnull` in Lemma `lem:414-srg`, Remark 4.14 of
[CGSS]: a null vector of `2I + A` is killed by the all-ones matrix. -/
theorem IsSRGWith.exists_adjMatrix_mulVec_eq_neg_two
    (h : X.IsSRGWith n k a c)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0) :
    ∃ z : V → ℝ, z ≠ 0 ∧ X.adjMatrix ℝ *ᵥ z = (-2 : ℝ) • z ∧
      (∑ v, z v) = 0 := by
  obtain ⟨z, hz, hQz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAz : X.adjMatrix ℝ *ᵥ z = (-2 : ℝ) • z := by
    rw [add_mulVec, smul_mulVec, one_mulVec] at hQz
    rw [eq_neg_of_add_eq_zero_right hQz, neg_smul]
  have hsum : ∑ v, (X.adjMatrix ℝ *ᵥ z) v = (k : ℝ) * ∑ v, z v := by
    simp only [mulVec, dotProduct]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Finset.sum_mul]
    congr 1
    simp_rw [X.adjMatrix_apply, X.adj_comm _ w]
    simpa using (X.degree_eq_sum_if_adj (R := ℝ) w).symm.trans
      (congrArg (fun t : ℕ ↦ (t : ℝ)) (h.regular w))
  have hzero : ∑ v, z v = 0 := by
    rw [hAz] at hsum
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hsum
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  exact ⟨z, hz, hAz, hzero⟩

/-- Step `s414srglin` of Lemma `lem:414-srg`, Remark 4.14 of [CGSS]. -/
theorem IsSRGWith.linear_relation_of_det_two_add_adjMatrix_eq_zero
    (h : X.IsSRGWith n k a c)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0) :
    (k : ℤ) - 2 * a + c = 4 := by
  obtain ⟨z, hz, hAz, hsum⟩ := h.exists_adjMatrix_mulVec_eq_neg_two hdet
  have hCz : Xᶜ.adjMatrix ℝ *ᵥ z = z := by
    have hJ := X.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    rw [X.compl_adjMatrix_eq_adjMatrix_compl ℝ] at hJ
    have he := congrArg (fun M ↦ M *ᵥ z) hJ
    simp only [add_mulVec, one_mulVec, hAz] at he
    have hjz : (Matrix.of fun (_ : V) (_ : V) ↦ (1 : ℝ)) *ᵥ z = 0 := by
      ext v
      simpa [mulVec, dotProduct] using hsum
    change z + (-2 : ℝ) • z + Xᶜ.adjMatrix ℝ *ᵥ z =
      (Matrix.of fun (_ : V) (_ : V) ↦ (1 : ℝ)) *ᵥ z at he
    rw [hjz] at he
    ext v
    have hv := congrFun he v
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hv
    linarith
  have hm := congrArg (fun M : Matrix V V ℝ ↦ M *ᵥ z) h.matrix_eq
  rw [pow_two, ← mulVec_mulVec, hAz, mulVec_smul, hAz] at hm
  simp only [add_mulVec, smul_mulVec, one_mulVec, hAz, hCz] at hm
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hz
  have he := congrFun hm v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at he
  change (-2 : ℝ) * (-2 * z v) =
    (k : ℝ) * z v + (a : ℝ) * (-2 * z v) + (c : ℝ) * z v at he
  have hv' : z v ≠ 0 := hv
  have hr : (k : ℝ) - 2 * a + c = 4 := by
    apply (mul_right_cancel₀ hv')
    nlinarith [he]
  exact_mod_cast hr

/-- Steps `s414srgnc` and `s414srgpairs` of Lemma `lem:414-srg`, Remark 4.14
of [CGSS]: singularity excludes both the empty and the complete graph. -/
theorem IsSRGWith.ne_bot_and_ne_top_of_det_two_add_adjMatrix_eq_zero
    (h : X.IsSRGWith n k a c)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0) :
    X ≠ ⊥ ∧ X ≠ ⊤ := by
  obtain ⟨z, hz, hAz, hsum⟩ := h.exists_adjMatrix_mulVec_eq_neg_two hdet
  constructor
  · intro hbot
    have : X.adjMatrix ℝ = 0 := by ext u v; simp [adjMatrix_apply, hbot]
    rw [this, zero_mulVec] at hAz
    exact hz ((smul_eq_zero.mp hAz.symm).resolve_left (by norm_num))
  · intro htop
    apply hz
    have hJ := X.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    rw [X.compl_adjMatrix_eq_adjMatrix_compl ℝ] at hJ
    have he := congrArg (fun M ↦ M *ᵥ z) hJ
    have hC : Xᶜ.adjMatrix ℝ = 0 := by ext u v; simp [adjMatrix_apply, htop]
    simp only [add_mulVec, one_mulVec, hAz, hC, add_zero] at he
    ext v
    have hv := congrFun he v
    simp [mulVec, dotProduct, hsum] at hv
    change z v = 0
    linarith

omit [DecidableEq V] in
/-- Step `s414srgc` of Lemma `lem:414-srg`, Remark 4.14 of [CGSS]: in a
connected, noncomplete strongly regular graph a nonedge has a common neighbour. -/
theorem IsSRGWith.pos_of_connected_of_ne_top (h : X.IsSRGWith n k a c)
    (hc : X.Connected) (htop : X ≠ ⊤) : 0 < c := by
  have hpath {u v : V} (p : X.Walk u v) : u = v ∨ X.Adj u v ∨ 0 < c := by
    induction p with
    | nil => exact Or.inl rfl
    | @cons u w v huw _ ih =>
      rcases ih with rfl | hwv | hpos
      · exact Or.inr (Or.inl huw)
      · by_cases huv : u = v
        · exact Or.inl huv
        by_cases hadj : X.Adj u v
        · exact Or.inr (Or.inl hadj)
        have hne : Nonempty (X.commonNeighbors u v) := ⟨⟨w, huw, hwv.symm⟩⟩
        exact Or.inr (Or.inr (by
          rw [← h.of_not_adj huv hadj]
          exact Fintype.card_pos_iff.mpr hne))
      · exact Or.inr (Or.inr hpos)
  have hnon : ∃ u v, u ≠ v ∧ ¬ X.Adj u v := by
    by_contra hn
    push Not at hn
    exact htop (eq_top_iff_forall_ne_adj.mpr hn)
  obtain ⟨u, v, huv, hadj⟩ := hnon
  rcases hpath (hc.preconnected u v).some with heq | hedge | hpos
  · exact (huv heq).elim
  · exact (hadj hedge).elim
  · exact hpos

-- Lemma (strongly regular graphs with eigenvalue minus two), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-srg`, assertions 1--3, Remark 4.14 of [CGSS]: parameter
bounds, the nonedge union bound, and the linear relation. Integer subtraction
in the last assertion is not truncated. -/
theorem IsSRGWith.params_of_det_two_add_adjMatrix_eq_zero
    (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0) :
    1 ≤ k ∧ k ≤ n - 2 ∧ a ≤ k - 1 ∧ 1 ≤ c ∧ c ≤ k ∧
      2 * k - c ≤ n - 2 ∧ (k : ℤ) - 2 * a + c = 4 := by
  obtain ⟨hbot, htop⟩ := h.ne_bot_and_ne_top_of_det_two_add_adjMatrix_eq_zero hdet
  obtain ⟨u, v, huv⟩ := ne_bot_iff_exists_adj.mp hbot
  have hk : 0 < k := by
    rw [← h.regular u]
    exact (X.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩
  have ha : a < k := by
    rw [← h.of_adj u v huv, ← h.regular u]
    exact huv.card_commonNeighbors_lt_degree
  have hnon : ∃ u v, u ≠ v ∧ ¬ X.Adj u v := by
    by_contra hn
    push Not at hn
    exact htop (eq_top_iff_forall_ne_adj.mpr hn)
  obtain ⟨u', v', hne, hnot⟩ := hnon
  have hck : c ≤ k := by
    rw [← h.of_not_adj hne hnot, ← h.regular u']
    exact X.card_commonNeighbors_le_degree_left u' v'
  have hsub : X.neighborFinset u' ∪ X.neighborFinset v' ⊆
      Finset.univ \ {u', v'} := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases Finset.mem_union.mp hw with hw | hw
    · have hw' := X.mem_neighborFinset u' w |>.mp hw
      exact ⟨hw'.ne.symm, fun heq ↦ hnot (heq ▸ hw')⟩
    · have hw' := X.mem_neighborFinset v' w |>.mp hw
      exact ⟨fun heq ↦ hnot (heq ▸ hw').symm, hw'.ne.symm⟩
  have hbound : 2 * k - c ≤ n - 2 := by
    have hh := Finset.card_le_card hsub
    simpa only [h.card_neighborFinset_union_of_not_adj hne hnot,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_pair hne, h.card] using hh
  exact ⟨hk, by omega, by omega, h.pos_of_connected_of_ne_top hc htop, hck,
    hbound, h.linear_relation_of_det_two_add_adjMatrix_eq_zero hdet⟩

-- Lemma (strongly regular graphs with eigenvalue minus two), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-srg`, assertion 4, Remark 4.14 of [CGSS]: the rank identity,
proved by the centred idempotent in steps `s414srgtheta`--`s414srgrkQ`.
Both subtractions in the identity are integer subtractions. -/
theorem IsSRGWith.rank_two_add_adjMatrix_of_det_eq_zero
    (h : X.IsSRGWith n k a c) (hc : X.Connected)
    (hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0) :
    ((a : ℤ) - c + 4) *
        ((((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank : ℤ) - 1) =
      2 * n - k - 2 := by
  obtain ⟨hkpos, hkn, ha, hcpos, hck, hbound, hlin⟩ :=
    h.params_of_det_two_add_adjMatrix_eq_zero hc hdet
  let A := X.adjMatrix ℝ
  let Q := (2 : ℝ) • (1 : Matrix V V ℝ) + A
  let J : Matrix V V ℝ := Matrix.of fun _ _ ↦ 1
  let b : ℝ := k + 2
  let d : ℝ := (a : ℝ) - c + 4
  have hk : (k : ℝ) = 2 * a - c + 4 := by
    have hl : (k : ℝ) - 2 * a + c = 4 := by exact_mod_cast hlin
    linarith
  have hb : b ≠ 0 := by dsimp [b]; positivity
  have hd : d ≠ 0 := by
    have hck' : (c : ℝ) ≤ k := by exact_mod_cast hck
    dsimp [d]
    linarith
  have hC : Xᶜ.adjMatrix ℝ = J - 1 - A := by
    have hh := X.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    rw [X.compl_adjMatrix_eq_adjMatrix_compl ℝ] at hh
    change 1 + A + Xᶜ.adjMatrix ℝ = J at hh
    rw [← hh]
    abel
  have hA : A * A = (k : ℝ) • 1 + (a : ℝ) • A + (c : ℝ) • (J - 1 - A) := by
    simpa only [A, pow_two, Nat.cast_smul_eq_nsmul, hC] using
      (h.matrix_eq (α := ℝ))
  have hQ : Q * Q = d • Q + (c : ℝ) • J := by
    dsimp [Q]
    simp only [add_mul, mul_add, smul_mul, Matrix.mul_smul, one_mul, mul_one, hA]
    dsimp [d]
    rw [hk]
    module
  have hAJ : A * J = (k : ℝ) • J := by
    ext u v
    change (∑ w, X.adjMatrix ℝ u w * 1) = (k : ℝ) * 1
    simpa only [mulVec, dotProduct, Function.const_apply] using
      (X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) h.regular (a := 1) (v := u))
  have hQJ : Q * J = b • J := by
    dsimp [Q, b]
    rw [add_mul, smul_mul, one_mul, hAJ]
    module
  have hQsym : Q.transpose = Q := by
    ext u v
    simp [Q, A, Matrix.one_apply, eq_comm, X.adj_comm]
  have hJQ : J * Q = b • J := by
    have hh := congrArg Matrix.transpose hQJ
    simpa only [transpose_mul, transpose_smul, hQsym,
      show J.transpose = J from rfl] using hh
  have hJJ : J * J = (n : ℝ) • J := by
    ext u v
    simp [J, Matrix.mul_apply, h.card]
  have hcn : (c : ℝ) * n = b * (b - d) := by
    have hh : (d * b + (c : ℝ) * n) • J = (b * b) • J := by
      calc
        _ = (d • Q + (c : ℝ) • J) * J := by
          simp only [add_mul, smul_mul, hQJ, hJJ, smul_smul, add_smul]
        _ = Q * (Q * J) := by rw [← hQ, Matrix.mul_assoc]
        _ = (b * b) • J := by rw [hQJ, Matrix.mul_smul, hQJ, smul_smul]
    obtain ⟨u⟩ := hc.nonempty
    have he := congrArg (fun M : Matrix V V ℝ ↦ M u u) hh
    simp only [J, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one] at he
    nlinarith
  have htrQ : Q.trace = 2 * (n : ℝ) := by
    simp [Q, A, Matrix.trace, adjMatrix_apply, h.card, mul_comm]
  have htrJ : J.trace = (n : ℝ) := by simp [J, Matrix.trace, h.card]
  have hr := Matrix.mul_rank_sub_one_eq_of_quadratic Q J b c d n hb hd hQ hQJ hJQ
    hJJ hcn htrQ htrJ
  dsimp [Q, A, b, d] at hr
  have hr' : ((a : ℝ) - c + 4) *
      ((((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank : ℝ) - 1) =
        2 * n - k - 2 := by linarith
  exact_mod_cast hr'

end SimpleGraph
