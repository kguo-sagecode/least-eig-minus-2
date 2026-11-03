/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Resolution
import LineGraphs.LineGraphSpectra.FourSpaces

/-!
# The spectrum of the resolution graph

Example 5.13 (`ex:5.13`) of [CGSS], steps `s5exvalues`–`s5exspec`.
The class and incidence Gram identities construct the four spectral projections;
their traces are the dimensions of the blueprint's four spaces.
-/

open Matrix
open scoped BigOperators

namespace Design.Resolution

attribute [local instance] Classical.propDecidable

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {k : ℕ} {D : Design P B (k * (2 * k - 1)) k (4 * k ^ 2 - 1) (2 * k + 1) 1}
  (R : D.Resolution (2 * k + 1))

/-- The class Gram row sums (`s5exvj`, Example 5.13 of [CGSS]). -/
theorem classGram_row_sum (a : B) :
    ∑ d, (R.classMatrixᵀ * R.classMatrix) a d = (2 * k - 1 : ℕ) := by
  simp_rw [R.transpose_classMatrix_mul_apply]
  simpa only [eq_comm, Finset.sum_boole] using
    congrArg (fun n : ℕ ↦ (n : ℝ)) (R.card_class (R.classOf a))

/-- The incidence Gram row sums (`s5exvj`, Example 5.13 of [CGSS]). -/
theorem incidenceGram_row_sum (a : B) :
    ∑ d, (D.realIncMatrixᵀ * D.realIncMatrix) a d = (k : ℝ) * (2 * k + 1) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, D.realIncMatrix_row_sum]
  rw [← Finset.sum_mul, D.realIncMatrix_col_sum]
  push_cast
  rfl

/-- The adjacency products used on all four spaces in `s5exvalues`,
Example 5.13 of [CGSS]. -/
theorem adjMatrix_products :
    let A := R.graph.adjMatrix ℝ
    let J := Matrix.of (fun (_ : B) (_ : B) ↦ (1 : ℝ))
    let Q := R.classMatrixᵀ * R.classMatrix
    let G := D.realIncMatrixᵀ * D.realIncMatrix
    A * J = (2 * (k : ℝ) * (k - 1)) • J ∧
      A * Q = (k - 1 : ℝ) • J - (k - 1 : ℝ) • Q ∧
        A * G = (k : ℝ) ^ 2 • J - (k : ℝ) • G := by
  dsimp only
  let J : Matrix B B ℝ := Matrix.of (fun _ _ ↦ 1)
  let Q := R.classMatrixᵀ * R.classMatrix
  let G := D.realIncMatrixᵀ * D.realIncMatrix
  have hk : 2 ≤ k := D.one_lt_k
  have hq : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hn : (Fintype.card B : ℝ) = 4 * (k : ℝ) ^ 2 - 1 := by
    rw [D.card_blocks, Nat.cast_sub (by nlinarith), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow, Nat.cast_one]
  have hJJ : J * J = (4 * (k : ℝ) ^ 2 - 1) • J := by
    ext a d
    simp [J, Matrix.mul_apply, hn]
  have hQJ : Q * J = (2 * (k : ℝ) - 1) • J := by
    ext a d
    simpa only [J, Q, Matrix.mul_apply, Matrix.of_apply, mul_one, Matrix.smul_apply,
      smul_eq_mul, hq] using R.classGram_row_sum a
  have hGJ : G * J = ((k : ℝ) * (2 * k + 1)) • J := by
    ext a d
    simpa only [J, G, Matrix.mul_apply, Matrix.of_apply, mul_one, Matrix.smul_apply,
      smul_eq_mul] using incidenceGram_row_sum (D := D) a
  have hQT : Qᵀ = Q := by simp [Q, Matrix.transpose_mul]
  have hGT : Gᵀ = G := by simp [G, Matrix.transpose_mul]
  have hJT : Jᵀ = J := rfl
  have hJQ : J * Q = (2 * (k : ℝ) - 1) • J := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, hQT, hJT] using
      congrArg Matrix.transpose hQJ
  have hJG : J * G = ((k : ℝ) * (2 * k + 1)) • J := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, hGT, hJT] using
      congrArg Matrix.transpose hGJ
  have hQQ : Q * Q = (2 * (k : ℝ) - 1) • Q := by
    change (R.classMatrixᵀ * R.classMatrix) * (R.classMatrixᵀ * R.classMatrix) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R.classMatrix, R.classMatrix_mul_transpose,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hq]
  have hGG : G * G = (2 * k : ℝ) • G + (k : ℝ) ^ 2 • J := by
    change (D.realIncMatrixᵀ * D.realIncMatrix) *
      (D.realIncMatrixᵀ * D.realIncMatrix) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc D.realIncMatrix,
      realIncMatrix_mul_transpose (D := D),
      Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_smul]
    congr 1
    ext a d
    simp [J, Matrix.mul_apply, ← Finset.sum_mul, D.realIncMatrix_col_sum, pow_two]
  have hQG : Q * G = (k : ℝ) • J := by
    change (R.classMatrixᵀ * R.classMatrix) * (D.realIncMatrixᵀ * D.realIncMatrix) = _
    have hCN : R.classMatrix * D.realIncMatrixᵀ = Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
      ext i p
      have he := congrArg (fun M : Matrix P (Fin (2 * k + 1)) ℝ ↦ M p i)
        R.realIncMatrix_mul_classMatrix_transpose
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_comm] using he
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc R.classMatrix, hCN]
    ext a d
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, one_mul,
      D.realIncMatrix_col_sum, Matrix.smul_apply, J, smul_eq_mul, mul_one]
    rw [← Finset.sum_mul, R.sum_classMatrix, one_mul]
  have hGQ : G * Q = (k : ℝ) • J := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, hQT, hGT, hJT] using
      congrArg Matrix.transpose hQG
  change R.graph.adjMatrix ℝ * J = _ ∧ R.graph.adjMatrix ℝ * Q = _ ∧
    R.graph.adjMatrix ℝ * G = _
  rw [R.adjMatrix_graph]
  change (J - Q - G + (k : ℝ) • 1) * J = _ ∧
    (J - Q - G + (k : ℝ) • 1) * Q = _ ∧
      (J - Q - G + (k : ℝ) • 1) * G = _
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    hJJ, hQJ, hGJ, hJQ, hQQ, hGQ, hJG, hQG, hGG]
  constructor
  · ext a d
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · constructor <;> ext a d <;>
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- The four projectors onto `j`, `W₁`, `W₂`, and `W₃` in `s5exvalues`,
Example 5.13 of [CGSS]. -/
noncomputable def projections : Fin 4 → Matrix B B ℝ :=
  Matrix.resolutionProjections k (Matrix.of (fun _ _ ↦ 1))
    (R.classMatrixᵀ * R.classMatrix) (D.realIncMatrixᵀ * D.realIncMatrix)

/-- The four actions in `s5exvalues`, Example 5.13 of [CGSS]. -/
theorem mul_projections (i : Fin 4) :
    R.graph.adjMatrix ℝ * R.projections i =
      Matrix.resolutionEigenvalues k i • R.projections i :=
  Matrix.mul_resolutionProjections D.one_lt_k R.adjMatrix_graph
    R.adjMatrix_products.1 R.adjMatrix_products.2.1 R.adjMatrix_products.2.2 i

/-- The symmetry required for the orthogonal spaces in `s5exdims`,
Example 5.13 of [CGSS]. -/
theorem isHermitian_projections (i : Fin 4) : (R.projections i).IsHermitian := by
  apply Matrix.isHermitian_resolutionProjections
  · exact Matrix.isHermitian_iff_isSymm.mpr rfl
  · exact (Matrix.spectrumMultiset_gram_products R.classMatrix).2.1.isHermitian
  · exact (Matrix.spectrumMultiset_gram_products D.realIncMatrix).2.1.isHermitian

/-- The four spaces span in `s5exspecH`, Example 5.13 of [CGSS]. -/
theorem sum_projections : ∑ i, R.projections i = 1 := Matrix.sum_resolutionProjections _ _ _ _

/-- The trace computation for `s5exd12` and `s5exd3`, Example 5.13 of [CGSS]. -/
theorem trace_projections (i : Fin 4) :
    (R.projections i).trace = (Matrix.resolutionMultiplicities k i : ℝ) := by
  have hk := D.one_lt_k
  have hn : (Fintype.card B : ℝ) = 4 * (k : ℝ) ^ 2 - 1 := by
    rw [D.card_blocks, Nat.cast_sub (by nlinarith), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow, Nat.cast_one]
  apply Matrix.trace_resolutionProjections hk D.card_blocks
  · simpa [Matrix.trace] using hn
  · simp only [Matrix.trace, Matrix.diag_apply, R.transpose_classMatrix_mul_apply, ite_true,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hn]
  · simp only [Matrix.trace, Matrix.diag_apply, D.transpose_realIncMatrix_mul_apply,
      Finset.inter_self, D.card_block, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    ring

/-- The exact four eigenspace dimensions in `s5exdims`, Example 5.13 of [CGSS]. -/
theorem finrank_eigenspace (i : Fin 4) :
    Module.finrank ℝ (Module.End.eigenspace (R.graph.adjMatrix ℝ).toLin'
      (Matrix.resolutionEigenvalues k i)) = Matrix.resolutionMultiplicities k i := by
  have he := (R.graph.isHermitian_adjMatrix ℝ).finrank_eigenspace_of_eigenprojections
    R.projections (Matrix.resolutionEigenvalues k)
    (Matrix.resolutionEigenvalues_injective D.one_lt_k) R.isHermitian_projections
    R.sum_projections R.mul_projections i
  rw [R.trace_projections] at he
  exact_mod_cast he

/-- The spectrum in `s5exspecH`, Example 5.13 of [CGSS], including all multiplicities. -/
theorem spectrumMultiset_graph :
    R.graph.spectrumMultiset = {(2 * (k : ℝ) * (k - 1))} +
      Multiset.replicate (2 * k) (-(k - 1 : ℝ)) +
      Multiset.replicate ((k - 1) * (2 * k + 1)) (k : ℝ) +
      Multiset.replicate ((k - 1) * (2 * k + 1)) (-(k : ℝ)) := by
  have hs := (R.graph.isHermitian_adjMatrix ℝ).spectrumMultiset_eq_of_eigenprojections
    R.projections (Matrix.resolutionEigenvalues k)
    (Matrix.resolutionEigenvalues_injective D.one_lt_k) R.isHermitian_projections
    R.sum_projections R.mul_projections (Matrix.resolutionMultiplicities k) R.trace_projections
  rw [SimpleGraph.spectrumMultiset, hs]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.resolutionMultiplicities,
    Matrix.resolutionEigenvalues, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Multiset.replicate_one, add_zero]
  abel

/-- Regularity in `s5exvj` and `s5exspec`, Example 5.13 of [CGSS]. -/
theorem graph_isRegularOfDegree : R.graph.IsRegularOfDegree (2 * k * (k - 1)) := by
  intro a
  have he := congrArg (fun M : Matrix B B ℝ ↦ M a a) R.adjMatrix_products.1
  have he' : (R.graph.degree a : ℝ) = 2 * (k : ℝ) * (k - 1) := by
    simpa [SimpleGraph.adjMatrix_mul_apply] using he
  have hk := D.one_lt_k
  have hcast : ((2 * k * (k - 1) : ℕ) : ℝ) = 2 * (k : ℝ) * (k - 1) := by
    simp [Nat.cast_sub (by omega : 1 ≤ k)]
  exact_mod_cast he'.trans hcast.symm

/-- Connectedness in `s5exspec`, Example 5.13 of [CGSS], by Lemma 5.1. -/
theorem graph_connected : R.graph.Connected := by
  have hn : 0 < Fintype.card B := by rw [D.card_blocks]; exact D.b_pos
  have : Nonempty B := Fintype.card_pos_iff.mp hn
  have hcast : ((2 * k * (k - 1) : ℕ) : ℝ) = 2 * (k : ℝ) * (k - 1) := by
    simp [Nat.cast_sub (by have := D.one_lt_k; omega : 1 ≤ k)]
  have hm : R.graph.eigenvalueMultiplicity (2 * k * (k - 1) : ℕ) = 1 := by
    rw [SimpleGraph.eigenvalueMultiplicity,
      (R.graph.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank, hcast]
    exact R.finrank_eigenspace 0
  have hc : Fintype.card R.graph.ConnectedComponent = 1 :=
    R.graph_isRegularOfDegree.multiplicity_eq_card_components.symm.trans hm
  have : Subsingleton R.graph.ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hc)
  exact { preconnected := fun a d ↦
    SimpleGraph.ConnectedComponent.eq.mp (Subsingleton.elim _ _), nonempty := inferInstance }

/-- Nonbipartiteness in `s5exnonbip`, Example 5.13 of [CGSS], by Lemma 5.3. -/
theorem graph_not_isBipartite : ¬ R.graph.IsBipartite := by
  rw [R.graph_isRegularOfDegree.isBipartite_iff_neg_eigenvalue R.graph_connected,
    R.spectrumMultiset_graph]
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast D.one_lt_k
  have hk1 : 1 ≤ k := by have := D.one_lt_k; omega
  simp only [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate,
    Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_ofNat, Nat.cast_one, or_assoc]
  rintro (h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩) <;> nlinarith

end Design.Resolution
