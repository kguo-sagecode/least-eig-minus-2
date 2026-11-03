/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.RootType
import LineGraphs.Representation.SymmetricSquare
import LineGraphs.Representation.Valency
import LineGraphs.Spectral.AllOnes
import LineGraphs.Spectral.Frames
import LineGraphs.Spectral.RelativeBound
import LineGraphs.Computations.C8
import LineGraphs.Computations.C24
import LineGraphs.Computations.C9
import LineGraphs.Computations.C10

/-!
# Regular graphs represented in E₈

Theorem 4.4 of [CGSS] (blueprint `thm:4.4`), with Lemma (the matrices of a regular graph)
`lem:4-regmat`, the entrywise form of Lemma (trace and rank) `lem:4-tracerank`, the relative
bounds EQ1 (`lem:4-EQ1`) and EQ2 (`lem:4-EQ2`), and the remark after Theorem 4.4
(`rem:4-after44`), which uses Computation C24 (`LineGraphs/Computations/C24.lean`).

EQ2 puts the equiangular lines on a cone. This file keeps classification as the explicit
hypothesis `hclass` of EQ2, Theorem 4.4 and assertion 1 of the remark, in the form used by
`IsRepresentation.exists_isRepresentedIn_rootType_of_classification` for the cone's
nine-dimensional ambient space. Theorems 3.5 and 3.6 are available: the unconditional EQ2
is `InnerProductSpace.card_le_fourteen_of_finrank_eq_eight` in `Spectral/RelativeBoundFourteen`,
and `Representation/Theorem44Unconditional` discharges `hclass` for the settled bounds
`card_le_28_of_regular`, `degree_le_16_of_regular` and
`not_regular_28_16_isRepresentedIn_E₈`.

Two steps of Theorem 4.4 take a shorter route than the blueprint. Step `s44trace` bounds the
nonzero eigenvalues of `M` through the positive semidefinite matrix `P` of step `s44P` in place
of the columns `b_k`; and step `s44d`, the case `(n, d) = (28, 17)` left by C8, is closed by
Lemma (trace and rank) for `M` of rank at most 6, as in the remark, in place of the root types
of the components.
-/

open Matrix Module Submodule EuclideanSpace
open scoped RealInnerProductSpace

namespace Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The trace estimate in step `s44trace` of Theorem 4.4 of [CGSS]: a bound
on the nonzero eigenvalues bounds the trace by rank times that bound. -/
theorem IsHermitian.trace_le_rank_mul_of_eigenvalues_le {A : Matrix V V ℝ}
    (hA : A.IsHermitian) {B : ℝ}
    (hB : ∀ μ ∈ A.spectrumMultiset, μ ≠ 0 → μ ≤ B) :
    A.trace ≤ (A.rank : ℝ) * B := by
  classical
  let Z := Finset.univ.filter (fun i ↦ hA.eigenvalues i ≠ 0)
  have ht : ∑ i ∈ Z, hA.eigenvalues i = ∑ i, hA.eigenvalues i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [Z] using hi
  have hr : A.rank = Z.card := by
    rw [hA.rank_eq_card_non_zero_eigs]
    simp only [Z, Fintype.card_subtype]
  have htr : A.trace = ∑ i, hA.eigenvalues i := by simpa using hA.trace_pow_eq_sum 1
  rw [htr, ← ht, hr]
  calc
    _ ≤ ∑ _i ∈ Z, B := Finset.sum_le_sum fun i hi ↦
      hB _ (hA.eigenvalues_mem_spectrumMultiset i) (Finset.mem_filter.mp hi).2
    _ = _ := by simp

omit [DecidableEq V] in
/-- Lemma (trace and rank) `lem:4-tracerank`, used in Theorem 4.4 of [CGSS] and the remark
after it: `(tr N)² ≤ rk N · ∑ N(u,w)²`. The blueprint's name
`Matrix.IsHermitian.trace_sq_le_rank_mul_sum_sq` is taken in `Spectral/Applications.lean` by
the form with the squared eigenvalues; this is the entrywise form the blueprint states. -/
theorem IsHermitian.trace_sq_le_rank_mul_sum_entry_sq {A : Matrix V V ℝ}
    (hA : A.IsHermitian) : A.trace ^ 2 ≤ (A.rank : ℝ) * ∑ u, ∑ v, A u v ^ 2 := by
  classical
  have he : (A ^ 2).trace = ∑ u, ∑ v, A u v ^ 2 := by
    simp only [pow_two, trace, diag, mul_apply]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    have hv : A v u = A u v := by simpa using congrFun (congrFun hA u) v
    rw [hv]
  simpa only [he] using hA.trace_sq_le_rank_mul_trace_sq

omit [DecidableEq V] in
/-- Lemma `lem:4-regmat`, used in Theorem 4.4 of [CGSS]: changing a positive
constant eigenvalue to another positive value preserves positivity and rank. -/
theorem PosSemidef.rank_add_allOnes_of_pos [Nonempty V] {A : Matrix V V ℝ}
    (hA : A.PosSemidef) {b c : ℝ} (hb : 0 < b)
    (hrow : A *ᵥ (fun _ ↦ 1) = b • (fun _ ↦ 1))
    (hc : 0 < b + c * Fintype.card V) :
    (A + c • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))).PosSemidef ∧
      (A + c • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))).rank = A.rank := by
  classical
  let B := A + c • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))
  have hJ : (of fun (_ : V) (_ : V) ↦ (1 : ℝ)).IsHermitian := by ext; rfl
  have hB : B.IsHermitian := hA.isHermitian.add (hJ.smul (IsSelfAdjoint.all c))
  have hs : B.spectrumMultiset = {b + c * Fintype.card V} +
      A.spectrumMultiset.erase b := by
    simpa [B] using
      hA.isHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes hrow 0 1 c
  refine ⟨hB.posSemidef_iff_spectrumMultiset_nonneg.mpr ?_, ?_⟩
  · intro μ hμ
    rw [hs, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · exact hc.le
    · exact hA.isHermitian.posSemidef_iff_spectrumMultiset_nonneg.mp hA μ
        (Multiset.mem_of_mem_erase hμ)
  · rw [hB.rank_eq_card_sub_eigenvalueMultiplicity_zero,
      hA.isHermitian.rank_eq_card_sub_eigenvalueMultiplicity_zero]
    congr 1
    change B.spectrumMultiset.count 0 = A.spectrumMultiset.count 0
    rw [hs, Multiset.count_add, Multiset.count_erase_of_ne (ne_of_lt hb)]
    simp [hc.ne]

end Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {d : ℕ}

/-- The matrix `M` of `lem:4-regmat`, for Theorem 4.4 of [CGSS]. -/
noncomputable def centeredMatrix (X : SimpleGraph V) [DecidableRel X.Adj] (d : ℕ) :
    Matrix V V ℝ :=
  (1 / 2 : ℝ) • ((2 : ℝ) • 1 + X.adjMatrix ℝ) -
    (((d : ℝ) + 2) / (2 * Fintype.card V)) • (of fun _ _ ↦ (1 : ℝ))

/-- The matrix `E` of `lem:4-regmat`, for Theorem 4.4 of [CGSS]. -/
noncomputable def equiangularMatrix (X : SimpleGraph V) [DecidableRel X.Adj] :
    Matrix V V ℝ :=
  (2 / 3 : ℝ) • ((2 : ℝ) • 1 + X.adjMatrix ℝ) -
    (1 / 3 : ℝ) • (of fun _ _ ↦ (1 : ℝ))

/-- Lemma `lem:4-regmat`, step `s4rmj`, for Theorem 4.4 of [CGSS]. -/
theorem IsRegularOfDegree.gram_mulVec_one (h : X.IsRegularOfDegree d) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ) *ᵥ (fun _ ↦ 1) =
      ((d : ℝ) + 2) • (fun _ ↦ 1) := by
  ext u
  simp only [add_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_one]
  have ha := X.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) h (a := 1) (v := u)
  change (X.adjMatrix ℝ *ᵥ (fun _ ↦ 1)) u = (d : ℝ) * 1 at ha
  linarith

/-- Lemma `lem:4-regmat`, for Theorem 4.4 of [CGSS]: the toolkit's centered
matrix differs from `M` by the positive scalar two. -/
private theorem centered_eq_smul (X : SimpleGraph V) [DecidableRel X.Adj] (d : ℕ) :
    X.centeredMatrix d = (1 / 2 : ℝ) •
      (((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ) -
        (((d : ℝ) + 2) / Fintype.card V) • (of fun _ _ ↦ (1 : ℝ))) := by
  ext u v
  simp only [centeredMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    of_apply]
  ring

/-- Lemma `lem:4-regmat`, step `s4rmMpsd`, for Theorem 4.4 of [CGSS]. -/
theorem IsRegularOfDegree.posSemidef_centered [Nonempty V] (h : X.IsRegularOfDegree d)
    (hQ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    (X.centeredMatrix d).PosSemidef := by
  rw [centered_eq_smul]
  exact (hQ.rank_sub_allOnes (by positivity) h.gram_mulVec_one).1.smul (by norm_num)

/-- Lemma `lem:4-regmat`, step `s4rmMrk`, for Theorem 4.4 of [CGSS]. -/
theorem IsRegularOfDegree.rank_centered [Nonempty V] (h : X.IsRegularOfDegree d)
    (hQ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef) :
    (X.centeredMatrix d).rank =
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank - 1 := by
  rw [centered_eq_smul, rank_smul_of_mem_nonZeroDivisors _ (by norm_num)]
  exact (hQ.rank_sub_allOnes (by positivity) h.gram_mulVec_one).2

/-- Lemma `lem:4-regmat`, assertion 3, for Theorem 4.4 of [CGSS]: simultaneous
positivity and rank preservation when the new constant eigenvalue is positive. -/
private theorem equiangular_psd_rank [Nonempty V] (h : X.IsRegularOfDegree d)
    (hQ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hn : Fintype.card V < 2 * d + 4) :
    X.equiangularMatrix.PosSemidef ∧ X.equiangularMatrix.rank =
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank := by
  have hrow : ((2 / 3 : ℝ) • ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ)) *ᵥ
      (fun _ ↦ 1) = ((2 / 3 : ℝ) * (d + 2)) • (fun _ ↦ 1) := by
    rw [smul_mulVec, h.gram_mulVec_one, smul_smul]
  have hp := (hQ.smul (show (0 : ℝ) ≤ 2 / 3 by norm_num)).rank_add_allOnes_of_pos
    (by positivity) hrow (c := -(1 / 3)) (by
      have hn' : (Fintype.card V : ℝ) < 2 * d + 4 := by exact_mod_cast hn
      linarith)
  simpa only [equiangularMatrix, neg_smul, ← sub_eq_add_neg,
    rank_smul_of_mem_nonZeroDivisors _ (show (2 / 3 : ℝ) ∈ nonZeroDivisors ℝ by
      norm_num)] using hp

/-- Lemma `lem:4-regmat`, step `s4rmEpsd`, for Theorem 4.4 of [CGSS]. -/
theorem IsRegularOfDegree.posSemidef_equiangular [Nonempty V] (h : X.IsRegularOfDegree d)
    (hQ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hn : Fintype.card V < 2 * d + 4) : X.equiangularMatrix.PosSemidef :=
  (equiangular_psd_rank h hQ hn).1

/-- Lemma `lem:4-regmat`, step `s4rmErk`, for Theorem 4.4 of [CGSS]. -/
theorem IsRegularOfDegree.rank_equiangular [Nonempty V] (h : X.IsRegularOfDegree d)
    (hQ : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hn : Fintype.card V < 2 * d + 4) :
    X.equiangularMatrix.rank = ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank :=
  (equiangular_psd_rank h hQ hn).2

end SimpleGraph

namespace InnerProductSpace

variable {V E : Type*} [Fintype V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Lemma EQ1 (`lem:4-EQ1`), used in Theorem 4.4 of [CGSS]: the relative bound in the
finite-dimensional span, with the numerical consequence for dimension at most seven.
The ambient space need not be finite-dimensional. -/
theorem card_le_relativeBound (v : V → E) (hv : ∀ i, ‖v i‖ = 1)
    (hp : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 1 / 3 ∨ ⟪v i, v j⟫ = -(1 / 3))
    (hk : finrank ℝ (span ℝ (Set.range v)) ≤ 7) :
    (Fintype.card V : ℝ) ≤
      8 * finrank ℝ (span ℝ (Set.range v)) /
        (9 - finrank ℝ (span ℝ (Set.range v))) ∧ Fintype.card V ≤ 28 := by
  let U := span ℝ (Set.range v)
  let : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  let w : V → U := fun i ↦ ⟨v i, subset_span (Set.mem_range_self i)⟩
  have hk' : (finrank ℝ U : ℝ) ≤ 7 := by exact_mod_cast hk
  have h := Matrix.card_le_relative_bound_of_abs_inner_eq w
    (α := 1 / 3) (by norm_num) (by norm_num) hv (by
      intro i j hij
      change |⟪v i, v j⟫| = _
      rcases hp i j hij with h | h <;> rw [h] <;> norm_num) (by nlinarith)
  have he : (finrank ℝ U : ℝ) * (1 - (1 / 3 : ℝ) ^ 2) /
      (1 - finrank ℝ U * (1 / 3 : ℝ) ^ 2) =
      8 * finrank ℝ U / (9 - finrank ℝ U) := by
    have h₁ : (9 : ℝ) - finrank ℝ U ≠ 0 := by linarith
    have h₂ : 1 - (finrank ℝ U : ℝ) * (1 / 3 : ℝ) ^ 2 ≠ 0 := by nlinarith
    apply (div_eq_div_iff h₂ h₁).mpr
    ring
  rw [he] at h
  refine ⟨h, ?_⟩
  have hb : (8 : ℝ) * finrank ℝ U / (9 - finrank ℝ U) ≤ 28 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  exact_mod_cast h.trans hb

/-- Lemma EQ2 (`lem:4-EQ2`), used in Theorem 4.4 and its following remark in
[CGSS]. Theorem 3.6's classification for the cone's ambient space is explicit. -/
theorem card_le_fourteen_of_finrank_eq_eight_of_classification
    (v : V → E) (hv : ∀ i, ‖v i‖ = 1)
    (hp : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 1 / 3 ∨ ⟪v i, v j⟫ = -(1 / 3))
    (hspan : span ℝ (Set.range v) = ⊤) (hdim : finrank ℝ E = 8)
    (hclass : ∀ S : LineSystem (WithLp 2 (E × ℝ)),
      S.Φ.Nonempty → S.IsMaximal → S.IsIndecomposable →
      ∃ t : LineSystem.RootType, Nonempty (S.Iso t.model)) :
    Fintype.card V ≤ 14 := by
  classical
  have hc := SimpleGraph.isRepresentation_equiangularCone v hv hp
  obtain ⟨t, ht, hr⟩ := hc.exists_isRepresentedIn_rootType_of_classification
    (SimpleGraph.equiangularConeGraph_connected v) hclass
  apply ht.card_le_fourteen_of_equiangularCone
  rw [hr, finrank_span_equiangularCone v hspan hdim]

end InnerProductSpace

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {d : ℕ}

omit [Nonempty V] in
/-- Step `s44spec` of Theorem 4.4 of [CGSS]: the root Gram matrix has rank at most eight. -/
theorem IsRepresentedIn.posSemidef_two_add_adjMatrix_and_rank_le_eight
    (hX : X.IsRepresentedIn LineSystem.E₈) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef ∧
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ 8 := by
  obtain ⟨x, hx, _⟩ := hX
  rw [← hx]
  refine ⟨posSemidef_gram ℝ x, ?_⟩
  rw [rank_gram_eq_finrank_span]
  simpa using (Submodule.finrank_le (span ℝ (Set.range x)))

/-- Step `s44q` of Theorem 4.4 of [CGSS]: the centered matrix factors in dimension seven. -/
theorem IsRepresentedIn.exists_gram_centered (hX : X.IsRepresentedIn LineSystem.E₈)
    (h : X.IsRegularOfDegree d) :
    ∃ q : V → EuclideanSpace ℝ (Fin 7), gram ℝ q = X.centeredMatrix d := by
  obtain ⟨hp, hr⟩ := hX.posSemidef_two_add_adjMatrix_and_rank_le_eight
  apply (h.posSemidef_centered hp).exists_gram_euclideanSpace
  rw [h.rank_centered hp]
  omega

omit [Nonempty V] in
/-- Step `s44P` of Theorem 4.4 of [CGSS]: the symmetric-square Gram identity. -/
theorem gram_symSq_centered {q : V → EuclideanSpace ℝ (Fin 7)}
    (hq : gram ℝ q = X.centeredMatrix d) :
    let t := ((d : ℝ) + 2) / (2 * Fintype.card V)
    gram ℝ (fun u ↦ symSq (q u)) = (1 / 2 : ℝ) • (1 : Matrix V V ℝ) +
      (1 / 4 - t) • ((2 : ℝ) • 1 + X.adjMatrix ℝ) +
        t ^ 2 • (of fun _ _ ↦ (1 : ℝ)) := by
  dsimp only
  ext u v
  have he : ⟪q u, q v⟫ = (X.centeredMatrix d) u v := congrFun (congrFun hq u) v
  rw [gram_apply, inner_symSq, he]
  simp only [centeredMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, adjMatrix_apply, of_apply]
  by_cases huv : u = v
  · subst v
    simp only [ite_true, SimpleGraph.irrefl, ite_false]
    ring
  · simp only [huv, ite_false]
    split_ifs <;> ring

/-- Step `s44big` of Theorem 4.4 of [CGSS]: the small-degree case uses only
the positive definite symmetric-square Gram matrix. -/
theorem IsRepresentedIn.card_le_28_of_regular_of_two_mul_degree_add_four_le
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d)
    (hn : 2 * d + 4 ≤ Fintype.card V) : Fintype.card V ≤ 28 := by
  obtain ⟨q, hq⟩ := hX.exists_gram_centered h
  have hp := hX.posSemidef_two_add_adjMatrix_and_rank_le_eight.1
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ht : (0 : ℝ) ≤ 1 / 4 - ((d : ℝ) + 2) / (2 * Fintype.card V) := by
    have hn' : (2 : ℝ) * d + 4 ≤ Fintype.card V := by exact_mod_cast hn
    have hd := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Fintype.card V)).mpr
      (show (d : ℝ) + 2 ≤ 1 / 4 * (2 * Fintype.card V) by linarith)
    linarith
  have hJ : (of fun (_ : V) (_ : V) ↦ (1 : ℝ)).PosSemidef := by
    simpa [vecMulVec] using posSemidef_vecMulVec_self_star (fun _ : V ↦ (1 : ℝ))
  have hpd : (gram ℝ (fun u ↦ symSq (q u))).PosDef := by
    rw [gram_symSq_centered hq]
    exact ((PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 2)).add_posSemidef
      (hp.smul ht)).add_posSemidef (hJ.smul (sq_nonneg _))
  have hb := (linearIndependent_of_posDef_gram hpd).fintype_card_le_finrank
  have hc : Fintype.card (SymSqIndex 7) = 28 := by decide +kernel
  simpa only [finrank_euclideanSpace, hc] using hb

omit [Fintype V] [Nonempty V] in
/-- Step `s44equi` of Theorem 4.4 of [CGSS]: the equiangular factor has unit
norms and the two prescribed off-diagonal products. -/
theorem norm_eq_one_and_inner_eq_of_gram_eq_equiangularMatrix {w : V → EuclideanSpace ℝ (Fin 8)}
    (hw : gram ℝ w = X.equiangularMatrix) :
    (∀ u, ‖w u‖ = 1) ∧
      ∀ u v, u ≠ v → ⟪w u, w v⟫ = 1 / 3 ∨ ⟪w u, w v⟫ = -(1 / 3) := by
  have he (u v : V) : ⟪w u, w v⟫ = (X.equiangularMatrix) u v :=
    congrFun (congrFun hw u) v
  constructor
  · intro u
    have hu := he u u
    norm_num [equiangularMatrix, adjMatrix_apply, real_inner_self_eq_norm_sq] at hu
    rcases hu with hu | hu
    · exact hu
    · have := norm_nonneg (w u)
      linarith
  · intro u v huv
    rw [he]
    simp only [equiangularMatrix, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne huv, mul_zero, zero_add,
      adjMatrix_apply, of_apply, mul_one]
    split_ifs <;> norm_num

/-- Steps `s44equi`--`s44n` of Theorem 4.4 of [CGSS]: when the equiangular
matrix is positive on constants, EQ2 excludes rank eight for more than fourteen
vertices. Classification is required only in the nine-dimensional cone space. -/
theorem IsRepresentedIn.rank_le_seven_of_regular_of_classification
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d)
    (hn : Fintype.card V < 2 * d + 4) (hbig : 14 < Fintype.card V)
    (hclass : ∀ S : LineSystem (WithLp 2 (EuclideanSpace ℝ (Fin 8) × ℝ)),
      S.Φ.Nonempty → S.IsMaximal → S.IsIndecomposable →
      ∃ t : LineSystem.RootType, Nonempty (S.Iso t.model)) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ 7 := by
  obtain ⟨hp, hr⟩ := hX.posSemidef_two_add_adjMatrix_and_rank_le_eight
  have he := h.posSemidef_equiangular hp hn
  have her := h.rank_equiangular hp hn
  obtain ⟨w, hw⟩ := he.exists_gram_euclideanSpace (her.le.trans hr)
  obtain ⟨hw₁, hw₂⟩ := norm_eq_one_and_inner_eq_of_gram_eq_equiangularMatrix hw
  by_contra hnot
  have hr8 : X.equiangularMatrix.rank = 8 := by omega
  have hspan : span ℝ (Set.range w) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← rank_gram_eq_finrank_span, hw, hr8, finrank_euclideanSpace_fin]
  have hb := InnerProductSpace.card_le_fourteen_of_finrank_eq_eight_of_classification
    w hw₁ hw₂ hspan (finrank_euclideanSpace_fin) hclass
  omega

omit [Nonempty V] in
-- Theorem 4.4
/-- Theorem 4.4 of [CGSS], order bound, with the classification hypothesis of EQ2 explicit.
`IsRepresentedIn.card_le_28_of_regular` discharges it using Theorem 3.6. -/
theorem IsRepresentedIn.card_le_28_of_regular_of_classification
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d)
    (hclass : ∀ S : LineSystem (WithLp 2 (EuclideanSpace ℝ (Fin 8) × ℝ)),
      S.Φ.Nonempty → S.IsMaximal → S.IsIndecomposable →
      ∃ t : LineSystem.RootType, Nonempty (S.Iso t.model)) : Fintype.card V ≤ 28 := by
  by_cases hsmall : Fintype.card V ≤ 14
  · omega
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_cases hn : 2 * d + 4 ≤ Fintype.card V
  · exact hX.card_le_28_of_regular_of_two_mul_degree_add_four_le h hn
  have hlt : Fintype.card V < 2 * d + 4 := by omega
  obtain ⟨hp, _⟩ := hX.posSemidef_two_add_adjMatrix_and_rank_le_eight
  have hr := hX.rank_le_seven_of_regular_of_classification h hlt (by omega) hclass
  obtain ⟨w, hw⟩ := (h.posSemidef_equiangular hp hlt).exists_gram_euclideanSpace
    ((h.rank_equiangular hp hlt).le.trans (hr.trans (by omega : 7 ≤ 8)))
  obtain ⟨hw₁, hw₂⟩ := norm_eq_one_and_inner_eq_of_gram_eq_equiangularMatrix hw
  apply (InnerProductSpace.card_le_relativeBound w hw₁ hw₂ ?_).2
  rw [← rank_gram_eq_finrank_span, hw, h.rank_equiangular hp hlt]
  exact hr

/-- Lemma `lem:4-regmat`, step `s4rmMact`, for Theorem 4.4 of [CGSS]. -/
theorem IsRegularOfDegree.centered_mulVec_one (h : X.IsRegularOfDegree d) :
    X.centeredMatrix d *ᵥ (fun _ ↦ 1) = 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [centeredMatrix, sub_mulVec, smul_mulVec, h.gram_mulVec_one, smul_mulVec]
  ext u
  simp [mulVec, dotProduct]
  field_simp
  ring

/-- The diagonal count in step `s44trace` of Theorem 4.4 of [CGSS]. -/
theorem trace_centered (X : SimpleGraph V) [DecidableRel X.Adj] (d : ℕ) :
    (X.centeredMatrix d).trace = (Fintype.card V : ℝ) - ((d : ℝ) + 2) / 2 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centeredMatrix, trace, diag, adjMatrix_apply]
  field_simp

/-- Steps `s44bound`--`s44trace` of Theorem 4.4 of [CGSS]. The spectral
toolkit sums the seven possible nonzero eigenvalues of the centered matrix. -/
theorem IsRepresentedIn.centered_trace_bound_of_regular
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d)
    (hn : Fintype.card V < 2 * d + 4) :
    0 ≤ ((d : ℝ) - 2 * Fintype.card V + 16) +
      14 * (2 * Fintype.card V - 2 * d - 4) / (2 * d + 4 - Fintype.card V) := by
  let n : ℝ := Fintype.card V
  let t : ℝ := (d + 2) / (2 * n)
  have hnpos : 0 < n := by
    change (0 : ℝ) < Fintype.card V
    exact_mod_cast Fintype.card_pos
  have hden : 0 < (2 : ℝ) * d + 4 - n := by
    have : (Fintype.card V : ℝ) < 2 * d + 4 := by exact_mod_cast hn
    dsimp [n]
    linarith
  have ht : 0 < 4 * t - 1 := by
    dsimp [t]
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
      (show (1 / 4 : ℝ) * (2 * n) < d + 2 by linarith)
    linarith
  obtain ⟨hp, hr⟩ := hX.posSemidef_two_add_adjMatrix_and_rank_le_eight
  obtain ⟨q, hq⟩ := hX.exists_gram_centered h
  have hM := h.posSemidef_centered hp
  have hrow : X.centeredMatrix d *ᵥ (fun _ ↦ 1) = (0 : ℝ) • (fun _ ↦ 1) := by
    simpa using h.centered_mulVec_one
  let P := (1 / 2 - 2 * t) • X.centeredMatrix d + (1 / 2 : ℝ) • 1 +
    (t / 2 - t ^ 2) • (of fun (_ : V) (_ : V) ↦ (1 : ℝ))
  have hP : P.PosSemidef := by
    have he : gram ℝ (fun u ↦ symSq (q u)) = P := by
      rw [gram_symSq_centered hq]
      ext u v
      simp only [P, centeredMatrix, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul, of_apply]
      dsimp [t, n]
      ring
    rw [← he]
    exact posSemidef_gram ℝ _
  have hs := hM.isHermitian.spectrumMultiset_smul_add_smul_one_add_smul_allOnes
    hrow (1 / 2) (1 / 2 - 2 * t) (t / 2 - t ^ 2)
  have heig : ∀ μ ∈ (X.centeredMatrix d).spectrumMultiset, μ ≠ 0 →
      μ ≤ 1 / (4 * t - 1) := by
    intro μ hμ hne
    have hμ' := (Multiset.mem_erase_of_ne hne).mpr hμ
    have hmem : (1 / 2 + (1 / 2 - 2 * t) * μ) ∈ P.spectrumMultiset := by
      rw [hs]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_map.mpr ⟨μ, hμ', rfl⟩))
    have hnonneg := hP.isHermitian.posSemidef_iff_spectrumMultiset_nonneg.mp hP _ hmem
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have htr := hM.isHermitian.trace_le_rank_mul_of_eigenvalues_le heig
  have hr7 : ((X.centeredMatrix d).rank : ℝ) ≤ 7 := by
    have hmr := h.rank_centered hp
    exact_mod_cast (show (X.centeredMatrix d).rank ≤ 7 by omega)
  have htr7 := htr.trans (mul_le_mul_of_nonneg_right hr7 (le_of_lt (one_div_pos.mpr ht)))
  rw [trace_centered] at htr7
  have hfrac : 1 / (4 * t - 1) = n / (2 * d + 4 - n) := by
    apply (div_eq_div_iff ht.ne' hden.ne').mpr
    dsimp [t]
    field_simp
    ring
  rw [hfrac] at htr7
  have hclear := (le_div_iff₀ hden).mp
    (show n - ((d : ℝ) + 2) / 2 ≤ 7 * n / (2 * d + 4 - n) by
      simpa only [mul_div_assoc] using htr7)
  apply (le_of_mul_le_mul_right ?_ hden)
  rw [zero_mul, add_mul, div_mul_cancel₀ _ hden.ne']
  dsimp only [n] at hclear ⊢
  nlinarith

/-- Step `s44d` of Theorem 4.4 of [CGSS]: a rank-seven root Gram matrix
cannot belong to a 17-regular graph of order 28, by the same trace count as C24. -/
theorem not_regular_28_17_of_rank_le_seven (h : X.IsRegularOfDegree 17)
    (hn : Fintype.card V = 28)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hr : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ 7) : False := by
  have hM := h.posSemidef_centered hp
  have hmr : ((X.centeredMatrix 17).rank : ℝ) ≤ 6 := by
    have hh := h.rank_centered hp
    exact_mod_cast (show (X.centeredMatrix 17).rank ≤ 6 by omega)
  have he : X.centeredMatrix 17 = (1 : ℝ) • (1 : Matrix V V ℝ) +
      (1 / 2 : ℝ) • X.adjMatrix ℝ +
        (-(19 / 56) : ℝ) • (of fun _ _ ↦ (1 : ℝ)) := by
    ext u v
    simp only [centeredMatrix, hn, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, of_apply]
    norm_num
    split_ifs <;> ring
  have hs : (∑ u, ∑ v, (X.centeredMatrix 17) u v ^ 2) = 227 / 4 := by
    rw [he]
    simp_rw [Computations.C24.sum_sq_row, h.degree_eq]
    norm_num [hn]
  have ht := trace_centered X 17
  rw [hn] at ht
  have hb := hM.isHermitian.trace_sq_le_rank_mul_sum_entry_sq
  rw [ht, hs] at hb
  nlinarith

-- Theorem 4.4
/-- Theorem 4.4 of [CGSS], degree bound, with the classification needed by
EQ2 explicit. C8 leaves `(28,17)`, excluded by the rank-seven trace obstruction. -/
theorem IsRepresentedIn.degree_le_16_of_regular_of_classification
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d)
    (hclass : ∀ S : LineSystem (WithLp 2 (EuclideanSpace ℝ (Fin 8) × ℝ)),
      S.Φ.Nonempty → S.IsMaximal → S.IsIndecomposable →
      ∃ t : LineSystem.RootType, Nonempty (S.Iso t.model)) : d ≤ 16 := by
  have hn := hX.card_le_28_of_regular_of_classification h hclass
  have hd : d < Fintype.card V := by
    simpa only [h.degree_eq] using X.degree_lt_card_verts (Classical.arbitrary V)
  by_cases hsmall : Fintype.card V ≤ 17
  · omega
  by_cases hlt : Fintype.card V < 2 * d + 4
  · rcases Computations.C8.quadratic_bound (Fintype.card V) d hn (by omega) hlt
      (hX.centered_trace_bound_of_regular h hlt) with hb | ⟨hc, rfl⟩
    · exact hb
    · exact (not_regular_28_17_of_rank_le_seven h hc
        hX.posSemidef_two_add_adjMatrix_and_rank_le_eight.1
        (hX.rank_le_seven_of_regular_of_classification h hlt (by omega) hclass)).elim
  · omega

-- Remark after Theorem 4.4
/-- Remark after Theorem 4.4 of [CGSS], blueprint assertion 1 (`rem:4-after44`):
C24 forces rank eight, contrary to EQ2. Classification is an explicit hypothesis;
`not_regular_28_16_isRepresentedIn_E₈` discharges it using Theorem 3.6. -/
theorem not_regular_28_16_isRepresentedIn_E₈_of_classification
    (h : X.IsRegularOfDegree 16) (hn : Fintype.card V = 28)
    (hclass : ∀ S : LineSystem (WithLp 2 (EuclideanSpace ℝ (Fin 8) × ℝ)),
      S.Φ.Nonempty → S.IsMaximal → S.IsIndecomposable →
      ∃ t : LineSystem.RootType, Nonempty (S.Iso t.model)) :
    ¬ X.IsRepresentedIn LineSystem.E₈ := by
  intro hX
  obtain ⟨hp, _⟩ := hX.posSemidef_two_add_adjMatrix_and_rank_le_eight
  have hr := hX.rank_le_seven_of_regular_of_classification h
    (by omega) (by omega) hclass
  let N := (2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ -
    (9 / 14 : ℝ) • (of fun _ _ ↦ (1 : ℝ))
  have he : N = (2 : ℝ) • X.centeredMatrix 16 := by
    ext u v
    simp only [N, centeredMatrix, hn, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, of_apply]
    norm_num
    ring
  have hN : N.IsHermitian := by
    rw [he]
    exact (h.posSemidef_centered hp).isHermitian.smul (IsSelfAdjoint.all 2)
  have hrN : (N.rank : ℝ) ≤ 6 := by
    have hmr := h.rank_centered hp
    rw [he, rank_smul_of_mem_nonZeroDivisors _ (by norm_num)]
    exact_mod_cast (show (X.centeredMatrix 16).rank ≤ 6 by omega)
  obtain ⟨ht, hs, _⟩ := Computations.C24.trace_sq_gt h hn
  have hb := hN.trace_sq_le_rank_mul_sum_entry_sq
  change N.trace = 38 at ht
  change (∑ u, ∑ v, N u v ^ 2) = 236 at hs
  rw [ht, hs] at hb
  nlinarith

end SimpleGraph

namespace SimpleGraph

/-- Classical adjacency decisions for the examples attaining the bounds of Theorem 4.4. -/
noncomputable local instance decidableAdjExamples {I : Type*} (Y : SimpleGraph I) :
    DecidableRel Y.Adj :=
  Classical.decRel _

/-- Remark after Theorem 4.4 of [CGSS], blueprint assertion 2 (`rem:4-after44`):
`L(K₈)` and the three Chang graphs attain order 28 at degree 12; the Schläfli
graph attains degree 16 at order 27. -/
theorem regular_28_12_and_27_16_isRepresentedIn_E₈ :
    (Fintype.card (⊤ : SimpleGraph (Fin 8)).edgeSet = 28 ∧
      (⊤ : SimpleGraph (Fin 8)).lineGraph.IsRegularOfDegree 12 ∧
      (⊤ : SimpleGraph (Fin 8)).lineGraph.IsRepresentedIn LineSystem.E₈) ∧
    (changI.IsRegularOfDegree 12 ∧ changI.IsRepresentedIn LineSystem.E₈) ∧
    (changII.IsRegularOfDegree 12 ∧ changII.IsRepresentedIn LineSystem.E₈) ∧
    (changIII.IsRegularOfDegree 12 ∧ changIII.IsRepresentedIn LineSystem.E₈) ∧
    (schlafli.IsRegularOfDegree 16 ∧ schlafli.IsRepresentedIn LineSystem.E₈) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨changI_isSRGWith.regular, changI_isRepresentedIn_E₈⟩,
    ⟨changII_isSRGWith.regular, changII_isRepresentedIn_E₈⟩,
    ⟨changIII_isSRGWith.regular, changIII_isRepresentedIn_E₈⟩,
    ⟨schlafli_isSRGWith.regular, schlafli_isRepresentedIn_E₈⟩⟩
  · rw [card_edgeSet, card_edgeFinset_top_eq_card_choose_two]
    decide
  · intro u
    rcases u with ⟨⟨i, j⟩, hij⟩
    have hd := (⊤ : SimpleGraph (Fin 8)).lineGraph_degree_mk
      ((⊤ : SimpleGraph (Fin 8)).mem_edgeSet.mp hij)
    have h7 (k : Fin 8) : (⊤ : SimpleGraph (Fin 8)).degree k = 7 := by
      convert complete_graph_degree k using 1; simp
    rw [h7, h7] at hd
    convert (show (⊤ : SimpleGraph (Fin 8)).lineGraph.degree ⟨s(i, j), hij⟩ = 12 by omega)
  · refine ⟨(⊤ : SimpleGraph (Fin 8)).lineGraphVector,
      (⊤ : SimpleGraph (Fin 8)).lineGraph_isRepresentation, ?_⟩
    rintro ⟨⟨i, j⟩, hij⟩
    rw [(⊤ : SimpleGraph (Fin 8)).lineGraphVector_mk hij]
    exact LineSystem.Dn_Φ_subset_E₈
      (LineSystem.add_single_mem_Dn i j ((⊤ : SimpleGraph (Fin 8)).mem_edgeSet.mp hij).ne)

end SimpleGraph
