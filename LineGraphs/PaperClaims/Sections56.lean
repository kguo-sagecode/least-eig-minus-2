/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.ExceptionalParameters
import LineGraphs.Computations.C14
import LineGraphs.Computations.C13Seidel
import LineGraphs.Spectral.Gram
import LineGraphs.Hadamard.FourthRows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Small claims of Sections 5 and 6 of [CGSS]

Claims that the paper makes in passing, in the remarks of Section 5, in the proof of
Corollary 5.10 and in the discussion after Hypothesis 6.1, and that had no Lean statement of their
own (found by the statement audit, `LineGraphs/AUDIT-statements.md`). Page references are to
[CGSS], J. Algebra 43 (1976), 305–327.

## Main definitions

* `Computations.C13.equiangularGram G`: the matrix `I + (1/3)(2A - J + I)` of a graph, that is,
  `I - S/3` for the Seidel matrix `S = J - I - 2A`.

## Main statements

* `Design.v_le_four_of_add_le_nine`, `Design.v_le_four_of_le_of_add_le_nine`: the remark after
  Theorem 5.8 (p. 324), "(i) holds only if `v ≤ 4`".
* `Design.NonbipartiteParameters.lam_eq_two_and_odd_of_t_eq_one`: Remark 5.12 (p. 325),
  "for `t = 1` we have `λ = 2` and `s` odd".
* `Design.NonbipartiteParameters.sub_one_le_of_one_lt`,
  `Design.NonbipartiteParameters.finite_setOf_s`: Remark 5.12 (p. 325), "for any `t > 1` there
  are finitely many possible values for `s`".
* `Computations.C13.same_equiangular_lines`: Corollary 5.10 (p. 324), the two graphs of C13
  "represent the same set of 12 equiangular lines in `ℝ⁶`". Its ingredients are
  `Computations.C13.posSemidef_equiangularGram_graph1` and `rank_equiangularGram_graph1` (the
  Gram matrix `I + (1/3)(2A - J + I)` is positive semidefinite of rank 6, from the spectrum
  `5³, 1³, (-3)⁶` of `2A - J + I`), the same for the second graph, and
  `Computations.C13.equiangularGram_isSwitchingEquivalent` (the switching of
  `Computations.C13.switching_equivalent` conjugates the two Gram matrices by a relabelling and a
  diagonal `±1` matrix); `Computations.C13.ncard_equiangular_lines` counts the lines and
  `Computations.C13.line_angle_of_gram_eq` gives the angle `arccos (1/3)`.
* `Matrix.IsHadamard.FourRowAgreement.line_angles`,
  `Matrix.IsHadamard.FourRowAgreement.lines_mem_hyperplane`: Section 6 (p. 326), "we have
  `½n(n-1)` lines in `ℝⁿ` with angles `90°` and `arccos 1/d`, which lie in a subspace of dimension
  `n - 1`", under Hypothesis 6.1, with `d = n/x`;
  `Matrix.IsHadamard.FourRowAgreement.exists_line_angles`: both angles occur when `n ≥ 3`.
-/

namespace Design

section RemarkAfterTheorem58

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ}

-- Remark after Theorem 5.8
/-- The remark after Theorem 5.8 of [CGSS] (p. 324): "we can assume that (i) holds only if
`v ≤ 4`". Alternative (i) of Theorem 5.8 (`Design.flagGraph_cospectral`) gives `v + b ≤ 9`, and
when `λ < r` Fisher's inequality `v ≤ b` (`Design.v_le_b_of_lam_lt_r`) leaves `v ≤ 4`. When
`λ = r`, every block is the whole point set and the paper passes to the dual design; in Lean this
is the hypothesis `v ≤ b` of `Design.flagGraph_cospectral`, with which the bound is
`Design.v_le_four_of_le_of_add_le_nine`. -/
theorem v_le_four_of_add_le_nine (D : Design P B v k b r lam) (hlr : lam < r)
    (h : v + b ≤ 9) : v ≤ 4 := by
  have := D.v_le_b_of_lam_lt_r hlr
  omega

/-- The remark after Theorem 5.8 of [CGSS] (p. 324), under the hypothesis `v ≤ b` of
`Design.flagGraph_cospectral` (Error 16): alternative (i), `v + b ≤ 9`, holds only if `v ≤ 4`. -/
theorem v_le_four_of_le_of_add_le_nine (_D : Design P B v k b r lam) (hvb : v ≤ b)
    (h : v + b ≤ 9) : v ≤ 4 := by
  omega

end RemarkAfterTheorem58

namespace NonbipartiteParameters

variable {v k b r lam s t : ℕ}

-- Remark 5.12
/-- Remark 5.12 of [CGSS] (p. 325): "In Theorem 5.8, case (iii), for `t = 1` we have
`λ = 2` and `s` odd". The parameters and the parity `Even (t * (s + 1))` are those of case (iii)
of `Design.flagGraph_cospectral`; `λ = 2` is `Computations.C14.lambda_eq_two`. -/
theorem lam_eq_two_and_odd_of_t_eq_one (h : NonbipartiteParameters v k b r lam s t)
    (heven : Even (t * (s + 1))) (ht : t = 1) : lam = 2 ∧ Odd s := by
  subst ht
  have hs : (2 : ℤ) ≤ s := by exact_mod_cast h.two_le_s
  refine ⟨?_, ?_⟩
  · have hl := Computations.C14.lambda_eq_two s lam hs
      (by linear_combination h.pair_count)
    exact_mod_cast hl
  · rw [one_mul] at heven
    exact Nat.odd_iff.mpr (by rcases heven with ⟨m, hm⟩; omega)

/-- Remark 5.12 of [CGSS] (p. 325), the bound behind "for any `t > 1` there are finitely
many possible values for `s`": `s - 1` divides `2t(t - 1)`, which is positive. -/
theorem sub_one_le_of_one_lt (h : NonbipartiteParameters v k b r lam s t) (ht : 1 < t) :
    (s : ℤ) - 1 ≤ 2 * t * (t - 1) := by
  have htZ : (1 : ℤ) < t := by exact_mod_cast ht
  have hpos : (0 : ℤ) < 2 * t * (t - 1) := by
    have : (0 : ℤ) < t - 1 := by omega
    positivity
  exact Int.le_of_dvd hpos h.dvd

/-- Remark 5.12 of [CGSS] (p. 325): "for any `t > 1` there are finitely many possible
values for `s`" in case (iii) of Theorem 5.8. -/
theorem finite_setOf_s (ht : 1 < t) :
    {s : ℕ | ∃ v k b r lam : ℕ, NonbipartiteParameters v k b r lam s t}.Finite := by
  apply (Set.finite_Iic (2 * t * t)).subset
  rintro s ⟨v, k, b, r, lam, h⟩
  have hle := h.sub_one_le_of_one_lt ht
  have hle' : (s : ℤ) ≤ 2 * t * t := by nlinarith
  exact_mod_cast hle'

end NonbipartiteParameters

end Design

namespace Computations.C13

open Matrix
open scoped RealInnerProductSpace

section EquiangularGram

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- C13, [CGSS] Corollary 5.10 (p. 324): the Gram matrix `I + (1/3)(2A - J + I)` of the
equiangular lines at angle `arccos (1/3)` given by the `(±1)` adjacency matrix `2A - J + I` of a
graph. -/
noncomputable def equiangularGram (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  1 + (1 / 3 : ℝ) • ((2 : ℝ) • G.adjMatrix ℝ - Matrix.of (fun _ _ ↦ (1 : ℝ)) + 1)

/-- C13, [CGSS] Corollary 5.10: `I + (1/3)(2A - J + I) = I - S/3` for the Seidel matrix
`S = J - I - 2A`. -/
theorem equiangularGram_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    equiangularGram G = (1 : ℝ) • (1 : Matrix V V ℝ) + (-(1 / 3) : ℝ) • G.seidelMatrix := by
  rw [equiangularGram, SimpleGraph.seidelMatrix]
  module

/-- C13, [CGSS] Corollary 5.10: the diagonal entries of `I + (1/3)(2A - J + I)` are `1`. -/
theorem equiangularGram_apply_self (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    equiangularGram G i i = 1 := by
  simp [equiangularGram]

/-- C13, [CGSS] Corollary 5.10: the off-diagonal entries of `I + (1/3)(2A - J + I)` are `±1/3`. -/
theorem abs_equiangularGram_apply_of_ne (G : SimpleGraph V) [DecidableRel G.Adj] {i j : V}
    (hij : i ≠ j) : |equiangularGram G i j| = 1 / 3 := by
  by_cases h : G.Adj i j <;> norm_num [equiangularGram, hij, h]

/-- C13, [CGSS] Corollary 5.10: Seidel switching conjugates the Gram matrices
`I + (1/3)(2A - J + I)` by the same relabelling and signs. -/
theorem equiangularGram_apply_of_switching {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) (d : V → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hS : ∀ i j, G.seidelMatrix i j = d i * d j * H.seidelMatrix (e i) (e j)) (i j : V) :
    equiangularGram G i j = d i * d j * equiangularGram H (e i) (e j) := by
  rw [equiangularGram_eq, equiangularGram_eq]
  by_cases hij : i = j
  · subst hij
    have hd2 : d i * d i = 1 := by rcases hd i with h | h <;> rw [h] <;> norm_num
    simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, hS i i]
    linear_combination (-1 : ℝ) * hd2
  · have he : e i ≠ e j := e.injective.ne hij
    simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_ne hij, one_apply_ne he,
      smul_eq_mul, hS i j]
    ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- C13, [CGSS] Corollary 5.10: switching a realization of `I + (1/3)(2A - J + I)` realizes the
Gram matrix of the switched graph. -/
theorem gram_smul_comp_of_switching {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) (d : V → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (hS : ∀ i j, G.seidelMatrix i j = d i * d j * H.seidelMatrix (e i) (e j))
    (y : W → E) (hy : gram ℝ y = equiangularGram H) :
    gram ℝ (fun i ↦ d i • y (e i)) = equiangularGram G := by
  ext i j
  rw [gram_apply, real_inner_smul_left, real_inner_smul_right,
    equiangularGram_apply_of_switching e d hd hS i j, ← hy, gram_apply]
  ring

/-- C13, [CGSS] Corollary 5.10: Seidel switching equivalent graphs have Gram matrices
`I + (1/3)(2A - J + I)` that are conjugate by a relabelling and a diagonal `±1` matrix. -/
theorem isSwitchingEquivalent_equiangularGram [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G.IsSwitchingEquivalent H) :
    (equiangularGram G).IsSwitchingEquivalent (equiangularGram H) := by
  obtain ⟨e, d, hd, hS⟩ := h
  exact ⟨e, d, hd, equiangularGram_apply_of_switching e d hd hS⟩

omit [DecidableEq V] [DecidableEq W] in
/-- C13, [CGSS] Corollary 5.10: changing signs and relabelling does not change the set of lines. -/
theorem range_span_smul_comp (e : V ≃ W) (d : V → ℝ) (hd : ∀ i, d i = 1 ∨ d i = -1)
    (y : W → E) :
    Set.range (fun i ↦ ℝ ∙ (d i • y (e i))) = Set.range (fun j ↦ ℝ ∙ y j) := by
  have h (i : V) : (ℝ ∙ (d i • y (e i))) = ℝ ∙ y (e i) :=
    Submodule.span_singleton_smul_eq
      (isUnit_iff_ne_zero.mpr (by rcases hd i with h | h <;> rw [h] <;> norm_num)) _
  simp only [h]
  exact e.surjective.range_comp (fun j ↦ ℝ ∙ y j)

/-- C13, [CGSS] Corollary 5.10: vectors with Gram matrix `I + (1/3)(2A - J + I)` are unit
vectors with inner products `±1/3`, and they span distinct lines. -/
theorem equiangular_of_gram_eq {G : SimpleGraph V} [DecidableRel G.Adj] (x : V → E)
    (hx : gram ℝ x = equiangularGram G) :
    (∀ i, ‖x i‖ = 1) ∧ (∀ i j, i ≠ j → |⟪x i, x j⟫| = 1 / 3) ∧
      Function.Injective (fun i ↦ ℝ ∙ x i) := by
  have hg (i j : V) : ⟪x i, x j⟫ = equiangularGram G i j := by rw [← hx, gram_apply]
  have hii (i : V) : ⟪x i, x i⟫ = 1 := by rw [hg, equiangularGram_apply_self]
  have hij (i j : V) (h : i ≠ j) : |⟪x i, x j⟫| = 1 / 3 := by
    rw [hg, abs_equiangularGram_apply_of_ne G h]
  refine ⟨fun i ↦ by rw [norm_eq_sqrt_real_inner, hii, Real.sqrt_one], hij, ?_⟩
  intro i j he
  dsimp only at he
  by_contra hne
  have hj : x j ∈ ℝ ∙ x i := by
    rw [he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hj
  have hnorm := hii j
  have hinner := hij i j hne
  rw [← hc, real_inner_smul_left, real_inner_smul_right, hii] at hnorm
  rw [← hc, real_inner_smul_right, hii, mul_one] at hinner
  nlinarith [abs_mul_abs_self c]

/-- C13, [CGSS] Corollary 5.10: vectors with Gram matrix `I + (1/3)(2A - J + I)` span equiangular
lines, any two of which meet at `arccos (1/3)`. -/
theorem line_angle_of_gram_eq {G : SimpleGraph V} [DecidableRel G.Adj] (x : V → E)
    (hx : gram ℝ x = equiangularGram G) {i j : V} (hij : i ≠ j) :
    Real.arccos (|⟪x i, x j⟫| / (‖x i‖ * ‖x j‖)) = Real.arccos (1 / 3) := by
  obtain ⟨hn, hi, -⟩ := equiangular_of_gram_eq x hx
  rw [hn, hn, hi i j hij, mul_one, div_one]

end EquiangularGram

/-- C13, [CGSS] Corollary 5.10: the Seidel matrix of the first graph is symmetric. -/
theorem isHermitian_seidelMatrix_graph1 : graph1.seidelMatrix.IsHermitian := by
  rw [seidelMatrix_graphOfMatrix]
  apply checkSymmetric_sound
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: the Seidel matrix of the second graph is symmetric. -/
theorem isHermitian_seidelMatrix_graph2 : graph2.seidelMatrix.IsHermitian := by
  rw [seidelMatrix_graphOfMatrix]
  apply checkSymmetric_sound
  decide +kernel

/-- C13, [CGSS] Corollary 5.10: from the Seidel spectrum `5³, 1³, (-3)⁶` of `2A - J + I`, the
Gram matrix `I + (1/3)(2A - J + I)` of the first graph has spectrum `(8/3)³, (4/3)³, 0⁶`. -/
theorem spectrumMultiset_equiangularGram_graph1 :
    (equiangularGram graph1).spectrumMultiset =
      (([(8 / 3, 3), (4 / 3, 3), (0, 6)] : List (ℝ × ℕ)).map
        fun x ↦ Multiset.replicate x.2 x.1).sum := by
  rw [equiangularGram_eq, isHermitian_seidelMatrix_graph1.spectrumMultiset_smul_one_add_smul,
    seidel_spectrum_graph1]
  norm_num [seidelSpectralData, Multiset.map_add, Multiset.map_replicate]

/-- C13, [CGSS] Corollary 5.10: the Gram matrix `I + (1/3)(2A - J + I)` of the second graph has
spectrum `(8/3)³, (4/3)³, 0⁶`. -/
theorem spectrumMultiset_equiangularGram_graph2 :
    (equiangularGram graph2).spectrumMultiset =
      (([(8 / 3, 3), (4 / 3, 3), (0, 6)] : List (ℝ × ℕ)).map
        fun x ↦ Multiset.replicate x.2 x.1).sum := by
  rw [equiangularGram_eq, isHermitian_seidelMatrix_graph2.spectrumMultiset_smul_one_add_smul,
    seidel_spectrum_graph2]
  norm_num [seidelSpectralData, Multiset.map_add, Multiset.map_replicate]

/-- C13, [CGSS] Corollary 5.10: the Gram matrix of the first graph is positive semidefinite. -/
theorem posSemidef_equiangularGram_graph1 : (equiangularGram graph1).PosSemidef := by
  have hH : (equiangularGram graph1).IsHermitian := by
    rw [equiangularGram_eq]
    exact isHermitian_seidelMatrix_graph1.smul_one_add_smul _ _
  rw [hH.posSemidef_iff_spectrumMultiset_nonneg, spectrumMultiset_equiangularGram_graph1]
  intro μ hμ
  have h : μ = 0 ∨ μ = 4 / 3 ∨ μ = 8 / 3 ∨ μ = 0 := by simpa [Multiset.mem_replicate] using hμ
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

/-- C13, [CGSS] Corollary 5.10: the Gram matrix of the second graph is positive semidefinite. -/
theorem posSemidef_equiangularGram_graph2 : (equiangularGram graph2).PosSemidef := by
  have hH : (equiangularGram graph2).IsHermitian := by
    rw [equiangularGram_eq]
    exact isHermitian_seidelMatrix_graph2.smul_one_add_smul _ _
  rw [hH.posSemidef_iff_spectrumMultiset_nonneg, spectrumMultiset_equiangularGram_graph2]
  intro μ hμ
  have h : μ = 0 ∨ μ = 4 / 3 ∨ μ = 8 / 3 ∨ μ = 0 := by simpa [Multiset.mem_replicate] using hμ
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

/-- C13, [CGSS] Corollary 5.10: the Gram matrix of the first graph has rank 6. -/
theorem rank_equiangularGram_graph1 : (equiangularGram graph1).rank = 6 := by
  have hH : (equiangularGram graph1).IsHermitian := posSemidef_equiangularGram_graph1.isHermitian
  rw [hH.rank_eq_card_sub_eigenvalueMultiplicity_zero]
  change Fintype.card (Fin 12) - Multiset.count 0 (equiangularGram graph1).spectrumMultiset = 6
  rw [spectrumMultiset_equiangularGram_graph1]
  norm_num [Multiset.count_replicate]

/-- C13, [CGSS] Corollary 5.10: the Gram matrix of the second graph has rank 6. -/
theorem rank_equiangularGram_graph2 : (equiangularGram graph2).rank = 6 := by
  have hH : (equiangularGram graph2).IsHermitian := posSemidef_equiangularGram_graph2.isHermitian
  rw [hH.rank_eq_card_sub_eigenvalueMultiplicity_zero]
  change Fintype.card (Fin 12) - Multiset.count 0 (equiangularGram graph2).spectrumMultiset = 6
  rw [spectrumMultiset_equiangularGram_graph2]
  norm_num [Multiset.count_replicate]

/-- C13, [CGSS] Corollary 5.10 (p. 324): the Gram matrices `I + (1/3)(2A - J + I)` of the
two graphs are conjugate by a relabelling and a diagonal `±1` matrix, by `switching_equivalent`. -/
theorem equiangularGram_isSwitchingEquivalent :
    (equiangularGram graph1).IsSwitchingEquivalent (equiangularGram graph2) :=
  isSwitchingEquivalent_equiangularGram switching_equivalent

-- Corollary 5.10
/-- C13, Corollary 5.10 of [CGSS] (p. 324): "The graphs are switching equivalent and
represent the same set of 12 equiangular lines in `ℝ⁶`." There are unit vectors `x i` and `y i`
in `ℝ⁶` with Gram matrices `I + (1/3)(2A - J + I)` for the first and the second graph; they span
the same set of lines, twelve distinct lines with angle `arccos (1/3)`, and they span `ℝ⁶`. The
vectors `x i` are `±y (e i)`, by the switching of `switching_equivalent`. -/
theorem same_equiangular_lines :
    ∃ x y : Fin 12 → EuclideanSpace ℝ (Fin 6),
      gram ℝ x = equiangularGram graph1 ∧ gram ℝ y = equiangularGram graph2 ∧
      Set.range (fun i ↦ ℝ ∙ x i) = Set.range (fun i ↦ ℝ ∙ y i) ∧
      (∀ i, ‖x i‖ = 1) ∧ (∀ i j, i ≠ j → |⟪x i, x j⟫| = 1 / 3) ∧
      Function.Injective (fun i ↦ ℝ ∙ x i) ∧ Submodule.span ℝ (Set.range x) = ⊤ := by
  obtain ⟨y, hy⟩ := posSemidef_equiangularGram_graph2.exists_gram_euclideanSpace
    (r := 6) rank_equiangularGram_graph2.le
  obtain ⟨e, d, hd, hS⟩ := switching_equivalent
  have hx := gram_smul_comp_of_switching e d hd hS y hy
  obtain ⟨hn, hi, hinj⟩ := equiangular_of_gram_eq _ hx
  refine ⟨_, y, hx, hy, range_span_smul_comp e d hd y, hn, hi, hinj, ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [← rank_gram_eq_finrank_span, hx, rank_equiangularGram_graph1, finrank_euclideanSpace_fin]

/-- C13, [CGSS] Corollary 5.10 (p. 324): the common line set has exactly 12 lines. -/
theorem ncard_equiangular_lines (x : Fin 12 → EuclideanSpace ℝ (Fin 6))
    (hx : gram ℝ x = equiangularGram graph1) :
    (Set.range fun i ↦ ℝ ∙ x i).ncard = 12 := by
  rw [Set.ncard_range_of_injective (equiangular_of_gram_eq x hx).2.2]
  simp

end Computations.C13

namespace Matrix.IsHadamard

open scoped RealInnerProductSpace
open Submodule

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)

-- Section 6, the lines of Hypothesis 6.1
/-- [CGSS], Section 6 (p. 326), the angle form of "lines in `ℝⁿ` with angles `90°` and
`arccos 1/d`": under Hypothesis 6.1 with parameter `x`, the lines spanned by the products
`p_{ij}` of two rows of `H`, for distinct pairs of rows, meet at `90°` or at `arccos (1/d)`, where
`d = n/x` (p. 326). The absolute value makes the angle independent of the signs of the
representatives. For `x = 0`, `1/d` is `0` in Lean and both angles are `90°`. The general form of
`Computations.C16.h12_line_angles`, from `inner_hadamardPairs_self` and
`FourRowAgreement.inner_hadamardPairs_mem`. -/
theorem FourRowAgreement.line_angles {x : ℕ} (ha : hH.FourRowAgreement x)
    (p q : HadamardPair n) (hpq : p ≠ q) :
    Real.arccos (|⟪H.hadamardRowProduct p.1.1 p.1.2, H.hadamardRowProduct q.1.1 q.1.2⟫| /
      (‖H.hadamardRowProduct p.1.1 p.1.2‖ * ‖H.hadamardRowProduct q.1.1 q.1.2‖)) ∈
      ({Real.pi / 2, Real.arccos (1 / ((n : ℝ) / x))} : Set ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast p.1.1.pos
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hH.inner_hadamardPairs_self,
    hH.inner_hadamardPairs_self, Real.mul_self_sqrt hn.le, one_div_div]
  have hh := ha.inner_hadamardPairs_mem hH p q hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
  rcases hh with hh | hh | hh
  · left
    rw [hh, abs_zero, zero_div, Real.arccos_zero]
  · right
    rw [hh, abs_neg, Nat.abs_cast]
  · right
    rw [hh, Nat.abs_cast]

-- Section 6, the lines of Hypothesis 6.1
/-- [CGSS], Section 6 (p. 326): "we have `½n(n-1)` lines in `ℝⁿ` with angles `90°` and
`arccos 1/d`, which lie in a subspace of dimension `n - 1`". Under Hypothesis 6.1 with parameter
`x`, the `½n(n-1)` pairs of rows give vectors `p_{ij}` in `jᗮ`, a subspace of dimension `n - 1`,
and the lines of two distinct pairs meet at `90°` or at `arccos (1/d)`, `d = n/x`. As in the
paper, the count is with multiplicity: for `d = 1` the lines coincide in groups of `½n`. -/
theorem FourRowAgreement.lines_mem_hyperplane {x : ℕ} (ha : hH.FourRowAgreement x)
    (hn : 0 < n) :
    Fintype.card (HadamardPair n) = n * (n - 1) / 2 ∧
      (∀ p : HadamardPair n, H.hadamardRowProduct p.1.1 p.1.2 ∈
        (ℝ ∙ WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)))ᗮ) ∧
      Module.finrank ℝ (ℝ ∙ WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)))ᗮ = n - 1 ∧
      ∀ p q : HadamardPair n, p ≠ q →
        Real.arccos (|⟪H.hadamardRowProduct p.1.1 p.1.2, H.hadamardRowProduct q.1.1 q.1.2⟫| /
          (‖H.hadamardRowProduct p.1.1 p.1.2‖ * ‖H.hadamardRowProduct q.1.1 q.1.2‖)) ∈
          ({Real.pi / 2, Real.arccos (1 / ((n : ℝ) / x))} : Set ℝ) :=
  ⟨by rw [card_hadamardPair, Nat.choose_two_right],
    fun p ↦ mem_orthogonal_singleton_iff_inner_left.mpr
      (hH.inner_hadamardPairs_one p.1.1 p.1.2 p.2.ne),
    hH.finrank_hadamardPairs_fixedRow ⟨0, hn⟩,
    ha.line_angles hH⟩

-- Section 6, the lines of Hypothesis 6.1
/-- [CGSS], Section 6 (p. 326): both angles `90°` and `arccos (1/d)` occur when `n ≥ 3`.
Two pairs of rows with one common row give `90°` (`inner_hadamardRowProduct_of_ne`). For
`arccos (1/d)`, fix three distinct rows `i, k, l`; Parseval (`sum_sq_inner_hadamardPairs`) gives
`∑ⱼ ⟪p_{ij}, p_{kl}⟫² = n²`, so some `⟪p_{ij}, p_{kl}⟫` is nonzero, which forces `j` to differ from
`i, k, l`, and Hypothesis 6.1 then gives `|⟪p_{ij}, p_{kl}⟫| = x`. -/
theorem FourRowAgreement.exists_line_angles {x : ℕ} (ha : hH.FourRowAgreement x)
    (hn : 3 ≤ n) :
    (∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      Real.arccos (|⟪H.hadamardRowProduct i j, H.hadamardRowProduct i k⟫| /
        (‖H.hadamardRowProduct i j‖ * ‖H.hadamardRowProduct i k‖)) = Real.pi / 2) ∧
    ∃ i j k l : Fin n, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      Real.arccos (|⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫| /
        (‖H.hadamardRowProduct i j‖ * ‖H.hadamardRowProduct k l‖)) =
        Real.arccos (1 / ((n : ℝ) / x)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnorm (a b : Fin n) : ‖H.hadamardRowProduct a b‖ = Real.sqrt n := by
    rw [norm_eq_sqrt_real_inner, hH.inner_hadamardPairs_self]
  have hcard : 2 < Fintype.card (Fin n) := by simpa using (show 2 < n by omega)
  obtain ⟨i, k, l, hik, hil, hkl⟩ := Fintype.two_lt_card_iff.mp hcard
  refine ⟨⟨i, k, l, hik, hil, hkl, ?_⟩, ?_⟩
  · rw [hH.inner_hadamardRowProduct_of_ne i k l hkl, abs_zero, zero_div, Real.arccos_zero]
  have hsum := hH.sum_sq_inner_hadamardPairs i k l
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [hsum]; positivity :
      (∑ j, ⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫ ^ 2) ≠ 0)
  have hj' : ⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫ ≠ 0 :=
    fun h ↦ hj (by rw [h]; ring)
  have hij : i ≠ j := by
    rintro rfl
    apply hj'
    rw [hH.hadamardRowProduct_self, real_inner_comm]
    exact hH.inner_hadamardPairs_one k l hkl
  have hjk : j ≠ k := by
    rintro rfl
    apply hj'
    rw [hadamardRowProduct_comm H i j]
    exact hH.inner_hadamardRowProduct_of_ne j i l hil
  have hjl : j ≠ l := by
    rintro rfl
    apply hj'
    rw [hadamardRowProduct_comm H i j, hadamardRowProduct_comm H k j]
    exact hH.inner_hadamardRowProduct_of_ne j i k hik
  have habs : |⟪H.hadamardRowProduct i j, H.hadamardRowProduct k l⟫| = x := by
    have hd := hH.inner_hadamardPairs_of_disjoint i j k l hij hik hil hjk hjl hkl
    have hm := ha i j k l hij hik hil hjk hjl hkl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm | hm
    · exact absurd (by rw [hd]; exact_mod_cast (sub_eq_zero.mpr hm)) hj'
    · have hm' : (8 * (H.fourRowAgreeCount i j k l : ℝ)) = n - x := by exact_mod_cast hm
      rw [hd, hm', sub_sub_cancel_left, abs_neg, Nat.abs_cast]
    · have hm' : (8 * (H.fourRowAgreeCount i j k l : ℝ)) = n + x := by exact_mod_cast hm
      rw [hd, hm', add_sub_cancel_left, Nat.abs_cast]
  refine ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, ?_⟩
  rw [habs, hnorm, hnorm, Real.mul_self_sqrt hnpos.le, one_div_div]

end Matrix.IsHadamard

