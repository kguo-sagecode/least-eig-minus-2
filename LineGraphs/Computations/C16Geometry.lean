/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C16Order12
import LineGraphs.Hadamard.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# C16: the 66 lines from the Paley matrix of order 12

Blueprint Lemma `lem:6-gram` gives squared norm 12 and membership in `jᗮ` for the row products.
The Boolean agreement check gives off-diagonal products `0, ±4`; normalization gives squared
norm two and products `0, ±2/3`. Thus these are 66 distinct lines at the claimed acute angles.
They are not a `LineSystem` in the Section 2 sense, whose permitted angles are 60° and 90°.
-/

open scoped RealInnerProductSpace
open Matrix Submodule

namespace Computations.C16

/-- C16: blueprint Lemma `lem:6-gram` gives squared norm 12 for each pair product. -/
theorem h12_inner_self (p : HadamardPair 12) :
    ⟪h12.hadamardRowProduct p.1.1 p.1.2, h12.hadamardRowProduct p.1.1 p.1.2⟫ = 12 :=
  h12_isHadamard.inner_hadamardPairs_self p.1.1 p.1.2

/-- C16: the agreement checker and blueprint Lemma `lem:6-gram` give `0, ±4` off diagonal. -/
theorem h12_inner_mem (p q : HadamardPair 12) (hpq : p ≠ q) :
    ⟪h12.hadamardRowProduct p.1.1 p.1.2, h12.hadamardRowProduct q.1.1 q.1.2⟫ ∈
      ({0, -4, 4} : Set ℝ) :=
  h12_fourRowAgreement.inner_hadamardPairs_mem h12_isHadamard p q hpq

/-- C16: the normalized roots have squared norm two. -/
theorem h12_root_inner_self (p : HadamardPair 12) :
    ⟪h12.hadamardRoot p, h12.hadamardRoot p⟫ = 2 :=
  h12_isHadamard.inner_hadamardRoot_self (by decide) p

/-- C16: the normalized off-diagonal inner products are `0, ±2/3`. -/
theorem h12_root_inner_mem (p q : HadamardPair 12) (hpq : p ≠ q) :
    ⟪h12.hadamardRoot p, h12.hadamardRoot q⟫ ∈ ({0, -(2 / 3), 2 / 3} : Set ℝ) := by
  rw [inner_hadamardRoot]
  have hh := h12_inner_mem p q hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with hh | hh | hh <;> norm_num [hh]

/-- C16: the hyperplane containing the 66 lines. -/
noncomputable abbrev h12Hyperplane :=
  (ℝ ∙ WithLp.toLp 2 (fun _ : Fin 12 ↦ (1 : ℝ)))ᗮ

/-- C16: blueprint Lemma `lem:6-gram`, part 4, places the roots in `jᗮ`. -/
theorem h12_root_mem_hyperplane (p : HadamardPair 12) : h12.hadamardRoot p ∈ h12Hyperplane :=
  mem_orthogonal_singleton_iff_inner_left.mpr (h12_isHadamard.inner_hadamardRoot_one p)

/-- C16: the containing hyperplane has dimension 11, by blueprint Lemma `lem:6-fixedrow`. -/
theorem h12_hyperplane_finrank : Module.finrank ℝ h12Hyperplane = 11 :=
  h12_isHadamard.finrank_hadamardPairs_fixedRow 0

/-- C16: an isometry `jᗮ ≃ ℝ¹¹`, so the ambient dimension claim preserves all angles. -/
noncomputable def h12HyperplaneIsometry : h12Hyperplane ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 11) :=
  ((stdOrthonormalBasis ℝ h12Hyperplane).reindex (finCongr h12_hyperplane_finrank)).repr

/-- C16: distinct pairs give distinct one-dimensional subspaces, not merely distinct vectors. -/
theorem h12_lines_injective :
    Function.Injective (fun p : HadamardPair 12 ↦ ℝ ∙ h12.hadamardRoot p) := by
  intro p q he
  dsimp only at he
  by_contra hpq
  have hq : h12.hadamardRoot q ∈ ℝ ∙ h12.hadamardRoot p := by
    rw [he]
    exact mem_span_singleton_self _
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hq
  have hnorm := h12_root_inner_self q
  have hinner := h12_root_inner_mem p q hpq
  rw [← hc, real_inner_smul_left, real_inner_smul_right, h12_root_inner_self] at hnorm
  rw [← hc, real_inner_smul_right, h12_root_inner_self] at hinner
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hinner
  rcases hinner with hi | hi | hi <;> nlinarith

/-- C16: there are exactly 66 lines from the 66 unordered row pairs. -/
theorem h12_numLines :
    (Set.range fun p : HadamardPair 12 ↦ ℝ ∙ h12.hadamardRoot p).ncard = 66 := by
  rw [Set.ncard_range_of_injective h12_lines_injective]
  norm_num [Nat.card_eq_fintype_card, card_hadamardPair, Nat.choose_two_right]

/-- C16: the acute angle between any two distinct lines is 90° or `arccos(1/3)`. The absolute
inner product makes this independent of the chosen signs of the representatives. -/
theorem h12_line_angles (p q : HadamardPair 12) (hpq : p ≠ q) :
    Real.arccos (|⟪h12.hadamardRoot p, h12.hadamardRoot q⟫| /
      (‖h12.hadamardRoot p‖ * ‖h12.hadamardRoot q‖)) ∈
      ({Real.pi / 2, Real.arccos (1 / 3)} : Set ℝ) := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, h12_root_inner_self,
    h12_root_inner_self, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hh := h12_root_inner_mem p q hpq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with hh | hh | hh <;> norm_num [hh, Real.arccos_zero]

/-- C16: one explicit agreement count, checked in the same integer-list representation. -/
theorem h12_agreement_example : h12.fourRowAgreeCount 0 1 2 3 = 1 := by
  change (toMatrix (R := ℤ) 12 h12Rows).fourRowAgreeCount 0 1 2 3 = 1
  rw [← agreementCount_eq]
  decide +kernel

/-- C16: both allowed acute angles occur; the corresponding normalized inner products are
zero and `-2/3`. The nonzero example uses the checked agreement count and `lem:6-gram`. -/
theorem h12_inner_values_attained :
    (∃ p q : HadamardPair 12, p ≠ q ∧ ⟪h12.hadamardRoot p, h12.hadamardRoot q⟫ = 0) ∧
    (∃ p q : HadamardPair 12, p ≠ q ∧
      ⟪h12.hadamardRoot p, h12.hadamardRoot q⟫ = -(2 / 3 : ℝ)) := by
  constructor
  · refine ⟨⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, by decide, ?_⟩
    rw [inner_hadamardRoot]
    dsimp only
    rw [h12_isHadamard.inner_hadamardRowProduct_of_ne 0 1 2 (by decide), mul_zero]
  · refine ⟨⟨(0, 1), by decide⟩, ⟨(2, 3), by decide⟩, by decide, ?_⟩
    rw [inner_hadamardRoot]
    dsimp only
    rw [h12_isHadamard.inner_hadamardPairs_of_disjoint 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    norm_num [h12_agreement_example]

end Computations.C16
