/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Pairs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The orthogonal basis attached to a row

Blueprint Lemma `lem:6-fixedrow` for Section 6 of [CGSS]. Including the product of the fixed
row with itself includes the all-ones vector and gives an orthogonal basis of the ambient space.
-/

open scoped BigOperators RealInnerProductSpace
open Submodule

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- The diagonal row product is `j`, as used in step `s6frbasis`. -/
theorem hadamardRowProduct_self (i : Fin n) :
    H.hadamardRowProduct i i = WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) := by
  ext c
  exact (pow_two (H i c : ℝ)).symm.trans (hH.entry_sq i c)

/-- Blueprint Lemma `lem:6-fixedrow`, part 1: a fixed row gives nonzero orthogonal products. -/
theorem hadamardPairs_orthogonal_of_mem (i : Fin n) :
    (∀ j, H.hadamardRowProduct i j ≠ 0) ∧
      Pairwise (fun j k ↦ ⟪H.hadamardRowProduct i j, H.hadamardRowProduct i k⟫ = 0) := by
  refine ⟨fun j hj ↦ ?_, fun j k hjk ↦ hH.inner_hadamardRowProduct_of_ne i j k hjk⟩
  have hs := hH.inner_hadamardPairs_self i j
  rw [hj, inner_zero_left] at hs
  have : 0 < (n : ℝ) := by exact_mod_cast Fin.pos i
  linarith

/-- Independence in step `s6frind` of blueprint Lemma `lem:6-fixedrow`. -/
theorem hadamardRowProduct_linearIndependent (i : Fin n) :
    LinearIndependent ℝ (H.hadamardRowProduct i) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero
    (hH.hadamardPairs_orthogonal_of_mem i).1 (hH.hadamardPairs_orthogonal_of_mem i).2

/-- The orthogonal basis of step `s6frbasis` of blueprint Lemma `lem:6-fixedrow`. -/
noncomputable def hadamardRowBasis (i : Fin n) :
    Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  exact Module.Basis.mk (hH.hadamardRowProduct_linearIndependent i)
    (by rw [(hH.hadamardRowProduct_linearIndependent i).span_eq_top_of_card_eq_finrank
      (by simp)])

/-- The basis vectors are the products, including `j` at the fixed row. -/
theorem hadamardRowBasis_apply (i j : Fin n) :
    hH.hadamardRowBasis i j = H.hadamardRowProduct i j := by
  simp [hadamardRowBasis, Module.Basis.mk_apply]

/-- The full orthogonal expansion underlying steps `s6frwp` and `s6frwj`. -/
theorem eq_sum_inner_hadamardRowProduct (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    v = (1 / (n : ℝ)) • ∑ j, ⟪v, H.hadamardRowProduct i j⟫ • H.hadamardRowProduct i j := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Fin.pos i))
  apply InnerProductSpace.ext_inner_right_basis (hH.hadamardRowBasis i)
  intro k
  rw [hH.hadamardRowBasis_apply]
  simp only [real_inner_smul_left, sum_inner]
  have hs : (∑ j, ⟪v, H.hadamardRowProduct i j⟫ *
      ⟪H.hadamardRowProduct i j, H.hadamardRowProduct i k⟫) =
      ⟪v, H.hadamardRowProduct i k⟫ * n := by
    rw [Finset.sum_eq_single k]
    · rw [hH.inner_hadamardPairs_self]
    · intro j _ hjk
      rw [hH.inner_hadamardRowProduct_of_ne i j k hjk, mul_zero]
    · simp
  rw [hs]
  field_simp

/-- Blueprint Lemma `lem:6-fixedrow`, part 2: expansion in the `n - 1` products in `jᗮ`. -/
theorem eq_sum_inner_hadamardPairs (i : Fin n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ⟪v, WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ))⟫ = 0) :
    v = (1 / (n : ℝ)) • ∑ j ∈ Finset.univ.erase i,
      ⟪v, H.hadamardRowProduct i j⟫ • H.hadamardRowProduct i j := by
  have he := hH.eq_sum_inner_hadamardRowProduct i v
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hH.hadamardRowProduct_self, hv,
    zero_smul, add_zero] at he
  exact he

/-- Blueprint Lemma `lem:6-fixedrow`, part 3: these products span precisely `jᗮ`. -/
theorem span_hadamardPairs_fixedRow (i : Fin n) :
    span ℝ (Set.range fun j : {j : Fin n // j ≠ i} ↦ H.hadamardRowProduct i j) =
      (ℝ ∙ WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)))ᗮ := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact mem_orthogonal_singleton_iff_inner_left.mpr
      (hH.inner_hadamardPairs_one i j j.2.symm)
  · intro v hv
    rw [hH.eq_sum_inner_hadamardPairs i v
      (mem_orthogonal_singleton_iff_inner_left.mp hv)]
    apply smul_mem
    apply sum_mem
    intro j hj
    exact smul_mem _ _ (subset_span ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, rfl⟩)

/-- The dimension statement in blueprint Lemma `lem:6-fixedrow`, part 3. -/
theorem finrank_hadamardPairs_fixedRow (i : Fin n) :
    Module.finrank ℝ (ℝ ∙ WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)))ᗮ = n - 1 := by
  rw [← hH.span_hadamardPairs_fixedRow i]
  have hc := finrank_span_eq_card ((hH.hadamardRowProduct_linearIndependent i).comp
    (fun j : {j : Fin n // j ≠ i} ↦ (j : Fin n)) Subtype.val_injective)
  simpa [Function.comp_def, Fintype.card_subtype_compl] using hc

end Matrix.IsHadamard
