/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ESubspaces
import LineGraphs.RootSetClassification.LatticeRootSet
import LineGraphs.RootSetClassification.ClassicalCartan

/-!
# The three E root systems and their prescribed bases

`lem:E` in the blueprint for Remark 3.11 of [CGSS]. The lattice norm-two
description proves the root-set axioms. The explicit integer bases and the
minimum-norm lemma give coefficients of one sign.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- The E₇ instance of step `rEgram` of Remark 3.11. -/
theorem E₇.gram_simpleRoot (i j : Fin 7) :
    ⟪E₇.simpleRoot i, E₇.simpleRoot j⟫ = (CartanMatrix.E 7 i j : ℝ) := by
  change ⟪E₈.simpleRoot i.castSucc, E₈.simpleRoot j.castSucc⟫ = _
  rw [E₈.gram_simpleRoot]
  simp [CartanMatrix.E]

/-- The E₆ instance of step `rEgram` of Remark 3.11. -/
theorem E₆.gram_simpleRoot (i j : Fin 6) :
    ⟪E₆.simpleRoot i, E₆.simpleRoot j⟫ = (CartanMatrix.E 6 i j : ℝ) := by
  change ⟪E₈.simpleRoot i.castSucc.castSucc, E₈.simpleRoot j.castSucc.castSucc⟫ = _
  rw [E₈.gram_simpleRoot]
  simp [CartanMatrix.E]

/-- Steps `rEreflection`--`rErootset` for E₈ in Remark 3.11. -/
theorem E₈_isRootSet : IsRootSet E₈ := by
  apply IsRootSet.of_norm_two_lattice e₈Lattice E₈ E₈_eq_norm_two LineSystem.E₈.finite
  · apply top_unique
    rw [← span_E₈_simpleRoot]
    exact span_mono (Set.range_subset_iff.mpr E₈.simpleRoot_mem)
  · exact fun _ hx _ hy ↦ inner_mem_int_e₈Lattice hx hy

/-- Steps `rEreflection`--`rErootset` for E₇ in its specified hyperplane. -/
theorem E₇_isRootSet : IsRootSet E₇ := by
  apply IsRootSet.of_norm_two_lattice e₇Lattice E₇
  · ext x
    change (x : EuclideanSpace ℝ (Fin 8)) ∈ E₈ ↔ _
    rw [E₈_eq_norm_two]
    rfl
  · exact LineSystem.E₈.finite.preimage Subtype.val_injective.injOn
  · apply top_unique
    rw [← span_E₇_simpleRoot]
    exact span_mono (Set.range_subset_iff.mpr fun i ↦ E₈.simpleRoot_mem i.castSucc)
  · exact fun _ hx _ hy ↦ inner_mem_int_e₈Lattice hx hy

/-- Steps `rEreflection`--`rErootset` for E₆ in its specified six-dimensional space. -/
theorem E₆_isRootSet : IsRootSet E₆ := by
  apply IsRootSet.of_norm_two_lattice e₆Lattice E₆
  · ext x
    change (x : EuclideanSpace ℝ (Fin 8)) ∈ E₈ ↔ _
    rw [E₈_eq_norm_two]
    rfl
  · exact LineSystem.E₈.finite.preimage Subtype.val_injective.injOn
  · apply top_unique
    rw [← span_E₆_simpleRoot]
    exact span_mono (Set.range_subset_iff.mpr fun i ↦ E₈.simpleRoot_mem i.castSucc.castSucc)
  · exact fun _ hx _ hy ↦ inner_mem_int_e₈Lattice hx hy

-- Remark 3.11, lem:E
/-- The three root-set assertions of `lem:E` in Remark 3.11 of [CGSS]. -/
theorem E_isRootSet : IsRootSet E₆ ∧ IsRootSet E₇ ∧ IsRootSet E₈ :=
  ⟨E₆_isRootSet, E₇_isRootSet, E₈_isRootSet⟩

/-- Step `rEbase` of Remark 3.11 for E₈: minimal lattice vectors have one-sign coefficients. -/
theorem E₈.base : E₈_isRootSet.IsBase E₈.simpleRoot := by
  refine ⟨E₈.simpleRoot_mem, E₈.simpleRoot_linearIndependent, fun r hr ↦ ?_⟩
  have hcross (i j : Fin 8) (hij : i ≠ j) : ⟪E₈.simpleBasis i, E₈.simpleBasis j⟫ ≤ 0 := by
    rw [E₈.simpleBasis_apply, E₈.simpleBasis_apply, E₈.gram_simpleRoot]
    exact_mod_cast CartanMatrix.E_off_diag_nonpos 8 i j hij
  obtain ⟨c, hc, he⟩ := coefficients_one_sign_of_minimal e₈Lattice (by norm_num : (0 : ℝ) < 2)
    (fun _ hx hne ↦ two_le_inner_self_of_mem_e₈Lattice hx hne) E₈.simpleBasis
    mem_e₈Lattice_iff_exists_coefficients hcross (E₈_subset_e₈Lattice hr)
    (LineSystem.E₈.inner_self r hr)
  exact ⟨c, hc, by simpa only [E₈.simpleBasis_apply] using he⟩

/-- Step `rEbase` of Remark 3.11 for E₇. -/
theorem E₇.base : E₇_isRootSet.IsBase E₇.simpleRoot := by
  refine ⟨fun i ↦ E₈.simpleRoot_mem i.castSucc, E₇.simpleRoot_linearIndependent, fun r hr ↦ ?_⟩
  have hmin (x : e₇Space) (hx : x ∈ e₇Lattice) (hne : x ≠ 0) : 2 ≤ ⟪x, x⟫ :=
    two_le_inner_self_of_mem_e₈Lattice hx (fun h ↦ hne (Subtype.ext h))
  have hcross (i j : Fin 7) (hij : i ≠ j) : ⟪E₇.simpleBasis i, E₇.simpleBasis j⟫ ≤ 0 := by
    rw [E₇.simpleBasis_apply, E₇.simpleBasis_apply, E₇.gram_simpleRoot]
    exact_mod_cast CartanMatrix.E_off_diag_nonpos 7 i j hij
  obtain ⟨c, hc, he⟩ := coefficients_one_sign_of_minimal e₇Lattice (by norm_num : (0 : ℝ) < 2)
    hmin E₇.simpleBasis mem_e₇Lattice_iff_exists_coefficients hcross
    (E₈_subset_e₈Lattice hr) (LineSystem.E₈.inner_self r hr)
  exact ⟨c, hc, by simpa only [E₇.simpleBasis_apply] using he⟩

/-- Step `rEbase` of Remark 3.11 for E₆. -/
theorem E₆.base : E₆_isRootSet.IsBase E₆.simpleRoot := by
  refine ⟨fun i ↦ E₈.simpleRoot_mem i.castSucc.castSucc,
    E₆.simpleRoot_linearIndependent, fun r hr ↦ ?_⟩
  have hmin (x : e₆Space) (hx : x ∈ e₆Lattice) (hne : x ≠ 0) : 2 ≤ ⟪x, x⟫ :=
    two_le_inner_self_of_mem_e₈Lattice hx (fun h ↦ hne (Subtype.ext h))
  have hcross (i j : Fin 6) (hij : i ≠ j) : ⟪E₆.simpleBasis i, E₆.simpleBasis j⟫ ≤ 0 := by
    rw [E₆.simpleBasis_apply, E₆.simpleBasis_apply, E₆.gram_simpleRoot]
    exact_mod_cast CartanMatrix.E_off_diag_nonpos 6 i j hij
  obtain ⟨c, hc, he⟩ := coefficients_one_sign_of_minimal e₆Lattice (by norm_num : (0 : ℝ) < 2)
    hmin E₆.simpleBasis mem_e₆Lattice_iff_exists_coefficients hcross
    (E₈_subset_e₈Lattice hr) (LineSystem.E₈.inner_self r hr)
  exact ⟨c, hc, by simpa only [E₆.simpleBasis_apply] using he⟩

-- Remark 3.11, lem:E
/-- The prescribed root bases in `lem:E` of Remark 3.11 of [CGSS]. -/
theorem E_base : E₆_isRootSet.IsBase E₆.simpleRoot ∧
    E₇_isRootSet.IsBase E₇.simpleRoot ∧ E₈_isRootSet.IsBase E₈.simpleRoot :=
  ⟨E₆.base, E₇.base, E₈.base⟩

/-- The E₈ Cartan identification in `lem:E` of Remark 3.11. -/
theorem E₈.cartanMatrix (i j : Fin 8) :
    IsRootSet.cartanPairing E₈.simpleRoot i j = (CartanMatrix.E 8 i j : ℝ) := by
  simp only [IsRootSet.cartanPairing, E₈.gram_simpleRoot, CartanMatrix.E_diag]
  push_cast
  ring

/-- The E₇ Cartan identification in `lem:E` of Remark 3.11. -/
theorem E₇.cartanMatrix (i j : Fin 7) :
    IsRootSet.cartanPairing E₇.simpleRoot i j = (CartanMatrix.E 7 i j : ℝ) := by
  simp only [IsRootSet.cartanPairing, E₇.gram_simpleRoot, CartanMatrix.E_diag]
  push_cast
  ring

/-- The E₆ Cartan identification in `lem:E` of Remark 3.11. -/
theorem E₆.cartanMatrix (i j : Fin 6) :
    IsRootSet.cartanPairing E₆.simpleRoot i j = (CartanMatrix.E 6 i j : ℝ) := by
  simp only [IsRootSet.cartanPairing, E₆.gram_simpleRoot, CartanMatrix.E_diag]
  push_cast
  ring

-- Remark 3.11, lem:E
/-- The three Cartan matrices in `lem:E` of Remark 3.11 of [CGSS], in Mathlib's numbering. -/
theorem E_cartanMatrix :
    (∀ i j, IsRootSet.cartanPairing E₆.simpleRoot i j = (CartanMatrix.E 6 i j : ℝ)) ∧
    (∀ i j, IsRootSet.cartanPairing E₇.simpleRoot i j = (CartanMatrix.E 7 i j : ℝ)) ∧
    (∀ i j, IsRootSet.cartanPairing E₈.simpleRoot i j = (CartanMatrix.E 8 i j : ℝ)) :=
  ⟨E₆.cartanMatrix, E₇.cartanMatrix, E₈.cartanMatrix⟩

end RootSetModel
