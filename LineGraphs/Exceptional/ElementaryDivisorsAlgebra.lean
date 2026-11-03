/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.BasisDetAlgebra
import Mathlib.Algebra.Module.Projective

/-! # Smith coefficients and the index in a saturated span

The integral linear algebra for Lemma `lem:snf` (Lemma 2.3) of [Exc].
-/

open Module Submodule

namespace Module.Basis.SmithNormalForm

variable {M ι : Type*} [AddCommGroup M] {N : Submodule ℤ M} {r : ℕ}

-- Lemma 2.3 [Exc]
/-- Lemma `lem:snf` (Lemma 2.3) of [Exc]: the Smith coefficients indexing
the basis of the column span are all nonzero. -/
theorem coeff_ne_zero (s : Basis.SmithNormalForm N ι r) (i : Fin r) : s.a i ≠ 0 := by
  intro ha
  apply s.bN.ne_zero i
  apply Subtype.ext
  change (s.bN i : M) = 0
  rw [s.snf, ha, zero_smul]

-- Lemma 2.3 [Exc]
/-- The index computation in Lemma `lem:snf` (Lemma 2.3) of [Exc]: the
product of the absolute Smith coefficients is the index in any saturated
superlattice whose quotient by the column span is killed by a nonzero integer. -/
theorem prod_natAbs_eq_relIndex_of_smul_mem (s : Basis.SmithNormalForm N ι r)
    (P : Submodule ℤ M) (hNP : N ≤ P)
    (hsat : ∀ (a : ℤ), a ≠ 0 → ∀ x : M, a • x ∈ P → x ∈ P)
    (hindex : ∃ a : ℤ, a ≠ 0 ∧ ∀ x ∈ P, a • x ∈ N) :
    ∏ i, (s.a i).natAbs = N.toAddSubgroup.relIndex P.toAddSubgroup := by
  classical
  have hspan : span ℤ (Set.range (fun i ↦ s.bM (s.f i))) = P := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply hsat (s.a i) (s.coeff_ne_zero i)
      rw [← s.snf]
      exact hNP (s.bN i).property
    · intro x hx
      change x ∈ span ℤ (Set.range (s.bM ∘ s.f))
      rw [Set.range_comp]
      apply s.bM.mem_span_image.mpr
      intro i hi
      by_contra hif
      obtain ⟨a, ha, hax⟩ := hindex
      have hh := s.repr_eq_zero_of_notMem_range ⟨a • x, hax x hx⟩ hif
      have he : a * s.bM.repr x i = 0 := by simpa using hh
      exact (Finsupp.mem_support_iff.mp hi) ((mul_eq_zero.mp he).resolve_left ha)
  let bP : Basis (Fin r) ℤ P :=
    (Basis.span (s.bM.linearIndependent.comp s.f s.f.injective)).map
      (LinearEquiv.ofEq _ _ hspan)
  have hbP (i : Fin r) : (bP i : M) = s.bM (s.f i) := by
    simp [bP, Basis.span_apply]
  let v : Fin r → P := fun i ↦ ⟨s.bN i, hNP (s.bN i).property⟩
  have hv (i : Fin r) : v i = s.a i • bP i := by
    apply Subtype.ext
    change (s.bN i : M) = s.a i • (bP i : M)
    rw [hbP, s.snf]
  have hmat : bP.toMatrix v = Matrix.diagonal s.a := by
    ext i j
    simp [Basis.toMatrix_apply, hv, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
    split_ifs with h
    · subst j; rfl
    · rfl
  have hrel := AddSubgroup.relIndex_eq_natAbs_det N.toAddSubgroup P.toAddSubgroup
    hNP s.bN bP
  rw [hrel]
  change _ = (bP.det v).natAbs
  rw [Basis.det_apply, hmat, Matrix.det_diagonal]
  exact (map_prod Int.natAbsHom s.a Finset.univ).symm

end Module.Basis.SmithNormalForm
