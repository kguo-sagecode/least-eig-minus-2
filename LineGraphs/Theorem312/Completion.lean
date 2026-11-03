/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.RootSet

/-!
# Completing the seeds for Theorem 3.12 of [CGSS]

`lem:312-completion` of the blueprint: adjoin an orthonormal basis of the orthogonal
complement, scaled to squared norm 2. All mixed products vanish.
-/

open scoped RealInnerProductSpace
open Submodule

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.12
/-- `lem:312-completion`, Theorem 3.12 of [CGSS]. A finite integral seed set
with the long-root parity condition extends to one spanning the ambient space.
The orthogonal complement and its basis may be zero and empty. -/
theorem exists_spanning_integral_seed_extension [FiniteDimensional ℝ V]
    {T : Set V} (hfin : T.Finite)
    (hnorm : ∀ t ∈ T, ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4)
    (hint : ∀ t ∈ T, ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = z)
    (heven : ∀ t ∈ T, ⟪t, t⟫ = 4 → ∀ u ∈ T, ∃ z : ℤ, ⟪t, u⟫ = 2 * z) :
    ∃ T' : Set V, T'.Finite ∧ T ⊆ T' ∧ span ℝ T' = ⊤ ∧
      (∀ t ∈ T', ⟪t, t⟫ = 2 ∨ ⟪t, t⟫ = 4) ∧
      (∀ t ∈ T', ∀ u ∈ T', ∃ z : ℤ, ⟪t, u⟫ = z) ∧
      (∀ t ∈ T', ⟪t, t⟫ = 4 → ∀ u ∈ T', ∃ z : ℤ, ⟪t, u⟫ = 2 * z) := by
  classical
  let W := span ℝ T
  let b := stdOrthonormalBasis ℝ Wᗮ
  let u : Fin (Module.finrank ℝ Wᗮ) → V := fun i ↦ Real.sqrt 2 • (b i : V)
  let P := span ℝ (T ∪ Set.range u)
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hunorm (i) : ⟪u i, u i⟫ = 2 := by
    have hb : ⟪(b i : V), (b i : V)⟫ = 1 := b.inner_eq_one i
    dsimp only [u]
    rw [real_inner_smul_left, real_inner_smul_right, hb, mul_one,
      ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have horth (t : V) (ht : t ∈ T) (i) : ⟪t, u i⟫ = 0 := by
    have hb : ⟪t, (b i : V)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K := W) (subset_span ht) (b i).property
    dsimp only [u]
    rw [real_inner_smul_right, hb, mul_zero]
  have hupair (i j) : ∃ z : ℤ, ⟪u i, u j⟫ = z := by
    by_cases hij : i = j
    · subst j
      exact ⟨2, by simpa only [Int.cast_ofNat] using hunorm i⟩
    · have hb : ⟪(b i : V), (b j : V)⟫ = 0 := b.inner_eq_zero hij
      exact ⟨0, by simp only [u, real_inner_smul_left, real_inner_smul_right,
        hb, mul_zero, Int.cast_zero]⟩
  have hW : W ≤ P := span_mono Set.subset_union_left
  have hperp : Wᗮ ≤ P := by
    have hbmem (i) : (b i : V) ∈ P := by
      have hu : u i ∈ P := subset_span (Or.inr ⟨i, rfl⟩)
      have h := P.smul_mem (Real.sqrt 2)⁻¹ hu
      simpa only [u, smul_smul, inv_mul_cancel₀ hsqrt, one_smul] using h
    have hbspan : span ℝ (Set.range b) ≤ P.comap Wᗮ.subtype := by
      apply span_le.mpr
      rintro x ⟨i, rfl⟩
      exact hbmem i
    have htop : (⊤ : Submodule ℝ Wᗮ) ≤ P.comap Wᗮ.subtype := by
      simpa only [← b.coe_toBasis, b.toBasis.span_eq] using hbspan
    intro x hx
    exact htop (show (⟨x, hx⟩ : Wᗮ) ∈ (⊤ : Submodule ℝ Wᗮ) from mem_top)
  refine ⟨T ∪ Set.range u, hfin.union (Set.finite_range u), Set.subset_union_left,
    ?_, ?_, ?_, ?_⟩
  · apply top_unique
    calc
      ⊤ = W ⊔ Wᗮ := W.isCompl_orthogonal.sup_eq_top.symm
      _ ≤ P := sup_le hW hperp
  · intro t ht
    rcases ht with ht | ⟨i, rfl⟩
    · exact hnorm t ht
    · exact Or.inl (hunorm i)
  · intro t ht v hv
    rcases ht with ht | ⟨i, rfl⟩ <;> rcases hv with hv | ⟨j, rfl⟩
    · exact hint t ht v hv
    · exact ⟨0, by simpa only [Int.cast_zero] using horth t ht j⟩
    · exact ⟨0, by simpa only [Int.cast_zero, real_inner_comm] using horth v hv i⟩
    · exact hupair i j
  · intro t ht hlong v hv
    have htold : t ∈ T := by
      rcases ht with ht | ⟨i, rfl⟩
      · exact ht
      · have := hunorm i
        linarith
    rcases hv with hv | ⟨j, rfl⟩
    · exact heven t htold hlong v hv
    · exact ⟨0, by simpa only [Int.cast_zero, mul_zero] using horth t htold j⟩

end LineSystem
