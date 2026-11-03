/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic
import LineGraphs.Cartan.Support

/-!
# Indecomposability from a connected root base

`lem:rem-base-connected` in the blueprint for Remark 3.11 of [CGSS]. An
orthogonal partition assigns adjacent simple roots to the same part. Connectedness
makes the assignment constant, and the spanning base excludes roots in the other part.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The graph of distinct nonorthogonal vectors, in `lem:rem-base-connected`
and `lem:rem-components` of Remark 3.11. -/
def nonorthogonalityGraph (α : I → V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ⟪α i, α j⟫ ≠ 0
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

-- Remark 3.11, lem:rem-base-connected
/-- Steps `rbcside`--`rbcother` of Remark 3.11: a connected root base makes the root set
indecomposable. Connectedness includes nonemptiness of the base. -/
theorem isIndecomposable_of_connected_base [Fintype I] {Φ : Set V} (hΦ : IsRootSet Φ)
    {α : I → V} (hα : hΦ.IsBase α) (hc : (nonorthogonalityGraph α).Connected) :
    hΦ.IsIndecomposable := by
  classical
  obtain ⟨i₀⟩ := hc.nonempty
  refine ⟨⟨α i₀, hα.mem i₀⟩, fun A B hab horth ↦ ?_⟩
  have hA : A ⊆ Φ := by rw [← hab]; exact Set.subset_union_left
  have hB : B ⊆ Φ := by rw [← hab]; exact Set.subset_union_right
  have hempty (S : Set V) (hS : S ⊆ Φ)
      (ho : ∀ r ∈ S, ∀ i, ⟪α i, r⟫ = 0) : S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have he (v : V) : ⟪v, r⟫ = 0 := by
      rw [← hα.toBasis.sum_repr v, sum_inner]
      simp only [real_inner_smul_left, IsBase.toBasis_apply, ho r hr, mul_zero,
        Finset.sum_const_zero]
    exact hΦ.ne_zero (hS hr) (inner_self_eq_zero.mp (he r))
  have hstep : ∀ ⦃i j⦄, (nonorthogonalityGraph α).Adj i j →
      (α i ∈ A) = (α j ∈ A) := by
    intro i j hij
    apply propext
    constructor
    · intro hi
      by_contra hj
      have hju : α j ∈ A ∪ B := hab ▸ hα.mem j
      exact hij.2 (horth _ hi _ (hju.resolve_left hj))
    · intro hj
      by_contra hi
      have hiu : α i ∈ A ∪ B := hab ▸ hα.mem i
      have he := horth _ hj _ (hiu.resolve_left hi)
      exact hij.2 (by simpa only [real_inner_comm] using he)
  have hconstant := hc.constant_of_edge_eq hstep
  by_cases hi : α i₀ ∈ A
  · right
    apply hempty B hB
    intro r hr i
    exact horth _ ((hconstant i₀ i) ▸ hi) _ hr
  · left
    apply hempty A hA
    intro r hr i
    have hiA : α i ∉ A := by simpa only [← hconstant i₀ i] using hi
    have hiB : α i ∈ B := (show α i ∈ A ∪ B from hab ▸ hα.mem i).resolve_left hiA
    simpa only [real_inner_comm] using horth _ hr _ hiB

end IsRootSet
