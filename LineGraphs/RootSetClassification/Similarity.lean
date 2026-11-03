/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.ClassicalCartan
import LineGraphs.RootSetClassification.ConnectedBase

/-!
# One common similarity factor

`lem:similarity` of the blueprint for Remark 3.11 of [CGSS]. Equality of the
Cartan pairings propagates the squared-length ratio along the connected base.
The resulting Gram identity extends to the entire space by bilinearity.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

variable {I V W : Type*} [Finite I]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Steps `rsimpositive`--`rsimall` of Remark 3.11: the basis correspondence
scales every inner product by the same positive factor. -/
theorem exists_pos_inner_map_of_cartanMatrix_eq
    (α : Module.Basis I ℝ V) (β : Module.Basis I ℝ W)
    (he : ∀ i j, cartanPairing α i j = cartanPairing β i j)
    (hc : (nonorthogonalityGraph α).Connected)
    (f : V ≃ₗ[ℝ] W) (hf : ∀ i, f (α i) = β i) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪f x, f y⟫ = a * ⟪x, y⟫ := by
  have := Fintype.ofFinite I
  have hq (i : I) : 0 < ⟪α i, α i⟫ := real_inner_self_pos.mpr (α.ne_zero i)
  have hr (i : I) : 0 < ⟪β i, β i⟫ := real_inner_self_pos.mpr (β.ne_zero i)
  have hbalance (i j : I) :
      ⟪β i, β j⟫ * ⟪α j, α j⟫ = ⟪α i, α j⟫ * ⟪β j, β j⟫ := by
    have h := (div_eq_div_iff (ne_of_gt (hq j)) (ne_of_gt (hr j))).mp (he i j)
    nlinarith
  have hedge : ∀ ⦃i j⦄, (nonorthogonalityGraph α).Adj i j →
      ⟪β i, β i⟫ / ⟪α i, α i⟫ = ⟪β j, β j⟫ / ⟪α j, α j⟫ := by
    intro i j hij
    apply (div_eq_div_iff (ne_of_gt (hq i)) (ne_of_gt (hq j))).mpr
    apply mul_left_cancel₀ hij.2
    have hji := hbalance j i
    rw [real_inner_comm (β i) (β j), real_inner_comm (α i) (α j)] at hji
    calc
      ⟪α i, α j⟫ * (⟪β i, β i⟫ * ⟪α j, α j⟫) =
          (⟪β i, β j⟫ * ⟪α i, α i⟫) * ⟪α j, α j⟫ := by rw [hji]; ring
      _ = (⟪β i, β j⟫ * ⟪α j, α j⟫) * ⟪α i, α i⟫ := by ring
      _ = ⟪α i, α j⟫ * (⟪β j, β j⟫ * ⟪α i, α i⟫) := by
        rw [hbalance]; ring
  obtain ⟨i₀⟩ := hc.nonempty
  let a := ⟪β i₀, β i₀⟫ / ⟪α i₀, α i₀⟫
  have ha : 0 < a := div_pos (hr i₀) (hq i₀)
  have hlength (i : I) : ⟪β i, β i⟫ = a * ⟪α i, α i⟫ :=
    (div_eq_iff (ne_of_gt (hq i))).mp (hc.constant_of_edge_eq hedge i i₀)
  have hgram (i j : I) : ⟪β i, β j⟫ = a * ⟪α i, α j⟫ := by
    apply mul_right_cancel₀ (ne_of_gt (hq j))
    rw [hbalance, hlength]
    ring
  refine ⟨a, ha, fun x y ↦ ?_⟩
  rw [← α.sum_repr x, ← α.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, hf, hgram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

-- Remark 3.11, lem:similarity
/-- `lem:similarity` of Remark 3.11: equal connected Cartan pairings and equality
of the root-set images make the basis correspondence a similarity. -/
theorem similarity_of_cartanMatrix_eq {Φ : Set V} {Ψ : Set W}
    (α : Module.Basis I ℝ V) (β : Module.Basis I ℝ W)
    (he : ∀ i j, cartanPairing α i j = cartanPairing β i j)
    (hc : (nonorthogonalityGraph α).Connected)
    (f : V ≃ₗ[ℝ] W) (hf : ∀ i, f (α i) = β i) (himage : f '' Φ = Ψ) :
    ∃ a : ℝ, IsSimilarity Φ Ψ f a := by
  obtain ⟨a, ha, hinner⟩ := exists_pos_inner_map_of_cartanMatrix_eq α β he hc f hf
  exact ⟨a, ha, hinner, himage⟩

end IsRootSet
