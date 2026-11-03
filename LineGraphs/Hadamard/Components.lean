/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Degree
import LineGraphs.Hadamard.Entries
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The components of the Hadamard line system

The counting and rank assertions of blueprint Lemma `lem:6-components`, Section 6 of [CGSS].
The graph uses increasing row pairs, as in `HadamardPair`. A component row is represented by
the pairs incident with that row; the other endpoint uniquely specifies the second row.
These assertions use only the Hadamard condition and positive order.
-/

open scoped BigOperators RealInnerProductSpace
open Submodule Finset

namespace Matrix

/-- The increasing pair associated with two distinct rows, in Section 6 of [CGSS]. -/
def HadamardPair.ofRows {n : ℕ} (i j : Fin n) (h : i ≠ j) : HadamardPair n :=
  if hij : i < j then ⟨(i, j), hij⟩ else ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hij) h.symm⟩

/-- The normalized product does not depend on the order of the two rows. -/
theorem hadamardRoot_ofRows {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (h : i ≠ j) :
    H.hadamardRoot (HadamardPair.ofRows i j h) =
      Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct i j := by
  unfold HadamardPair.ofRows
  split_ifs <;> simp only [hadamardRoot]
  rw [hadamardRowProduct_comm]

/-- The graph `Λ_H` preceding blueprint Lemma `lem:6-components`, Section 6 of [CGSS]. -/
def hadamardGraph {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : SimpleGraph (HadamardPair n) where
  Adj p q := p ≠ q ∧ ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ≠ 0
  symm := ⟨by
    intro p q h
    exact ⟨h.1.symm, by rw [real_inner_comm]; exact h.2⟩⟩
  loopless := ⟨fun p h ↦ h.1 rfl⟩

/-- The pairs in a component incident with a fixed row, in `lem:6-components`. -/
noncomputable def componentRowPairs {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (K : H.hadamardGraph.ConnectedComponent) (i : Fin n) : Finset (HadamardPair n) := by
  classical
  exact univ.filter fun p ↦ p ∈ K.supp ∧ (p.1.1 = i ∨ p.1.2 = i)

/-- The component span `U_K` in blueprint Lemma `lem:6-components`, Section 6 of [CGSS]. -/
noncomputable def componentSpan {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (K : H.hadamardGraph.ConnectedComponent) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  span ℝ (H.hadamardRoot '' K.supp)

/-- The rank `m_K` of a component in blueprint Lemma `lem:6-components`. -/
noncomputable def componentRank {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ}
    (K : H.hadamardGraph.ConnectedComponent) : ℕ := Module.finrank ℝ (componentSpan K)

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Step `s6csum` of `lem:6-components`, Section 6 of [CGSS]: the normalized expansion. -/
theorem eq_sum_inner_normalizedRowProduct (i : Fin n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ⟪v, WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ))⟫ = 0) :
    v = (1 / 2 : ℝ) • ∑ j ∈ univ.erase i,
      ⟪v, Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct i j⟫ •
        (Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct i j) := by
  calc
    v = (1 / (n : ℝ)) • ∑ j ∈ univ.erase i,
        ⟪v, H.hadamardRowProduct i j⟫ • H.hadamardRowProduct i j :=
      hH.eq_sum_inner_hadamardPairs i v hv
    _ = _ := by
      simp only [smul_sum, real_inner_smul_right, smul_smul]
      apply sum_congr rfl
      intro j _
      congr 1
      have hs := Real.mul_self_sqrt (show 0 ≤ 2 / (n : ℝ) by positivity)
      calc
        (1 / (n : ℝ)) * ⟪v, H.hadamardRowProduct i j⟫ =
            (1 / 2 : ℝ) * (2 / (n : ℝ)) * ⟪v, H.hadamardRowProduct i j⟫ := by ring
        _ = _ := by nth_rw 1 [← hs]; ring

omit hH in
/-- Step `s6cterm` of `lem:6-components`: a nonzero coefficient stays in the component. -/
theorem mem_component_of_inner_ne_zero (_hH : H.IsHadamard)
    (K : H.hadamardGraph.ConnectedComponent)
    {p q : HadamardPair n} (hp : p ∈ K.supp)
    (hpq : ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ≠ 0) : q ∈ K.supp := by
  by_cases he : p = q
  · exact he ▸ hp
  · exact K.mem_supp_of_adj_mem_supp hp ⟨he, hpq⟩

/-- Steps `s6cexp` and `s6cspan` of `lem:6-components`: each row spans the component. -/
theorem span_component_row (K : H.hadamardGraph.ConnectedComponent) (i : Fin n) :
    span ℝ (H.hadamardRoot '' (componentRowPairs K i : Set (HadamardPair n))) =
      componentSpan K := by
  classical
  apply le_antisymm
  · apply span_mono
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, (mem_filter.mp hp).2.1, rfl⟩
  · apply span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    rw [hH.eq_sum_inner_normalizedRowProduct i (H.hadamardRoot p)
      (hH.inner_hadamardRoot_one p)]
    apply smul_mem
    apply sum_mem
    intro j hj
    by_cases hz : ⟪H.hadamardRoot p,
        Real.sqrt (2 / (n : ℝ)) • H.hadamardRowProduct i j⟫ = 0
    · rw [hz, zero_smul]
      exact zero_mem _
    · have hij : i ≠ j := (mem_erase.mp hj).1.symm
      rw [← hadamardRoot_ofRows H i j hij] at hz ⊢
      apply smul_mem
      apply subset_span
      refine ⟨HadamardPair.ofRows i j hij, ?_, rfl⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, hH.mem_component_of_inner_ne_zero K hp hz, ?_⟩
      unfold HadamardPair.ofRows
      split_ifs <;> simp

/-- Step `s6cind` of `lem:6-components`: the roots through one row are independent. -/
theorem component_row_linearIndependent (K : H.hadamardGraph.ConnectedComponent)
    (i : Fin n) : LinearIndependent ℝ
      (fun p : (componentRowPairs K i : Set (HadamardPair n)) ↦ H.hadamardRoot p) := by
  classical
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro p hp
    have hs := hH.inner_hadamardRoot_self (Fin.pos i) p
    rw [hp, inner_zero_left] at hs
    norm_num at hs
  · intro p q hpq
    rw [inner_hadamardRoot]
    have hp := (mem_filter.mp p.property).2.2
    have hq := (mem_filter.mp q.property).2.2
    have he : (p : HadamardPair n) ≠ q := fun h ↦ hpq (Subtype.ext h)
    have hm : p.val.1.1 = q.val.1.1 ∨ p.val.1.1 = q.val.1.2 ∨
        p.val.1.2 = q.val.1.1 ∨ p.val.1.2 = q.val.1.2 := by
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · exact Or.inl (hp.trans hq.symm)
      · exact Or.inr (Or.inl (hp.trans hq.symm))
      · exact Or.inr (Or.inr (Or.inl (hp.trans hq.symm)))
      · exact Or.inr (Or.inr (Or.inr (hp.trans hq.symm)))
    rw [hH.inner_hadamardPairs_of_meet p q he hm, mul_zero]

-- Lemma (the components), Section 6
/-- Blueprint `lem:6-components`, part 1 (`s6cone`), Section 6 of [CGSS]: each row
is incident with exactly `m_K` pairs of a component. -/
theorem card_component_row (K : H.hadamardGraph.ConnectedComponent) (i : Fin n) :
    (componentRowPairs K i).card = componentRank K := by
  classical
  have hc := finrank_span_eq_card (hH.component_row_linearIndependent K i)
  have he : (Set.range fun p : (componentRowPairs K i : Set (HadamardPair n)) ↦
      H.hadamardRoot p) = H.hadamardRoot '' (componentRowPairs K i : Set (HadamardPair n)) :=
    by
      ext v
      exact ⟨fun ⟨p, hp⟩ ↦ ⟨p, p.property, hp⟩,
        fun ⟨p, hp, hv⟩ ↦ ⟨⟨p, hp⟩, hv⟩⟩
  rw [he, hH.span_component_row] at hc
  simpa only [componentRank, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Set.ncard_coe_finset] using hc.symm

-- Lemma (the components), Section 6
/-- Blueprint `lem:6-components`, part 2 (`s6ctwo`), Section 6 of [CGSS]: double counting
the incidences of rows with pairs gives `2 |K| = n m_K`. -/
theorem two_mul_card_component (K : H.hadamardGraph.ConnectedComponent) :
    2 * K.supp.ncard = n * componentRank K := by
  classical
  have hc (p : HadamardPair n) :
      (univ.filter fun i : Fin n ↦ p.1.1 = i ∨ p.1.2 = i).card = 2 := by
    have he : (univ.filter fun i : Fin n ↦ p.1.1 = i ∨ p.1.2 = i) =
        {p.1.1, p.1.2} := by ext i; simp [eq_comm]
    rw [he, card_pair p.2.ne]
  have hs : ∑ i : Fin n, (componentRowPairs K i).card = 2 * K.supp.ncard := by
    simp only [componentRowPairs, card_filter]
    rw [sum_comm]
    calc
      (∑ p : HadamardPair n, ∑ i : Fin n,
          if p ∈ K.supp ∧ (p.1.1 = i ∨ p.1.2 = i) then (1 : ℕ) else 0) =
          ∑ p : HadamardPair n, if p ∈ K.supp then 2 else 0 := by
        apply sum_congr rfl
        intro p _
        by_cases hp : p ∈ K.supp
        · simp only [hp, true_and, ite_true]
          simpa only [card_filter] using hc p
        · simp [hp]
      _ = 2 * K.supp.ncard := by
        rw [← sum_filter]
        simp [Set.ncard_eq_toFinset_card', mul_comm]
  simpa only [hH.card_component_row, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] using hs.symm

/-- Blueprint `lem:6-components`, part 3 (`s6cthree`): a component has positive rank. -/
theorem componentRank_pos (K : H.hadamardGraph.ConnectedComponent) :
    0 < componentRank K := by
  have hp := Set.ncard_pos (s := K.supp) |>.mpr K.nonempty_supp
  have hc := hH.two_mul_card_component K
  by_contra hz
  have : componentRank K = 0 := by omega
  rw [this, mul_zero] at hc
  omega

/-- Blueprint `lem:6-components`, part 3 (`s6cthree`): the rank is at most `n - 1`. -/
theorem componentRank_le (K : H.hadamardGraph.ConnectedComponent) (hn : 0 < n) :
    componentRank K ≤ n - 1 := by
  have hle : componentSpan K ≤
      (ℝ ∙ WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)))ᗮ := by
    apply span_le.mpr
    rintro _ ⟨p, _, rfl⟩
    exact mem_orthogonal_singleton_iff_inner_left.mpr (hH.inner_hadamardRoot_one p)
  have hd := Submodule.finrank_mono hle
  rwa [hH.finrank_hadamardPairs_fixedRow ⟨0, hn⟩] at hd

end IsHadamard
end Matrix
