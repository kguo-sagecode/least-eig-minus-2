/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.ComponentClosure

/-!
# The possible component decompositions

Blueprint Lemma `lem:6-decomposition`, Section 6 of [CGSS]. The ranks partition the `n - 1`
pairs through one row. The line counts of Lemma 3.4 then force either one classical component
of full rank or, at order 16, an exceptional component of type `E₇`.
-/

open scoped BigOperators RealInnerProductSpace
open Finset

namespace Matrix

/-- Pairs through a row are indexed by the other `n - 1` rows (`s6dsum`). -/
def HadamardPair.rowEquiv {n : ℕ} (i : Fin n) :
    {j : Fin n // j ≠ i} ≃ {p : HadamardPair n // p.1.1 = i ∨ p.1.2 = i} where
  toFun j := ⟨HadamardPair.ofRows i j j.property.symm, by
    unfold HadamardPair.ofRows
    split_ifs <;> simp⟩
  invFun p := ⟨if p.val.1.1 = i then p.val.1.2 else p.val.1.1, by
    split_ifs with h
    · exact fun he ↦ p.val.property.ne (h.trans he.symm)
    · exact h⟩
  left_inv j := by
    apply Subtype.ext
    by_cases h : i < j
    · simp [HadamardPair.ofRows, h]
    · simp [HadamardPair.ofRows, h, j.property]
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨⟨a, b⟩, hab⟩, h | h⟩
    · dsimp at h
      subst i
      simp [HadamardPair.ofRows, hab]
    · dsimp at h
      subst i
      simp [HadamardPair.ofRows, hab.ne, not_lt_of_ge hab.le]

/-- There are exactly `n - 1` pairs through a row, used in step `s6dsum`. -/
theorem card_hadamardPair_row {n : ℕ} (i : Fin n) :
    Fintype.card {p : HadamardPair n // p.1.1 = i ∨ p.1.2 = i} = n - 1 := by
  rw [← Fintype.card_congr (HadamardPair.rowEquiv i)]
  simp [Fintype.card_subtype_compl]

namespace IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Step `s6dsum` of `lem:6-decomposition`, Section 6 of [CGSS]: the component ranks
sum to `n - 1`, by partitioning the pairs through a fixed row. -/
theorem sum_componentRank [Fintype H.hadamardGraph.ConnectedComponent] (hn : 0 < n) :
    ∑ K : H.hadamardGraph.ConnectedComponent, componentRank K = n - 1 := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let F : Finset (HadamardPair n) := univ.filter fun p ↦ p.1.1 = i ∨ p.1.2 = i
  have hF : F.card = n - 1 := by
    simpa only [F, Fintype.card_subtype] using card_hadamardPair_row i
  have hc (K : H.hadamardGraph.ConnectedComponent) :
      (F.filter fun p ↦ H.hadamardGraph.connectedComponentMk p = K) =
        componentRowPairs K i := by
    ext p
    simp only [F, componentRowPairs, mem_filter, mem_univ, true_and,
      SimpleGraph.ConnectedComponent.mem_supp_iff, and_comm]
  have hs := card_eq_sum_card_fiberwise (f := H.hadamardGraph.connectedComponentMk)
    (s := F) (t := univ) (fun _ _ ↦ mem_univ _)
  simp only [hc, hH.card_component_row, hF] at hs
  exact hs.symm

/-- Step `s6dtypes` of `lem:6-decomposition`: the numerical restrictions imposed by
the model line counts of Lemma 3.4 of [CGSS]. -/
theorem component_type_bounds (hn : 16 ∣ n) (hn16 : 16 ≤ n)
    (K : H.hadamardGraph.ConnectedComponent) (t : LineSystem.RootType)
    (hr : t.rank = componentRank K) (hc : n * componentRank K ≤ 2 * t.numLines) :
    match (generalizing := false) t with
    | .A _ _ => componentRank K = n - 1
    | .D _ _ => n + 2 ≤ 2 * componentRank K
    | .E₆ => False
    | .E₇ => n = 16
    | .E₈ => n = 16 := by
  have hp := hH.componentRank_pos K
  have hu := hH.componentRank_le K (by omega)
  cases t with
  | A m hm =>
    change componentRank K = n - 1
    change m = componentRank K at hr
    change n * componentRank K ≤ 2 * (m * (m + 1) / 2) at hc
    have hd : 2 * (m * (m + 1) / 2) ≤ m * (m + 1) := Nat.mul_div_le _ _
    rw [← hr] at hp hu hc ⊢
    have hnle : n ≤ m + 1 := by nlinarith
    omega
  | D m hm =>
    change n + 2 ≤ 2 * componentRank K
    change m = componentRank K at hr
    change n * componentRank K ≤ 2 * (m * (m - 1)) at hc
    rw [← hr] at hp hc ⊢
    have hm' : m - 1 + 1 = m := by omega
    nlinarith
  | E₆ =>
    change False
    change 6 = componentRank K at hr
    change n * componentRank K ≤ 2 * 36 at hc
    rw [← hr] at hc
    omega
  | E₇ =>
    change n = 16
    change 7 = componentRank K at hr
    change n * componentRank K ≤ 2 * 63 at hc
    rw [← hr] at hc
    obtain ⟨k, hk⟩ := hn
    omega
  | E₈ =>
    change n = 16
    change 8 = componentRank K at hr
    change n * componentRank K ≤ 2 * 120 at hc
    rw [← hr] at hc
    obtain ⟨k, hk⟩ := hn
    omega

/-- Two distinct components use disjoint portions of the rank sum (`s6dsmall`). -/
theorem add_componentRank_le (hn : 0 < n)
    (K L : H.hadamardGraph.ConnectedComponent) (hKL : K ≠ L) :
    componentRank K + componentRank L ≤ n - 1 := by
  classical
  let := Fintype.ofFinite H.hadamardGraph.ConnectedComponent
  have hs := Finset.sum_le_sum_of_subset (f := componentRank (H := H))
    (Finset.subset_univ ({K, L} : Finset H.hadamardGraph.ConnectedComponent))
  simpa only [sum_pair hKL, hH.sum_componentRank hn] using hs

/-- A sole component has full rank and contains every pair (`s6dcaseA`, `s6dalone`). -/
theorem component_eq_univ_of_forall_eq (hn : 0 < n) (K : H.hadamardGraph.ConnectedComponent)
    (hK : ∀ L : H.hadamardGraph.ConnectedComponent, L = K) :
    K.supp = Set.univ ∧ componentRank K = n - 1 := by
  classical
  let := Fintype.ofFinite H.hadamardGraph.ConnectedComponent
  constructor
  · apply Set.eq_univ_of_forall
    intro p
    exact hK (H.hadamardGraph.connectedComponentMk p)
  · have hs := hH.sum_componentRank hn
    rw [sum_eq_single K] at hs
    · exact hs
    · intro L _ hL
      exact (hL (hK L)).elim
    · simp

-- Lemma (the possible decompositions), Section 6
/-- Blueprint `lem:6-decomposition`, Section 6 of [CGSS], conditional on Theorem 3.5.
Either there is a single component of type `A_(n-1)` or `D_(n-1)`, or `n = 16` and
there is a component of type `E₇`. -/
theorem component_cases_of_classification (hn : 16 ∣ n) (hn16 : 16 ≤ n)
    (ha : H.AgreeSixteenths)
    (hclass : ∀ S : LineSystem (EuclideanSpace ℝ (Fin n)), S.Φ.Nonempty →
      S.IsIndecomposable → S.IsStarClosed →
        ∃! t : LineSystem.RootType, Nonempty (S.Iso t.model)) :
    (∃ K : H.hadamardGraph.ConnectedComponent, K.supp = Set.univ ∧
      (Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso (LineSystem.An (n - 1))) ∨
       Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso (LineSystem.Dn (n - 1))))) ∨
    (n = 16 ∧ ∃ K : H.hadamardGraph.ConnectedComponent,
      Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso LineSystem.E₇)) := by
  classical
  let := Fintype.ofFinite H.hadamardGraph.ConnectedComponent
  have hnpos : 0 < n := by omega
  have htypes (K : H.hadamardGraph.ConnectedComponent) :=
    (hH.component_rootType_of_classification hn hn16 ha hclass K).exists
  choose t ht using htypes
  have hiso (K : H.hadamardGraph.ConnectedComponent) (u : LineSystem.RootType)
      (hu : t K = u) : Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso u.model) :=
    hu ▸ (ht K).1
  have hb (K : H.hadamardGraph.ConnectedComponent) :=
    hH.component_type_bounds hn hn16 K (t K) (ht K).2.1 (ht K).2.2.2
  have hfull (K : H.hadamardGraph.ConnectedComponent) (hr : componentRank K = n - 1) :
      ∀ L : H.hadamardGraph.ConnectedComponent, L = K := by
    intro L
    by_contra hLK
    have hp := hH.componentRank_pos L
    have hs := hH.add_componentRank_le hnpos L K hLK
    omega
  by_cases hA : ∃ K m hm, t K = LineSystem.RootType.A m hm
  · obtain ⟨K, m, hm, hKt⟩ := hA
    have hr : componentRank K = n - 1 := by simpa only [hKt] using hb K
    have hmrank : m = n - 1 := by simpa only [hKt, LineSystem.RootType.rank, hr]
      using (ht K).2.1
    have hu := (hH.component_eq_univ_of_forall_eq hnpos K (hfull K hr)).1
    left
    refine ⟨K, hu, Or.inl ?_⟩
    have hi : Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso (LineSystem.An m)) :=
      hiso K (.A m hm) hKt
    exact hmrank ▸ hi
  by_cases hD : ∃ K m hm, t K = LineSystem.RootType.D m hm
  · obtain ⟨K, m, hm, hKt⟩ := hD
    have hr : n + 2 ≤ 2 * componentRank K := by simpa only [hKt] using hb K
    have hall : ∀ L : H.hadamardGraph.ConnectedComponent, L = K := by
      intro L
      by_contra hLK
      have hsum := hH.add_componentRank_le hnpos L K hLK
      have hL := hb L
      have hLrank := (ht L).2.1
      cases hLt : t L with
      | A l hl => exact hA ⟨L, l, hl, hLt⟩
      | D l hl =>
        simp only [hLt] at hL
        omega
      | E₆ => simp only [hLt] at hL
      | E₇ =>
        simp only [hLt] at hL
        simp only [hLt, LineSystem.RootType.rank] at hLrank
        omega
      | E₈ =>
        simp only [hLt] at hL
        simp only [hLt, LineSystem.RootType.rank] at hLrank
        omega
    obtain ⟨hu, hKrank⟩ := hH.component_eq_univ_of_forall_eq hnpos K hall
    have hmrank : m = n - 1 := by simpa only [hKt, LineSystem.RootType.rank, hKrank]
      using (ht K).2.1
    left
    refine ⟨K, hu, Or.inr ?_⟩
    have hi : Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso (LineSystem.Dn m)) :=
      hiso K (.D m hm) hKt
    exact hmrank ▸ hi
  have hexc (K : H.hadamardGraph.ConnectedComponent) :
      t K = LineSystem.RootType.E₇ ∨ t K = LineSystem.RootType.E₈ := by
    have hK := hb K
    cases hKt : t K with
    | A m hm => exact (hA ⟨K, m, hm, hKt⟩).elim
    | D m hm => exact (hD ⟨K, m, hm, hKt⟩).elim
    | E₆ => simp only [hKt] at hK
    | E₇ => exact Or.inl rfl
    | E₈ => exact Or.inr rfl
  let p : HadamardPair n := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
    change (0 : ℕ) < 1
    omega⟩
  let K₀ := H.hadamardGraph.connectedComponentMk p
  have hn16eq : n = 16 := by
    have hK := hb K₀
    rcases hexc K₀ with hK₀ | hK₀ <;> simpa only [hK₀] using hK
  have hseven : ∃ K, t K = LineSystem.RootType.E₇ := by
    by_contra hseven
    have hevery (K : H.hadamardGraph.ConnectedComponent) : componentRank K = 8 := by
      have hKt := (hexc K).resolve_left (fun h ↦ hseven ⟨K, h⟩)
      simpa only [hKt, LineSystem.RootType.rank] using (ht K).2.1.symm
    have hs := hH.sum_componentRank hnpos
    simp only [hevery, sum_const, card_univ, smul_eq_mul, hn16eq] at hs
    omega
  obtain ⟨K, hK⟩ := hseven
  right
  refine ⟨hn16eq, K, ?_⟩
  exact hiso K .E₇ hK

end IsHadamard
end Matrix
