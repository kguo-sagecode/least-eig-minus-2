/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Decomposition
import LineGraphs.Hadamard.Orthogonal
import LineGraphs.Hadamard.E7

/-!
# Theorem 6.2

Theorem 6.2 of [CGSS], blueprint `thm:6.2`, with Theorem 3.5 as an explicit hypothesis.
The small-order lemma forces order divisible by 16. The component decomposition leaves a
classical component of full rank, excluded by the orthogonal family through one row, or an
`E₇` component at order 16, excluded by the star count.
-/

open scoped RealInnerProductSpace

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
include hH

/-- Step `s62F` of Theorem 6.2 of [CGSS]: a full component carries the `n - 1` mutually
orthogonal roots through a row to an orthogonal family in its model. -/
theorem exists_orthogonal_family_of_component_eq_univ
    (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : LineSystem E}
    (K : H.hadamardGraph.ConnectedComponent) (hK : K.supp = Set.univ)
    (e : (hH.componentStarClosure hn hn16 ha K).Iso T) (i : Fin n) :
    ∃ v : {j : Fin n // j ≠ i} → E,
      (∀ j, v j ∈ T.Φ) ∧ Pairwise (fun j k ↦ ⟪v j, v k⟫ = 0) := by
  let p (j : {j : Fin n // j ≠ i}) := HadamardPair.ofRows i j j.property.symm
  have hp (j : {j : Fin n // j ≠ i}) :
      H.hadamardRoot (p j) ∈ (hH.componentStarClosure hn hn16 ha K).Φ := by
    apply (hH.componentLineSystem hn hn16 ha K).subset_starClosure
    apply hH.hadamardRoot_mem_componentLineSystem
    rw [hK]
    exact Set.mem_univ _
  refine ⟨fun j ↦ e.toEquiv ⟨H.hadamardRoot (p j), hp j⟩,
    fun j ↦ (e.toEquiv ⟨H.hadamardRoot (p j), hp j⟩).property, ?_⟩
  intro j k hjk
  rw [e.inner_map]
  change ⟪H.hadamardRoot (HadamardPair.ofRows i j j.property.symm),
    H.hadamardRoot (HadamardPair.ofRows i k k.property.symm)⟫ = 0
  rw [hadamardRoot_ofRows, hadamardRoot_ofRows]
  exact hH.hadamardRoots_orthogonal_of_mem i j k (fun he ↦ hjk (Subtype.ext he))

-- Theorem 6.2
/-- Theorem 6.2 of [CGSS], blueprint `thm:6.2`, conditional on the forward unique-type
form of Theorem 3.5: no Hadamard matrix of order greater than two has every four-row
agreement count among `n/16`, `n/8`, and `3n/16`. -/
theorem not_fourRow_agree_sixteenths_of_classification (hn2 : 2 < n)
    (hclass : ∀ S : LineSystem (EuclideanSpace ℝ (Fin n)), S.Φ.Nonempty →
      S.IsIndecomposable → S.IsStarClosed →
        ∃! t : LineSystem.RootType, Nonempty (S.Iso t.model)) : ¬ H.AgreeSixteenths := by
  intro ha
  obtain ⟨hn, hn16⟩ := hH.sixteen_dvd_of_agree_sixteenths hn2 ha
  rcases hH.component_cases_of_classification hn hn16 ha hclass with
    ⟨K, hK, heA | heD⟩ | ⟨hnEq, K, he⟩
  · obtain ⟨e⟩ := heA
    let i : Fin n := ⟨0, by omega⟩
    obtain ⟨v, hv, ho⟩ :=
      hH.exists_orthogonal_family_of_component_eq_univ hn hn16 ha K hK e i
    exact LineSystem.An.not_card_pairwise_orthogonal (by omega) v hv ho
      (by simp [Fintype.card_subtype_compl])
  · obtain ⟨e⟩ := heD
    let i : Fin n := ⟨0, by omega⟩
    obtain ⟨v, hv, ho⟩ :=
      hH.exists_orthogonal_family_of_component_eq_univ hn hn16 ha K hK e i
    have heven := LineSystem.Dn.even_of_card_pairwise_orthogonal v hv ho
      (by simp [Fintype.card_subtype_compl])
    obtain ⟨k, hk⟩ := heven
    obtain ⟨m, hm⟩ := hn
    omega
  · subst n
    exact hH.not_component_E₇_of_classification ha hclass K he

end Matrix.IsHadamard
