/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Sixteenths
import LineGraphs.LineSystem.Classification

/-!
# Unconditional component classification and Theorem 6.2

The settled declarations for blueprint `lem:6-components`, `lem:6-decomposition`,
`lem:6-E7`, and `thm:6.2`. Theorem 3.5 of [CGSS], `LineSystem.classification`, discharges
the classification hypothesis of the component arguments and of Theorem 6.2.
-/

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)

-- Lemma (the components), Section 6
/-- Part 5 of blueprint `lem:6-components`, Section 6 of [CGSS]: a component's star closure
has a unique root type, with the same rank and line count, containing at least half the
product of the order and the component rank many lines. Its root isomorphism induces the
surjective linear isometry of spans `LineSystem.Iso.spanIsometry`. -/
theorem component_rootType (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)
    (K : H.hadamardGraph.ConnectedComponent) :
    ∃! t : LineSystem.RootType,
      Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso t.model) ∧
      t.rank = componentRank K ∧
      (hH.componentStarClosure hn hn16 ha K).numLines = t.numLines ∧
      n * componentRank K ≤ 2 * t.numLines := by
  exact hH.component_rootType_of_classification hn hn16 ha
    (fun S hne hI hSC ↦ (S.classification hne).mp ⟨hI, hSC⟩) K

-- Lemma (the possible decompositions), Section 6
/-- Blueprint `lem:6-decomposition`, Section 6 of [CGSS]: either all row pairs form a
single component of type `A_(n-1)` or `D_(n-1)`, or the order is 16 and a component has
type `E₇`. The classification input is supplied by Theorem 3.5. -/
theorem component_cases (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths) :
    (∃ K : H.hadamardGraph.ConnectedComponent, K.supp = Set.univ ∧
      (Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso (LineSystem.An (n - 1))) ∨
       Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso (LineSystem.Dn (n - 1))))) ∨
    (n = 16 ∧ ∃ K : H.hadamardGraph.ConnectedComponent,
      Nonempty ((hH.componentStarClosure hn hn16 ha K).Iso LineSystem.E₇)) := by
  exact hH.component_cases_of_classification hn hn16 ha
    (fun S hne hI hSC ↦ (S.classification hne).mp ⟨hI, hSC⟩)

-- Lemma (no component of type E₇), Section 6
/-- Blueprint `lem:6-E7`, Section 6 of [CGSS]: for a Hadamard matrix of order 16 whose
four distinct rows always agree in 1, 2, or 3 places, no component has star closure
isomorphic to `E₇`. The agreement hypothesis is written without division as
`H.AgreeSixteenths`, and Theorem 3.5 supplies the classification. -/
theorem not_component_E₇ {H : Matrix (Fin 16) (Fin 16) ℤ}
    (hH : H.IsHadamard) (ha : H.AgreeSixteenths)
    (K : H.hadamardGraph.ConnectedComponent) :
    ¬ Nonempty ((hH.componentStarClosure (dvd_refl 16) (le_refl 16) ha K).Iso LineSystem.E₇) := by
  exact hH.not_component_E₇_of_classification ha
    (fun S hne hI hSC ↦ (S.classification hne).mp ⟨hI, hSC⟩) K

include hH

-- Theorem 6.2
/-- Theorem 6.2 of [CGSS], blueprint `thm:6.2`: a Hadamard matrix of order `n > 2` cannot
have every four distinct rows agree in `n/16`, `n/8`, or `3n/16` places. The agreement
hypothesis is exactly `16 * agr ∈ {n, 2n, 3n}`, without division or rounding. No extra
order bound, divisibility assumption, or classification hypothesis is needed. -/
theorem not_fourRow_agree_sixteenths (hn2 : 2 < n)
    (ha : ∀ i j k l : Fin n, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      16 * H.fourRowAgreeCount i j k l ∈ ({n, 2 * n, 3 * n} : Set ℕ)) : False := by
  exact hH.not_fourRow_agree_sixteenths_of_classification hn2
    (fun S hne hI hSC ↦ (S.classification hne).mp ⟨hI, hSC⟩) ha

end Matrix.IsHadamard
