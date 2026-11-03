/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SwitchingRegular
import LineGraphs.Seidel.SwitchingTransport
import LineGraphs.Computations.C22

/-!
# Classification of regular switchings of T(5) and T(8)

Lemmas `lem:414-E6` and `lem:414-E8`, Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

open Classical in
-- Lemma (regular switchings of T(5)), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-E6`, Remark 4.14: every cubic switching of `T(5)` is Petersen. -/
theorem nonempty_iso_petersen_of_switch_triangular5
    (H : Set (⊤ : SimpleGraph (Fin 5)).edgeSet)
    (hr : ((⊤ : SimpleGraph (Fin 5)).lineGraph.switch H).IsRegularOfDegree 3) :
    Nonempty ((⊤ : SimpleGraph (Fin 5)).lineGraph.switch H ≃g petersen) := by
  let Z := triangularSwitchingGraph H
  let e : (⊤ : SimpleGraph (Fin 5)).lineGraph.switch H ≃g switchTriangular Z := by
    dsimp [Z]
    rw [switchTriangular_triangularSwitchingGraph]
  have hz : (switchTriangular Z).IsRegularOfDegree 3 := by
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    exact (e.degree_eq v).trans (hr v)
  have htwo := isRegularOfDegree_two_of_switchTriangular_five Z hz
  obtain ⟨f⟩ := htwo.nonempty_iso_cycle_of_two_of_card_eq_five rfl
  obtain ⟨g⟩ := Computations.C22.e6_switch_cycle5
  exact ⟨e.trans (f.switchTriangular.trans g)⟩

/-- The eleven SE4 models and C22 classify switchings by graphs of degree at most three
in the proof of `lem:414-E8`. -/
theorem nonempty_iso_triangular8_or_chang_of_degree_le_three
    (Z : SimpleGraph (Fin 8)) [DecidableRel Z.Adj] {d : ℕ}
    (hr : Z.IsRegularOfDegree d) (hd : d ≤ 3) :
    Nonempty (switchTriangular Z ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) ∨
      Nonempty (switchTriangular Z ≃g changI) ∨ Nonempty (switchTriangular Z ≃g changII) ∨
      Nonempty (switchTriangular Z ≃g changIII) := by
  interval_cases d
  · rw [hr.eq_bot_of_zero]
    exact Or.inl Computations.C22.e8_switch_empty
  · obtain ⟨e⟩ := hr.nonempty_iso_fourK2 rfl
    obtain ⟨f⟩ := Computations.C22.e8_switch_fourK2
    exact Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩)
  · rcases hr.nonempty_iso_of_two_of_card_eq_eight rfl with h | h | h
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_cycle8
      exact Or.inr (Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩))
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_cycleThreeFive
      exact Or.inr (Or.inr (Or.inr ⟨e.switchTriangular.trans f⟩))
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_twoC4
      exact Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩)
  · rcases hr.nonempty_iso_of_three_of_card_eq_eight rfl with
      h | h | h | h | h | h
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_twoK4
      exact Or.inl ⟨e.switchTriangular.trans f⟩
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_cube
      exact Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩)
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_wagner
      exact Or.inr (Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩))
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_truncatedK33
      exact Or.inr (Or.inr (Or.inr ⟨e.switchTriangular.trans f⟩))
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_twiceTruncatedK4
      exact Or.inr (Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩))
    · obtain ⟨e⟩ := h
      obtain ⟨f⟩ := Computations.C22.e8_switch_twoDiamonds
      exact Or.inr (Or.inl ⟨e.switchTriangular.trans f⟩)

/-- The complement reduction in `lem:414-E8` makes every regular switching graph an SE4 case. -/
theorem nonempty_iso_triangular8_or_chang_of_regular_switchTriangular
    (Z : SimpleGraph (Fin 8))
    (hr : (switchTriangular Z).IsRegularOfDegree 12) :
    Nonempty (switchTriangular Z ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) ∨
      Nonempty (switchTriangular Z ≃g changI) ∨ Nonempty (switchTriangular Z ≃g changII) ∨
      Nonempty (switchTriangular Z ≃g changIII) := by
  classical
  obtain ⟨d, hd, hZ⟩ := exists_isRegularOfDegree_of_switchTriangular_eight Z hr
  by_cases hsmall : d ≤ 3
  · exact nonempty_iso_triangular8_or_chang_of_degree_le_three Z hZ hsmall
  have hc : Zᶜ.IsRegularOfDegree (7 - d) := by
    simpa only [Fintype.card_fin] using hZ.compl
  have h := nonempty_iso_triangular8_or_chang_of_degree_le_three Zᶜ hc (by omega)
  simpa only [switchTriangular_compl] using h

open Classical in
-- Lemma (regular switchings of T(8)), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-E8`, Remark 4.14: every twelve-regular switching of `T(8)` is triangular
or one of the three Chang graphs. The cut is arbitrary. -/
theorem nonempty_iso_triangular8_or_chang_of_switch_triangular8
    (H : Set (⊤ : SimpleGraph (Fin 8)).edgeSet)
    (hr : ((⊤ : SimpleGraph (Fin 8)).lineGraph.switch H).IsRegularOfDegree 12) :
    Nonempty ((⊤ : SimpleGraph (Fin 8)).lineGraph.switch H ≃g
      (⊤ : SimpleGraph (Fin 8)).lineGraph) ∨
      Nonempty ((⊤ : SimpleGraph (Fin 8)).lineGraph.switch H ≃g changI) ∨
      Nonempty ((⊤ : SimpleGraph (Fin 8)).lineGraph.switch H ≃g changII) ∨
      Nonempty ((⊤ : SimpleGraph (Fin 8)).lineGraph.switch H ≃g changIII) := by
  let Z := triangularSwitchingGraph H
  let e : (⊤ : SimpleGraph (Fin 8)).lineGraph.switch H ≃g switchTriangular Z := by
    dsimp [Z]
    rw [switchTriangular_triangularSwitchingGraph]
  have hz : (switchTriangular Z).IsRegularOfDegree 12 := by
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    exact (e.degree_eq v).trans (hr v)
  rcases nonempty_iso_triangular8_or_chang_of_regular_switchTriangular Z hz with
    h | h | h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨e.trans f⟩)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans f⟩))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨e.trans f⟩))

end SimpleGraph
