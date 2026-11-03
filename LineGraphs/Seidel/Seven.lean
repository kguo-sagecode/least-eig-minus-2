/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SevenDistinct
import LineGraphs.Seidel.LineGraph

/-! # The seven graphs of Proposition `prop:414-seven` (Remark 4.14) -/

namespace SimpleGraph

/-- Steps `s414sevnum` and `s414sevlk` of Proposition `prop:414-seven`, completed by the
Chang clique profiles: none of the seven graphs is triangular. -/
theorem seidelSeven_not_iso_lineGraph_complete (i : Fin 7) (m : ℕ) :
    ¬ Nonempty ((seidelSeven i).2 ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) := by
  classical
  rintro ⟨e⟩
  have hn := Fintype.card_congr e.toEquiv
  rw [Fintype.card_fin, card_completeGraph_edgeSet] at hn
  have hk := e.regular_degree_eq (seidelSeven_isSRGWith i).regular
    (lineGraph_completeGraph_isRegularOfDegree m)
  have hn28 : (seidelSeven i).1 ≤ 28 := by fin_cases i <;> decide
  have hm : m ≤ 8 := by
    by_contra! hm
    have h := Nat.choose_le_choose 2 (show 9 ≤ m by omega)
    norm_num [Nat.choose] at h
    omega
  interval_cases m <;> fin_cases i <;>
    simp [seidelSeven, seidelSevenParameters, Nat.choose] at hn hk
  · exact changI_not_iso_triangular8 ⟨e⟩
  · exact changII_not_iso_triangular8 ⟨e⟩
  · exact changIII_not_iso_triangular8 ⟨e⟩

/-- Steps `s414sevnum`, `s414sevshr` and `s414sevlk` of Proposition `prop:414-seven`:
none of the seven graphs is the line graph of a balanced complete bipartite graph. -/
theorem seidelSeven_not_iso_lineGraph_completeBipartite (i : Fin 7) (m : ℕ) :
    ¬ Nonempty ((seidelSeven i).2 ≃g
      (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) := by
  classical
  rintro ⟨e⟩
  have hn := Fintype.card_congr e.toEquiv
  rw [Fintype.card_fin, card_completeBipartiteGraph_edgeSet] at hn
  have hk := e.regular_degree_eq (seidelSeven_isSRGWith i).regular
    (lineGraph_completeBipartiteGraph_isRegularOfDegree m)
  have hn28 : (seidelSeven i).1 ≤ 28 := by fin_cases i <;> decide
  have hm : m ≤ 5 := by nlinarith
  interval_cases m <;> fin_cases i <;>
    simp [seidelSeven, seidelSevenParameters] at hn hk
  exact shrikhande_not_iso_lineGraph_completeBipartite_four ⟨e⟩

/-- Step `s414sevnum` of Proposition `prop:414-seven`: the orders and degrees exclude
all cocktail party graphs. -/
theorem seidelSeven_not_iso_cocktailParty (i : Fin 7) (m : ℕ) :
    ¬ Nonempty ((seidelSeven i).2 ≃g cocktailParty m) := by
  rintro ⟨e⟩
  have hn := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at hn
  have hk := e.regular_degree_eq (seidelSeven_isSRGWith i).regular
    (cocktailParty_isRegularOfDegree m)
  fin_cases i <;> simp [seidelSeven, seidelSevenParameters] at hn hk <;> omega

-- Proposition (the seven graphs), assertions 1 and 2, for Remark 4.14 of [CGSS]
/-- Assertions 1 and 2 of `prop:414-seven`, Remark 4.14 of [CGSS]: each of the seven
graphs is connected, strongly regular, has least eigenvalue minus two, is represented
in `E₈`, and belongs to none of the three excluded infinite families. -/
theorem seidel_seven_properties (i : Fin 7) :
    (seidelSeven i).2.Connected ∧
      (seidelSeven i).2.IsSRGWith (seidelSeven i).1 (seidelSevenParameters i).1
        (seidelSevenParameters i).2.1 (seidelSevenParameters i).2.2 ∧
      (seidelSeven i).2.leastEigenvalue = -2 ∧
      (seidelSeven i).2.IsRepresentedIn LineSystem.E₈ ∧
      ∀ m, ¬ Nonempty ((seidelSeven i).2 ≃g (⊤ : SimpleGraph (Fin m)).lineGraph) ∧
        ¬ Nonempty ((seidelSeven i).2 ≃g
          (completeBipartiteGraph (Fin m) (Fin m)).lineGraph) ∧
        ¬ Nonempty ((seidelSeven i).2 ≃g cocktailParty m) := by
  exact ⟨seidelSeven_connected i, seidelSeven_isSRGWith i, seidelSeven_leastEigenvalue i,
    seidelSeven_isRepresentedIn_E₈ i, fun m ↦ ⟨seidelSeven_not_iso_lineGraph_complete i m,
      seidelSeven_not_iso_lineGraph_completeBipartite i m, seidelSeven_not_iso_cocktailParty i m⟩⟩

-- Examples 4.5–4.9 and Remark 4.14
/-- Examples 4.5–4.9 and Remark 4.14 of [CGSS]: none of the seven graphs is a line graph,
even when the proposed root graph has isolated vertices or an infinite vertex type. -/
theorem seidelSeven_not_iso_lineGraph (i : Fin 7) {W : Type*} (Y : SimpleGraph W) :
    ¬ Nonempty ((seidelSeven i).2 ≃g Y.lineGraph) := by
  classical
  rintro ⟨e⟩
  obtain ⟨hc, hs, hl, -, hf⟩ := seidel_seven_properties i
  have hd := ((seidelSeven i).2.leastEigenvalue_eq_neg_two_iff.mp hl).2
  obtain ⟨m, -, hm | hm⟩ :=
    hs.nonempty_iso_lineGraph_complete_or_completeBipartite hc hd e
  · exact (hf m).1 hm
  · exact (hf m).2.1 hm

end SimpleGraph
