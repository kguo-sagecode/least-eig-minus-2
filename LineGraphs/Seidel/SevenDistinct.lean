/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.SevenModels
import LineGraphs.Seidel.FamilyParameters

/-! # The separating invariants in Proposition `prop:414-seven` (Remark 4.14) -/

open Computations.C22

namespace SimpleGraph

noncomputable local instance : Fintype
    (completeBipartiteGraph (Fin 4) (Fin 4)).edgeSet := Fintype.ofFinite _

/-- Step `s414sevchang`, Proposition `prop:414-seven`: Chang I differs from `T(8)`. -/
theorem changI_not_iso_triangular8 :
    ¬ Nonempty (changI ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) := by
  rintro ⟨e⟩
  have h := e.cliqueProfile_eq 4
  rw [cliqueProfile_changI, cliqueProfile_t8] at h
  have hh := congrArg (Multiset.count 32) h
  norm_num at hh

/-- Step `s414sevchang`, Proposition `prop:414-seven`: Chang II differs from `T(8)`. -/
theorem changII_not_iso_triangular8 :
    ¬ Nonempty (changII ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) := by
  rintro ⟨e⟩
  have h := e.cliqueProfile_eq 4
  rw [cliqueProfile_changII, cliqueProfile_t8] at h
  have hh := congrArg (Multiset.count 34) h
  norm_num at hh

/-- Step `s414sevchang`, Proposition `prop:414-seven`: Chang III differs from `T(8)`. -/
theorem changIII_not_iso_triangular8 :
    ¬ Nonempty (changIII ≃g (⊤ : SimpleGraph (Fin 8)).lineGraph) := by
  rintro ⟨e⟩
  have h := e.cliqueProfile_eq 4
  rw [cliqueProfile_changIII, cliqueProfile_t8] at h
  have hh := congrArg (Multiset.count 33) h
  norm_num at hh

/-- Step `s414sevchang`, Proposition `prop:414-seven`: Chang I and II differ. -/
theorem changI_not_iso_changII : ¬ Nonempty (changI ≃g changII) := by
  rintro ⟨e⟩
  have h := e.cliqueProfile_eq 4
  rw [cliqueProfile_changI, cliqueProfile_changII] at h
  have hh := congrArg (Multiset.count 32) h
  norm_num at hh

/-- Step `s414sevchang`, Proposition `prop:414-seven`: Chang I and III differ. -/
theorem changI_not_iso_changIII : ¬ Nonempty (changI ≃g changIII) := by
  rintro ⟨e⟩
  have h := e.cliqueProfile_eq 4
  rw [cliqueProfile_changI, cliqueProfile_changIII] at h
  have hh := congrArg (Multiset.count 32) h
  norm_num at hh

/-- Step `s414sevchang`, Proposition `prop:414-seven`: Chang II and III differ. -/
theorem changII_not_iso_changIII : ¬ Nonempty (changII ≃g changIII) := by
  rintro ⟨e⟩
  have h := e.cliqueProfile_eq 4
  rw [cliqueProfile_changII, cliqueProfile_changIII] at h
  have hh := congrArg (Multiset.count 34) h
  norm_num at hh

/-- Step `s414sevshr`, Proposition `prop:414-seven`: Shrikhande has no four-cliques. -/
theorem shrikhande_not_iso_lineGraph_completeBipartite_four :
    ¬ Nonempty (shrikhande ≃g (completeBipartiteGraph (Fin 4) (Fin 4)).lineGraph) := by
  rintro ⟨e⟩
  have h := congrArg Multiset.card (e.cliqueMultiset_map 4)
  rw [Multiset.card_map, cliqueCount_shrikhande,
    cliqueCount_lineGraph_completeBipartite] at h
  norm_num at h

-- Proposition (the seven graphs), assertion 3, for Remark 4.14 of [CGSS]
/-- Assertion 3 of `prop:414-seven`, Remark 4.14: the seven graphs are pairwise
non-isomorphic. Their orders and degrees separate all pairs except the Chang graphs. -/
theorem seidel_seven_pairwise_not_iso :
    Pairwise (fun i j : Fin 7 ↦ ¬ Nonempty ((seidelSeven i).2 ≃g (seidelSeven j).2)) := by
  intro i j hij
  rintro ⟨e⟩
  have hn := Fintype.card_congr e.toEquiv
  have hk := e.regular_degree_eq (seidelSeven_isSRGWith i).regular
    (seidelSeven_isSRGWith j).regular
  fin_cases i <;> fin_cases j <;>
    simp [seidelSeven, seidelSevenParameters] at hn hk hij
  all_goals first
    | exact changI_not_iso_changII ⟨e⟩
    | exact changI_not_iso_changII ⟨e.symm⟩
    | exact changI_not_iso_changIII ⟨e⟩
    | exact changI_not_iso_changIII ⟨e.symm⟩
    | exact changII_not_iso_changIII ⟨e⟩
    | exact changII_not_iso_changIII ⟨e.symm⟩

end SimpleGraph
