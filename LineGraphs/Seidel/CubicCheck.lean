/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.CubicCase023
import LineGraphs.Seidel.CubicCase024
import LineGraphs.Seidel.CubicCase025
import LineGraphs.Seidel.CubicCase026
import LineGraphs.Seidel.CubicCase027
import LineGraphs.Seidel.CubicCase034
import LineGraphs.Seidel.CubicCase035
import LineGraphs.Seidel.CubicCase036
import LineGraphs.Seidel.CubicCase037
import LineGraphs.Seidel.CubicCase045
import LineGraphs.Seidel.CubicCase046
import LineGraphs.Seidel.CubicCase047
import LineGraphs.Seidel.CubicCase056
import LineGraphs.Seidel.CubicCase057
import LineGraphs.Seidel.CubicCase067

/-! # Assembly of the local SE4 certificates (`res:414-SE4`, Remark 4.14) -/

namespace SimpleGraph.CubicEight

/-- All completions of the rooted SE4 neighbourhood table have a checked isomorphism. -/
theorem checkCompletions_eq_true :
    checkCompletions checkCertificate [1, 2, 3, 4, 5, 6, 7] initialRows = true := by
  have cover : ∀ s ∈ rowChoices initialRows 1, compatible initialRows 1 s = true →
      s ∈ [{0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 2, 7},
        {0, 3, 4}, {0, 3, 5}, {0, 3, 6}, {0, 3, 7}, {0, 4, 5},
        {0, 4, 6}, {0, 4, 7}, {0, 5, 6}, {0, 5, 7}, {0, 6, 7}] := by
    decide +kernel
  apply List.all_eq_true.mpr
  intro s hs
  by_cases hc : compatible initialRows 1 s = true
  · simp only [hc, ite_true]
    have hm := cover s hs hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact check_completions_023
    · exact check_completions_024
    · exact check_completions_025
    · exact check_completions_026
    · exact check_completions_027
    · exact check_completions_034
    · exact check_completions_035
    · exact check_completions_036
    · exact check_completions_037
    · exact check_completions_045
    · exact check_completions_046
    · exact check_completions_047
    · exact check_completions_056
    · exact check_completions_057
    · exact check_completions_067
  · simp [hc]

/-- The cubic conclusion of `res:414-SE4` for the fixed root labelling. -/
theorem nonempty_iso_of_neighborFinset_zero (X : SimpleGraph (Fin 8)) [DecidableRel X.Adj]
    (hr : X.IsRegularOfDegree 3) (hzero : X.neighborFinset 0 = {1, 2, 3}) :
    ∃ i, Nonempty (X ≃g model i) :=
  nonempty_iso_of_checkCertificate X
    (checkCompletions_initial_sound X hr hzero checkCertificate checkCompletions_eq_true)

end SimpleGraph.CubicEight
