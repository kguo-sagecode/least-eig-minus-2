/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.ExtensionMatrix
import LineGraphs.Cited.HallConnor.BruckRyserChowla

/-!
# No 2-(15,5,2) design

The conclusions `hc:thm:false` and `hc:cor:main` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13).
-/

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

/-- Hall–Connor's extension contradicts Bruck–Ryser–Chowla, `hc:thm:false`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem false_of_parameters_15_5_2 (D : Design P B 15 5 21 7 2) : False := by
  obtain ⟨M, hM⟩ := D.hall_connor
  exact Matrix.bruck_ryser_chowla_twenty_two M hM

/-- The bundled nonexistence statement `hcMainBundled` of `hc:cor:main`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem not_nonempty_15_5_2 : ¬ Nonempty (Design (Fin 15) (Fin 21) 15 5 21 7 2) :=
  fun ⟨D⟩ ↦ D.false_of_parameters_15_5_2

omit [DecidableEq B] in
/-- Pair counts alone exclude a 2-(15,5,2) design, `hcMainUnbundled` of `hc:cor:main`
([CGSS], Remark 5.12 and Example 5.13); the replication and label counts are derived. -/
theorem not_pair_counts_15_5_2 (F : B → Finset P) (hv : Fintype.card P = 15)
    (hk : ∀ label, (F label).card = 5) :
    ¬ (∀ p q, p ≠ q →
      (Finset.univ.filter (fun label ↦ p ∈ F label ∧ q ∈ F label)).card = 2) := by
  classical
  intro hlam
  obtain ⟨D, _⟩ := exists_of_pair_counts_15_5_2 F hv hk hlam
  exact D.false_of_parameters_15_5_2

end Design
