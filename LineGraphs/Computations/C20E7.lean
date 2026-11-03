/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20E7Rows00
import LineGraphs.Computations.C20E7Rows01
import LineGraphs.Computations.C20E7Rows02
import LineGraphs.Computations.C20E7Rows03
import LineGraphs.Computations.C20E7Rows04
import LineGraphs.Computations.C20E7Rows05
import LineGraphs.Computations.C20E7Rows06
import LineGraphs.Computations.NeighborCertificates
import LineGraphs.Computations.C4E7

/-!
# C20 E7 neighborhoods

C20 for E7, transferred to neighborhoods of real roots. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C20

theorem e7_counts_checked : e7Roots.all (checkNeighborCount 4 32 e7Roots) = true := by
  apply all_eq_true_of_chunks (chunk := fun k => e7Roots.drop (20 * k) |>.take 20)
    (m := 7) (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 7).all e7Chunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    e7_chunk_0,
    e7_chunk_1,
    e7_chunk_2,
    e7_chunk_3,
    e7_chunk_4,
    e7_chunk_5,
    e7_chunk_6, Bool.and_self]

end Computations.C20

namespace LineSystem

/-- C20: every root of E7 has 32 roots at inner product one. -/
theorem E₇.card_N {r} (hr : r ∈ E₇.Φ) : (E₇.N r).ncard = 32 := by
  apply E₇.tableModel.card_N_of_check (Equiv.refl (Fin 126)) C20.e7Roots
    (by decide +kernel) C20.e7_counts_checked hr

/-- The apex used in the Sage C20 pairs. -/
noncomputable def E₇.neighborApex : EuclideanSpace ℝ (Fin 8) :=
  integerVector E₇.tableModel.c (E₇.tableModel.v (115 : Fin 126))

/-- The two roots of each pair, as integer root indices. -/
def E₇.neighborPairLabel (p : Fin 16 × Bool) : Fin 126 :=
  ⟨(C20.e7Pairs[p.1.val]?.getD [])[if p.2 then 1 else 0]?.getD 0 % 126,
    Nat.mod_lt _ (by decide)⟩

/-- The pairs enumerate exactly N at the certified apex. -/
noncomputable def E₇.neighborPairs : (Fin 16 × Bool) ≃ E₇.N E₇.neighborApex :=
  E₇.tableModel.subsetEquiv _ (fun _ h => h.1) E₇.neighborPairLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      change (_ ∧ _) ↔ _
      rw [and_iff_right (E₇.tableModel.root_mem i)]
      change (⟪integerVector E₇.tableModel.c (E₇.tableModel.v i),
        integerVector E₇.tableModel.c (E₇.tableModel.v (115 : Fin 126))⟫ = 1) ↔ _
      rw [E₇.tableModel.inner_eq_one_iff]
      exact (by decide +kernel : ∀ i : Fin 126,
        integerInner (E₇.tableModel.v i) (E₇.tableModel.v (115 : Fin 126)) = 4 ↔
          ∃ p, E₇.neighborPairLabel p = i) i)

/-- The two roots of each enumerated pair sum to the apex. -/
theorem E₇.neighborPairs_add (i : Fin 16) :
    (E₇.neighborPairs (i, false) : EuclideanSpace ℝ (Fin 8)) +
      E₇.neighborPairs (i, true) = E₇.neighborApex := by
  change integerVector E₇.tableModel.c
    (E₇.tableModel.v (E₇.neighborPairLabel (i, false))) +
    integerVector E₇.tableModel.c
      (E₇.tableModel.v (E₇.neighborPairLabel (i, true))) = _
  rw [← integerVector_add]
  apply congrArg (integerVector E₇.tableModel.c)
  exact (by decide +kernel : ∀ j : Fin 16,
    E₇.tableModel.v (E₇.neighborPairLabel (j, false)) +
      E₇.tableModel.v (E₇.neighborPairLabel (j, true)) =
        E₇.tableModel.v (115 : Fin 126)) i

end LineSystem
