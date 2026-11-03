/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20E8Rows00
import LineGraphs.Computations.C20E8Rows01
import LineGraphs.Computations.C20E8Rows02
import LineGraphs.Computations.C20E8Rows03
import LineGraphs.Computations.C20E8Rows04
import LineGraphs.Computations.C20E8Rows05
import LineGraphs.Computations.C20E8Rows06
import LineGraphs.Computations.C20E8Rows07
import LineGraphs.Computations.C20E8Rows08
import LineGraphs.Computations.C20E8Rows09
import LineGraphs.Computations.C20E8Rows10
import LineGraphs.Computations.C20E8Rows11
import LineGraphs.Computations.NeighborCertificates
import LineGraphs.Computations.C4E8

/-!
# C20 E8 neighborhoods

C20 for E8, transferred to neighborhoods of real roots. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C20

theorem e8_counts_checked : e8Roots.all (checkNeighborCount 4 56 e8Roots) = true := by
  apply all_eq_true_of_chunks (chunk := fun k => e8Roots.drop (20 * k) |>.take 20)
    (m := 12) (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 12).all e8Chunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    e8_chunk_0,
    e8_chunk_1,
    e8_chunk_2,
    e8_chunk_3,
    e8_chunk_4,
    e8_chunk_5,
    e8_chunk_6,
    e8_chunk_7,
    e8_chunk_8,
    e8_chunk_9,
    e8_chunk_10,
    e8_chunk_11, Bool.and_self]

end Computations.C20

namespace LineSystem

/-- C20: every root of E8 has 56 roots at inner product one. -/
theorem E₈.card_N {r} (hr : r ∈ E₈.Φ) : (E₈.N r).ncard = 56 := by
  apply E₈.tableModel.card_N_of_check (Equiv.refl (Fin 240)) C20.e8Roots
    (by decide +kernel) C20.e8_counts_checked hr

/-- The apex used in the Sage C20 pairs. -/
noncomputable def E₈.neighborApex : EuclideanSpace ℝ (Fin 8) :=
  integerVector E₈.tableModel.c (E₈.tableModel.v (225 : Fin 240))

/-- The two roots of each pair, as integer root indices. -/
def E₈.neighborPairLabel (p : Fin 28 × Bool) : Fin 240 :=
  ⟨(C20.e8Pairs[p.1.val]?.getD [])[if p.2 then 1 else 0]?.getD 0 % 240,
    Nat.mod_lt _ (by decide)⟩

/-- The pairs enumerate exactly N at the certified apex. -/
noncomputable def E₈.neighborPairs : (Fin 28 × Bool) ≃ E₈.N E₈.neighborApex :=
  E₈.tableModel.subsetEquiv _ (fun _ h => h.1) E₈.neighborPairLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      change (_ ∧ _) ↔ _
      rw [and_iff_right (E₈.tableModel.root_mem i)]
      change (⟪integerVector E₈.tableModel.c (E₈.tableModel.v i),
        integerVector E₈.tableModel.c (E₈.tableModel.v (225 : Fin 240))⟫ = 1) ↔ _
      rw [E₈.tableModel.inner_eq_one_iff]
      exact (by decide +kernel : ∀ i : Fin 240,
        integerInner (E₈.tableModel.v i) (E₈.tableModel.v (225 : Fin 240)) = 4 ↔
          ∃ p, E₈.neighborPairLabel p = i) i)

/-- The two roots of each enumerated pair sum to the apex. -/
theorem E₈.neighborPairs_add (i : Fin 28) :
    (E₈.neighborPairs (i, false) : EuclideanSpace ℝ (Fin 8)) +
      E₈.neighborPairs (i, true) = E₈.neighborApex := by
  change integerVector E₈.tableModel.c
    (E₈.tableModel.v (E₈.neighborPairLabel (i, false))) +
    integerVector E₈.tableModel.c
      (E₈.tableModel.v (E₈.neighborPairLabel (i, true))) = _
  rw [← integerVector_add]
  apply congrArg (integerVector E₈.tableModel.c)
  exact (by decide +kernel : ∀ j : Fin 28,
    E₈.tableModel.v (E₈.neighborPairLabel (j, false)) +
      E₈.tableModel.v (E₈.neighborPairLabel (j, true)) =
        E₈.tableModel.v (225 : Fin 240)) i

end LineSystem
