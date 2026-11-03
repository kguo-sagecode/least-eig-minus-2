/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20E6Rows00
import LineGraphs.Computations.C20E6Rows01
import LineGraphs.Computations.C20E6Rows02
import LineGraphs.Computations.C20E6Rows03
import LineGraphs.Computations.NeighborCertificates
import LineGraphs.Computations.C4E6

/-!
# C20 E6 neighborhoods

C20 for E6, transferred to neighborhoods of real roots. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C20

theorem e6_counts_checked : e6Roots.all (checkNeighborCount 4 20 e6Roots) = true := by
  apply all_eq_true_of_chunks (chunk := fun k => e6Roots.drop (20 * k) |>.take 20)
    (m := 4) (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 4).all e6Chunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    e6_chunk_0,
    e6_chunk_1,
    e6_chunk_2,
    e6_chunk_3, Bool.and_self]

end Computations.C20

namespace LineSystem

/-- C20: every root of E6 has 20 roots at inner product one. -/
theorem E₆.card_N {r} (hr : r ∈ E₆.Φ) : (E₆.N r).ncard = 20 := by
  apply E₆.tableModel.card_N_of_check (Equiv.refl (Fin 72)) C20.e6Roots
    (by decide +kernel) C20.e6_counts_checked hr

/-- The apex used in the Sage C20 pairs. -/
noncomputable def E₆.neighborApex : EuclideanSpace ℝ (Fin 8) :=
  integerVector E₆.tableModel.c (E₆.tableModel.v (63 : Fin 72))

/-- The two roots of each pair, as integer root indices. -/
def E₆.neighborPairLabel (p : Fin 10 × Bool) : Fin 72 :=
  ⟨(C20.e6Pairs[p.1.val]?.getD [])[if p.2 then 1 else 0]?.getD 0 % 72,
    Nat.mod_lt _ (by decide)⟩

/-- The pairs enumerate exactly N at the certified apex. -/
noncomputable def E₆.neighborPairs : (Fin 10 × Bool) ≃ E₆.N E₆.neighborApex :=
  E₆.tableModel.subsetEquiv _ (fun _ h => h.1) E₆.neighborPairLabel
    (by unfold Function.Injective; decide +kernel) (by
      intro i
      change (_ ∧ _) ↔ _
      rw [and_iff_right (E₆.tableModel.root_mem i)]
      change (⟪integerVector E₆.tableModel.c (E₆.tableModel.v i),
        integerVector E₆.tableModel.c (E₆.tableModel.v (63 : Fin 72))⟫ = 1) ↔ _
      rw [E₆.tableModel.inner_eq_one_iff]
      exact (by decide +kernel : ∀ i : Fin 72,
        integerInner (E₆.tableModel.v i) (E₆.tableModel.v (63 : Fin 72)) = 4 ↔
          ∃ p, E₆.neighborPairLabel p = i) i)

/-- The two roots of each enumerated pair sum to the apex. -/
theorem E₆.neighborPairs_add (i : Fin 10) :
    (E₆.neighborPairs (i, false) : EuclideanSpace ℝ (Fin 8)) +
      E₆.neighborPairs (i, true) = E₆.neighborApex := by
  change integerVector E₆.tableModel.c
    (E₆.tableModel.v (E₆.neighborPairLabel (i, false))) +
    integerVector E₆.tableModel.c
      (E₆.tableModel.v (E₆.neighborPairLabel (i, true))) = _
  rw [← integerVector_add]
  apply congrArg (integerVector E₆.tableModel.c)
  exact (by decide +kernel : ∀ j : Fin 10,
    E₆.tableModel.v (E₆.neighborPairLabel (j, false)) +
      E₆.tableModel.v (E₆.neighborPairLabel (j, true)) =
        E₆.tableModel.v (63 : Fin 72)) i

end LineSystem
