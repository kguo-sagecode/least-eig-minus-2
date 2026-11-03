/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20A9Rows00
import LineGraphs.Computations.C20A9Rows01
import LineGraphs.Computations.C20A9Rows02
import LineGraphs.Computations.C20A9Rows03
import LineGraphs.Computations.C20A9Rows04
import LineGraphs.Computations.NeighborCertificates

/-!
# C20 A9 neighborhoods

C20 for A9, transferred to neighborhoods of real roots. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C20

theorem a9_counts_checked : a9Roots.all (checkNeighborCount 1 16 a9Roots) = true := by
  apply all_eq_true_of_chunks (chunk := fun k => a9Roots.drop (20 * k) |>.take 20)
    (m := 5) (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 5).all a9Chunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    a9_chunk_0,
    a9_chunk_1,
    a9_chunk_2,
    a9_chunk_3,
    a9_chunk_4, Bool.and_self]

/-- The finite integer model in the certificate's order. -/
@[reducible] noncomputable def a9Model : LineSystem.IntegerModel (LineSystem.An 9) :=
  (LineSystem.An.integerModel 9).ofTable a9Roots 90 (by decide +kernel)
    (by decide +kernel) (by
      have he : a9Roots = LineSystem.An.rootList 9 := by decide +kernel
      intro w
      rw [he]
      exact LineSystem.An.mem_rootList 9 w)

end Computations.C20

namespace LineSystem

/-- C20: every root of A9 has 16 roots at inner product one. -/
theorem An.card_N_nine {r} (hr : r ∈ (An 9).Φ) : ((An 9).N r).ncard = 16 := by
  apply C20.a9Model.card_N_of_check (Equiv.refl (Fin 90)) C20.a9Roots
    (by decide +kernel) C20.a9_counts_checked hr

end LineSystem
