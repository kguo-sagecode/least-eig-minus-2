/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20D9Rows00
import LineGraphs.Computations.C20D9Rows01
import LineGraphs.Computations.C20D9Rows02
import LineGraphs.Computations.C20D9Rows03
import LineGraphs.Computations.C20D9Rows04
import LineGraphs.Computations.C20D9Rows05
import LineGraphs.Computations.C20D9Rows06
import LineGraphs.Computations.C20D9Rows07
import LineGraphs.Computations.NeighborCertificates

/-!
# C20 D9 neighborhoods

C20 for D9, transferred to neighborhoods of real roots. -/

open Computations
open scoped RealInnerProductSpace

namespace Computations.C20

theorem d9_counts_checked : d9Roots.all (checkNeighborCount 1 28 d9Roots) = true := by
  apply all_eq_true_of_chunks (chunk := fun k => d9Roots.drop (20 * k) |>.take 20)
    (m := 8) (by decide +kernel)
  apply List.all_eq_true.mp
  change (List.range 8).all d9Chunk = true
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    d9_chunk_0,
    d9_chunk_1,
    d9_chunk_2,
    d9_chunk_3,
    d9_chunk_4,
    d9_chunk_5,
    d9_chunk_6,
    d9_chunk_7, Bool.and_self]

/-- The finite integer model in the certificate's order. -/
@[reducible] noncomputable def d9Model : LineSystem.IntegerModel (LineSystem.Dn 9) :=
  (LineSystem.Dn.integerModel 9).ofTable d9Roots 144 (by decide +kernel)
    (by decide +kernel) (by
      have he : d9Roots = LineSystem.Dn.rootList 9 := by decide +kernel
      intro w
      rw [he]
      exact LineSystem.Dn.mem_rootList 9 w)

end Computations.C20

namespace LineSystem

/-- C20: every root of D9 has 28 roots at inner product one. -/
theorem Dn.card_N_nine {r} (hr : r ∈ (Dn 9).Φ) : ((Dn 9).N r).ncard = 28 := by
  apply C20.d9Model.card_N_of_check (Equiv.refl (Fin 144)) C20.d9Roots
    (by decide +kernel) C20.d9_counts_checked hr

end LineSystem
