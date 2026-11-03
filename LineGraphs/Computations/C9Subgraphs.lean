/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9ChangI
import LineGraphs.Computations.C9Shrikhande
import LineGraphs.Computations.C9Schlafli
import LineGraphs.Computations.C9Clebsch

/-! # The induced subgraphs in [CGSS], Examples 4.7 and 4.8 -/

namespace SimpleGraph

set_option maxRecDepth 4000

-- Example 4.7
/-- Example 4.7 of [CGSS]: the Shrikhande rows among the Chang I rows. -/
def shrikhande.changIIndex : Fin 16 → Fin 28 :=
  ![3, 4, 5, 6, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21]

-- Example 4.7
/-- Example 4.7 of [CGSS]: the row map is injective and preserves and reflects adjacency. -/
theorem shrikhande.changIIndex_checked : Function.Injective shrikhande.changIIndex ∧
    ∀ i j, changI.Adj (shrikhande.changIIndex i) (shrikhande.changIIndex j) ↔
      shrikhande.Adj i j := by
  decide +kernel

-- Example 4.7
/-- Example 4.7 of [CGSS]: Shrikhande is an induced subgraph of Chang I. -/
def shrikhande.changIEmbedding : shrikhande ↪g changI where
  toFun := shrikhande.changIIndex
  inj' := shrikhande.changIIndex_checked.1
  map_rel_iff' := shrikhande.changIIndex_checked.2 _ _

-- Example 4.7
/-- Example 4.7 of [CGSS]: the induced subgraph on the specified Chang I rows is Shrikhande. -/
theorem shrikhande.nonempty_iso_induce_changI :
    Nonempty (shrikhande ≃g changI.induce (Set.range shrikhande.changIIndex)) :=
  ⟨shrikhande.changIEmbedding.isoInduceRange⟩

-- Example 4.8
/-- Example 4.8 of [CGSS]: the Clebsch rows among the Schläfli rows. -/
def clebsch.schlafliIndex : Fin 16 → Fin 27 :=
  ![3, 7, 10, 12, 4, 8, 11, 13, 15, 16, 17, 18, 21, 22, 23, 24]

-- Example 4.8
/-- Example 4.8 of [CGSS]: the row map is an induced embedding onto the neighbours of
row 14, whose vector is `e₅ + e₆` (the integer table is scaled by two). -/
theorem clebsch.schlafliIndex_checked : Function.Injective clebsch.schlafliIndex ∧
    (∀ i j, schlafli.Adj (clebsch.schlafliIndex i) (clebsch.schlafliIndex j) ↔
      clebsch.Adj i j) ∧
    (∀ j, (∃ i, clebsch.schlafliIndex i = j) ↔ schlafli.Adj 14 j) ∧
    Computations.C9.schlafliVectors 14 = ![0, 0, 0, 0, 2, 2, 0, 0] := by
  decide +kernel

-- Example 4.8
/-- Example 4.8 of [CGSS]: Clebsch is an induced subgraph of Schläfli. -/
def clebsch.schlafliEmbedding : clebsch ↪g schlafli where
  toFun := clebsch.schlafliIndex
  inj' := clebsch.schlafliIndex_checked.1
  map_rel_iff' := clebsch.schlafliIndex_checked.2.1 _ _

-- Example 4.8
/-- Example 4.8 of [CGSS]: Clebsch is the subgraph induced by the neighbours of `e₅ + e₆`. -/
theorem clebsch.nonempty_iso_induce_schlafli :
    Nonempty (clebsch ≃g schlafli.induce (schlafli.neighborSet 14)) := by
  have hr : Set.range clebsch.schlafliIndex = schlafli.neighborSet 14 :=
    Set.ext clebsch.schlafliIndex_checked.2.2.1
  rw [← hr]
  exact ⟨clebsch.schlafliEmbedding.isoInduceRange⟩

end SimpleGraph
