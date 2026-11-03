/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Hyp24
import LineGraphs.Graphs.TriangleProperty

/-! # The triangle property of the orthogonality graph, after Lemma 2.8 of [CGSS] -/

open scoped RealInnerProductSpace

namespace LineSystem.Hyp24

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (H : Hyp24 V)

-- Lemma 2.8 (corollary)
/-- Corollary of Lemma 2.8 of [CGSS] (`cor:triangle-property`): the orthogonality graph
has the triangle property. No ambient finite-dimensionality assumption is needed. -/
theorem orthGraph_hasTriangleProperty : H.orthGraph.HasTriangleProperty := by
  intro x y hxy
  -- ⟨1⟩1 (28triangle), ⟨2⟩1 (28products).
  let z : H.Γa := ⟨H.third x y, H.third_mem_Γa x.property y.property hxy⟩
  have hxz : H.orthGraph.Adj x z := H.inner_third_left x.property hxy
  have hyz : H.orthGraph.Adj y z := H.inner_third_right y.property hxy
  have hout (w : H.Γa) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
      (H.orthGraph.Adj w x ∧ ¬H.orthGraph.Adj w y ∧ ¬H.orthGraph.Adj w z) ∨
      (¬H.orthGraph.Adj w x ∧ H.orthGraph.Adj w y ∧ ¬H.orthGraph.Adj w z) ∨
      (¬H.orthGraph.Adj w x ∧ ¬H.orthGraph.Adj w y ∧ H.orthGraph.Adj w z) := by
    have h := (H.triangle x.property y.property hxy).2 w w.property
      (fun he ↦ hwx (Subtype.ext he)) (fun he ↦ hwy (Subtype.ext he))
      (fun he ↦ hwz (Subtype.ext he))
    rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;>
      simp only [orthGraph_adj, z, hx, hy, hz, one_ne_zero, not_false_eq_true,
        and_self, or_true, true_or]
  refine ⟨z, hxz, hyz, ?_, hout⟩
  -- ⟨1⟩2 (28unique).
  intro w hxw hyw
  by_contra hwz
  have h := hout w hxw.ne.symm hyw.ne.symm hwz
  rcases h with h | h | h
  · exact h.2.1 hyw.symm
  · exact h.1 hxw.symm
  · exact h.1 hxw.symm

-- Lemma 2.9
/-- Lemma 2.9 of [CGSS] (`lem:2.9`): a universal vertex partitions all remaining
vertices into the triangles of a friendship graph. The case of one vertex has `m = 0`. -/
theorem orthGraph_iso_friendship_of_forall_adj (x : H.Γa)
    (hx : ∀ y, y ≠ x → H.orthGraph.Adj x y) :
    ∃ m, Nonempty (H.orthGraph ≃g SimpleGraph.friendship m) :=
  -- Steps 29mate, 29pairs and 29edges are proved in the pure graph lemma.
  H.orthGraph_hasTriangleProperty.nonempty_iso_friendship_of_forall_adj x hx

end LineSystem.Hyp24
