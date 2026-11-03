/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Apex
import LineGraphs.Seidel.Switching
import LineGraphs.Seidel.RootTransitivity
import LineGraphs.Representation.LineGraph

/-! # Switching from the apex

Lemma `lem:414-transversal` of Remark 4.14 of [CGSS].
-/

open scoped RealInnerProductSpace
open Submodule

namespace SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Step `s414trw` of `lem:414-transversal`: maximality turns a norm-two apex into a root. -/
theorem IsRepresentation.apex_mem_latticeRoots (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) (hm : hx.latticeRoots.IsMaximal)
    (hn : ⟪hx.apex k, hx.apex k⟫ = 2) : hx.apex k ∈ hx.latticeRoots.Φ := by
  apply hm _ (by rw [hx.span_latticeRoots]; exact hx.apex_mem_span k) hn
  intro y hy
  exact inner_mem_five_of_mem_int hn hy.2 (hx.inner_apex_mem_int hr hy.1)

/-- Steps `s414trinj`--`s414tradj` of `lem:414-transversal`: choosing one vector from
each pair `r, c - r` gives a switching of the graph represented by the `r`. -/
theorem IsRepresentation.nonempty_iso_switch_of_pairs (hx : X.IsRepresentation x)
    {P : Type*} [Fintype P] [DecidableEq P] (Y : SimpleGraph P) [DecidableRel Y.Adj]
    (r : P → E) (hy : Y.IsRepresentation r) (c : E) (hc : ⟪c, c⟫ = 2)
    (hcr : ∀ p, ⟪c, r p⟫ = 1) (hp : ∀ u, ∃ p, x u = r p ∨ x u = c - r p)
    (hn : Fintype.card V = Fintype.card P) : ∃ H : Set P, Nonempty (X ≃g Y.switch H) := by
  have hchoose (u : V) : ∃ (p : P) (s : Bool), x u = if s then c - r p else r p := by
    obtain ⟨p, h | h⟩ := hp u
    · exact ⟨p, false, h⟩
    · exact ⟨p, true, h⟩
  choose p s hs using hchoose
  have hrc (p : P) : ⟪r p, c⟫ = 1 := by rw [real_inner_comm, hcr]
  have hc' : ‖c‖ ^ 2 = 2 := by simpa only [real_inner_self_eq_norm_sq] using hc
  have hip (u v : V) : ⟪x u, x v⟫ =
      if s u = s v then ⟪r (p u), r (p v)⟫ else 1 - ⟪r (p u), r (p v)⟫ := by
    rw [hs u, hs v]
    cases s u <;> cases s v <;>
      simp [inner_sub_left, inner_sub_right, hc', hcr, hrc]
    ring
  have hpi : Function.Injective p := by
    intro u v huv
    by_cases hsign : s u = s v
    · apply hx.injective
      rw [hs u, hs v, huv, hsign]
    · have hnonneg := hx.inner_nonneg u v
      rw [hip, ite_eq_right hsign, huv, hy.inner_self] at hnonneg
      norm_num at hnonneg
  have hps := (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hn)).mp hpi
  let f : V ≃ P := Equiv.ofBijective p ⟨hpi, hps⟩
  let H : Set P := f '' {u | s u = true}
  have hH (u : V) : f u ∈ H ↔ s u = true := by
    simp only [H, Set.mem_image, Set.mem_ofPred_eq, f.injective.eq_iff, exists_eq_right]
  refine ⟨H, ⟨{ toEquiv := f, map_rel_iff' := ?_ }⟩⟩
  intro u v
  rw [switch_adj, f.injective.ne_iff, hH, hH]
  by_cases huv : u = v
  · subst v
    simp
  have hpv : p u ≠ p v := hpi.ne huv
  have hxu := isRepresentation_iff.mp hx u v
  have hyr := isRepresentation_iff.mp hy (p u) (p v)
  rw [ite_eq_right huv] at hxu
  rw [ite_eq_right hpv] at hyr
  have hrel := hip u v
  rw [hxu, hyr] at hrel
  change (u ≠ v ∧ (Y.Adj (p u) (p v) ↔ (s u = true ↔ s v = true))) ↔ X.Adj u v
  cases hsu : s u <;> cases hsv : s v <;> by_cases ha : X.Adj u v <;>
    by_cases hb : Y.Adj (p u) (p v) <;> simp [huv, hsu, hsv, ha, hb] at hrel ⊢

-- Lemma (switching from the apex), for Remark 4.14 of [CGSS]
/-- Lemma `lem:414-transversal`, Remark 4.14: a norm-two apex and the C20 enumeration
of its pairs give an isomorphism with a switched line graph. The model hypotheses
are maximality, root transitivity, and the explicit two roots over each edge. -/
theorem IsRepresentation.nonempty_iso_lineGraph_switch (hx : X.IsRepresentation x) {k : ℕ}
    (hr : X.IsRegularOfDegree k) {W : Type*} [Fintype W] [DecidableEq W]
    (S : LineSystem (EuclideanSpace ℝ W)) (e : hx.latticeRoots.Iso S)
    (hmax : S.IsMaximal) (c : EuclideanSpace ℝ W) (hc : c ∈ S.Φ)
    (ht : ∀ z ∈ S.Φ, ∃ g ∈ S.isometryGroup, g z = c)
    (Y : SimpleGraph W) [DecidableRel Y.Adj]
    (hp : ∀ z ∈ S.N c, ∃ p : Y.edgeSet,
      z = Y.lineGraphVector p ∨ z = c - Y.lineGraphVector p)
    (hcr : ∀ p : Y.edgeSet, ⟪c, Y.lineGraphVector p⟫ = 1)
    (hw : ⟪hx.apex k, hx.apex k⟫ = 2) (hn : Fintype.card V = Fintype.card Y.edgeSet) :
    ∃ H : Set Y.edgeSet, Nonempty (X ≃g Y.lineGraph.switch H) := by
  classical
  have hwroot := hx.apex_mem_latticeRoots hr (e.isMaximal hmax) hw
  let w : hx.latticeRoots.Φ := ⟨hx.apex k, hwroot⟩
  obtain ⟨g, hg, hgw⟩ := ht (e.toEquiv w) (e.toEquiv w).property
  let y : V → EuclideanSpace ℝ W := fun u ↦ g (e.toEquiv ⟨x u, hx.mem_latticeRoots u⟩)
  have hy : X.IsRepresentation y := by
    apply isRepresentation_iff.mpr
    intro u v
    change ⟪g _, g _⟫ = _
    rw [g.inner_map_map, e.inner_map]
    exact isRepresentation_iff.mp hx u v
  have hymem (u : V) : y u ∈ S.N c := by
    refine ⟨(hg _).mpr (e.toEquiv ⟨x u, hx.mem_latticeRoots u⟩).property, ?_⟩
    rw [← hgw]
    change ⟪g _, g _⟫ = _
    rw [g.inner_map_map, e.inner_map, real_inner_comm]
    exact hx.inner_apex hr u
  exact hy.nonempty_iso_switch_of_pairs Y.lineGraph Y.lineGraphVector
    Y.lineGraph_isRepresentation c (S.inner_self c hc) hcr
    (fun u ↦ hp (y u) (hymem u)) hn

end SimpleGraph
