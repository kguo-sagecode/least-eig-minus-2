/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.Seidel.Switching
import LineGraphs.Seidel.LineGraphRecognition

/-! # Switching representations and recognizing cycles

Lemma `lem:4-switch` of the Section 4 blueprint for [CGSS]: replacing selected roots
`x u` by `h - x u` realizes graph switching within a star-closed line system.
The cycle recognition lemma `lem:cycle` of Section 5 reuses the general theorem from
`Seidel/LineGraphRecognition.lean`, adding the explicit lower bound on the order.
-/

open scoped RealInnerProductSpace

namespace SimpleGraph

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

-- Lemma (switching by vectors, SW4), Section 4
/-- Lemma (switching by vectors, SW4), `lem:4-switch` of `blueprint/sec4-leasteigenvalue.tex`,
used for [CGSS] Section 4: switching selected representing roots to `h - x u` represents the
switched graph, with all vectors still in the star-closed line system. -/
theorem IsRepresentation.switch [DecidableEq V] (hx : X.IsRepresentation x)
    {S : LineSystem E} (hS : S.IsStarClosed) (hxS : ∀ u, x u ∈ S.Φ)
    {h : E} (hh : h ∈ S.Φ) (hhx : ∀ u, ⟪h, x u⟫ = 1)
    (U : Set V) [DecidablePred (· ∈ U)] :
    (X.switch U).IsRepresentation (fun u ↦ if u ∈ U then h - x u else x u) ∧
      ∀ u, (if u ∈ U then h - x u else x u) ∈ S.Φ := by
  -- Step s4swmem: star closure gives x u - h, and negation gives h - x u.
  have hmem (u : V) : h - x u ∈ S.Φ := by
    have hip : ⟪x u, -h⟫ = -1 := by
      rw [inner_neg_right, real_inner_comm, hhx]
    have hs := hS (x u) (hxS u) (-h) (S.neg_mem h hh) hip
    simpa only [neg_add_rev, neg_neg, sub_eq_add_neg] using S.neg_mem _ hs
  -- Step s4swip: products within the switching set stay fixed.
  have hsame (u v : V) : ⟪h - x u, h - x v⟫ = ⟪x u, x v⟫ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, S.inner_self h hh,
      hhx, real_inner_comm h (x u), hhx]
    ring
  -- Products across the cut exchange zero and one.
  have hcross (u v : V) : ⟪h - x u, x v⟫ = 1 - ⟪x u, x v⟫ := by
    rw [inner_sub_left, hhx]
  -- The final `\qedstep` packages the switched representation and root membership.
  constructor
  · apply isRepresentation_iff.mpr
    intro u v
    by_cases huv : u = v
    · subst v
      by_cases hu : u ∈ U <;> simp only [hu, ↓reduceIte, hsame, hx.inner_self]
    · by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;> by_cases ha : X.Adj u v <;>
        simp [hu, hv, huv, ha, switch_adj, hsame, hcross, inner_sub_right,
          real_inner_comm h (x u), hhx, isRepresentation_iff.mp hx u v]
  · intro u
    split_ifs
    · exact hmem u
    · exact hxS u

-- Lemma (connected 2-regular graphs), Section 5
/-- Lemma (connected 2-regular graphs), `lem:cycle` of `blueprint/sec5-spectral.tex`
(errata Gap 16): a finite connected 2-regular graph has at least three vertices and is
isomorphic to the cycle on its number of vertices. -/
theorem nonempty_iso_cycleGraph [Fintype V] (hc : X.Connected)
    (hr : X.IsRegularOfDegree 2) :
    3 ≤ Fintype.card V ∧ Nonempty (X ≃g cycleGraph (Fintype.card V)) := by
  obtain ⟨v⟩ := hc.nonempty
  have hlt := X.degree_lt_card_verts v
  rw [hr v] at hlt
  exact ⟨hlt, hr.nonempty_iso_cycle hc⟩

end SimpleGraph
