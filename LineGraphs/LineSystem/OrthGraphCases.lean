/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.OrthGraphParameters

/-! # The alternatives in [CGSS, Lemma 2.12] -/

open scoped RealInnerProductSpace

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Lemma 2.12
/-- Step 212star of `lem:2.12` ([CGSS, Lemma 2.12]): a nonempty indecomposable
star-closed system is one antipodal pair or admits Hypothesis 2.4. Nonemptiness and the
separate one-line case implement errata Implicit hypothesis 4. -/
theorem IsIndecomposable.eq_pair_or_exists_hyp24 {S : LineSystem V}
    (hI : S.IsIndecomposable) (hNE : S.Φ.Nonempty) (hSC : S.IsStarClosed) :
    (∃ r ∈ S.Φ, S.Φ = {r, -r}) ∨ ∃ H : Hyp24 V, H.S = S := by
  classical
  obtain ⟨r, hr⟩ := hNE
  by_cases ho : ∀ s ∈ S.Φ, s ∉ ({r, -r} : Set V) → ⟪r, s⟫ = 0
  · -- 212split: the pair and its complement are an orthogonal partition.
    have hp : ({r, -r} : Set V) ⊆ S.Φ := by
      rintro x (rfl | hx)
      · exact hr
      · exact Set.mem_singleton_iff.mp hx ▸ S.neg_mem r hr
    have hcover : ({r, -r} : Set V) ∪ (S.Φ \ {r, -r}) = S.Φ := by
      ext x
      simp only [Set.mem_union, Set.mem_sdiff]
      exact ⟨fun h ↦ h.elim (hp ·) And.left, fun hx ↦ by tauto⟩
    have horth : ∀ p ∈ ({r, -r} : Set V), ∀ q ∈ S.Φ \ {r, -r}, ⟪p, q⟫ = 0 := by
      rintro p (rfl | hp) q hq
      · exact ho q hq.1 hq.2
      · rw [Set.mem_singleton_iff] at hp
        rw [hp, inner_neg_left, ho q hq.1 hq.2, neg_zero]
    rcases hI _ _ hcover horth with hempty | hempty
    · have : r ∈ (∅ : Set V) := hempty ▸ Set.mem_insert r {-r}
      exact this.elim
    · refine Or.inl ⟨r, hr, ?_⟩
      rw [hempty, Set.union_empty] at hcover
      exact hcover.symm
  · -- 212orient: orient a nonorthogonal root on a different line to product `-1`.
    push Not at ho
    obtain ⟨s, hs, hsp, hrs⟩ := ho
    have hne : r ≠ s := fun he ↦ hsp (Or.inl he.symm)
    have hneg : r ≠ -s := fun he ↦ hsp (Or.inr
      (Set.mem_singleton_iff.mpr (by simpa using congrArg Neg.neg he.symm)))
    rcases S.inner_eq_neg_one_or_zero_or_one hr hs hne hneg with h | h | h
    · exact Or.inr ⟨⟨S, hI, hSC, r, s, hr, hs, h⟩, rfl⟩
    · exact False.elim (hrs h)
    · refine Or.inr ⟨⟨S, hI, hSC, r, -s, hr, S.neg_mem s hs, ?_⟩, rfl⟩
      rw [inner_neg_right, h]

namespace Hyp24

-- Lemma 2.12
/-- Steps 212empty–212remaining of `lem:2.12` ([CGSS, Lemma 2.12]): every chosen-star
orthogonality graph is empty, a friendship graph with at least one triangle, or one of
the three strongly regular possibilities, with all four parameters (errata Error 12). -/
theorem orthGraph_cases (H : Hyp24 V) :
    H.orthGraph = ⊥ ∨
    (∃ m, 1 ≤ m ∧ Nonempty (H.orthGraph ≃g SimpleGraph.friendship m)) ∨
    H.orthGraph.IsSRGWith 9 4 1 2 ∨ H.orthGraph.IsSRGWith 15 6 1 3 ∨
    H.orthGraph.IsSRGWith 27 10 1 5 := by
  classical
  -- 212graphs: existence of an edge and of a universal vertex exhaust the cases.
  by_cases he : ∃ x y, H.orthGraph.Adj x y
  · by_cases hu : ∃ x, ∀ y, y ≠ x → H.orthGraph.Adj x y
    · -- 212universal: an edge excludes the zero-triangle friendship graph.
      obtain ⟨x, hx⟩ := hu
      obtain ⟨m, ⟨e⟩⟩ := H.orthGraph_iso_friendship_of_forall_adj x hx
      refine Or.inr (Or.inl ⟨m, ?_, ⟨e⟩⟩)
      by_contra hm
      have hm0 : m = 0 := by omega
      subst m
      obtain ⟨p, q, hpq⟩ := he
      exact (e.map_rel_iff.mpr hpq).ne (Subsingleton.elim _ _)
    · -- 212remaining: no universal vertex implies noncompleteness.
      push Not at hu
      have hnc : H.orthGraph ≠ ⊤ := by
        intro hc
        obtain ⟨x, y, hxy⟩ := he
        obtain ⟨z, hzx, hxz⟩ := hu x
        exact hxz (by simpa only [hc, SimpleGraph.top_adj] using hzx.symm)
      obtain ⟨k, hk, hreg⟩ := H.orthGraph_isSRGWith he hnc hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by simpa using hreg)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hreg))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hreg))))
  · -- 212empty: the finite graph has no edges, including the empty vertex set.
    left
    ext x y
    exact iff_of_false (fun h ↦ he ⟨x, y, h⟩) (by simp)

end Hyp24
end LineSystem
