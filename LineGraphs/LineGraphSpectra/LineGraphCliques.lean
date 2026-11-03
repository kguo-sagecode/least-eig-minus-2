/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignGraphs

/-!
# A clique obstruction for Example 5.13

Step `s5exnoiso` of Example 5.13 (`ex:5.13`) of [CGSS]. For the regular root
constructed there, a star-size argument proves the required non-isomorphism
directly. Thus this instance does not require the deferred general EX4 theorem.
-/

namespace Sym2

variable {V : Type*}

/-- Pairwise intersecting edges with more than three members form a star;
the combinatorial input for `s5exnoiso`, Example 5.13 of [CGSS]. -/
theorem exists_common_mem_of_card_gt_three (S : Finset (Sym2 V)) (hcard : 3 < S.card)
    (hp : ∀ e ∈ S, ∀ f ∈ S, ∃ a, a ∈ e ∧ a ∈ f) :
    ∃ a, ∀ e ∈ S, a ∈ e := by
  classical
  obtain ⟨e, heS, f, hfS, hef⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨a, hae, haf⟩ := hp e heS f hfS
  let b := Sym2.Mem.other hae
  let c := Sym2.Mem.other haf
  have he : e = s(a, b) := (Sym2.other_spec hae).symm
  have hf : f = s(a, c) := (Sym2.other_spec haf).symm
  have hbc : b ≠ c := fun h ↦ hef (by rw [he, hf, h])
  have hother {d : Sym2 V} (hdS : d ∈ S) (had : a ∉ d) : d = s(b, c) := by
    obtain ⟨x, hxe, hxd⟩ := hp e heS d hdS
    obtain ⟨y, hyf, hyd⟩ := hp f hfS d hdS
    rw [he, Sym2.mem_iff] at hxe
    rw [hf, Sym2.mem_iff] at hyf
    have hb : b ∈ d := by
      rcases hxe with rfl | rfl
      · exact (had hxd).elim
      · exact hxd
    have hc : c ∈ d := by
      rcases hyf with rfl | rfl
      · exact (had hyd).elim
      · exact hyd
    exact (Sym2.mem_and_mem_iff hbc).mp ⟨hb, hc⟩
  by_cases hall : ∀ d ∈ S, a ∈ d
  · exact ⟨a, hall⟩
  · push Not at hall
    obtain ⟨g, hgS, hag⟩ := hall
    have hg := hother hgS hag
    have hab : a ≠ b := by intro h; apply hag; rw [hg, h]; simp
    have hac : a ≠ c := by intro h; apply hag; rw [hg, h]; simp
    have hsub : S ⊆ {e, f, g} := by
      intro d hdS
      by_cases had : a ∈ d
      · obtain ⟨x, hxg, hxd⟩ := hp g hgS d hdS
        rw [hg, Sym2.mem_iff] at hxg
        rcases hxg with rfl | rfl
        · have hd : d = e := (Sym2.mem_and_mem_iff hab).mp ⟨had, hxd⟩ |>.trans he.symm
          simp [hd]
        · have hd : d = f := (Sym2.mem_and_mem_iff hac).mp ⟨had, hxd⟩ |>.trans hf.symm
          simp [hd]
      · have hd : d = g := (hother hdS had).trans hg.symm
        simp [hd]
    have hle := Finset.card_le_card hsub
    have h₁ := Finset.card_insert_le e {f, g}
    have h₂ := Finset.card_insert_le f {g}
    have h₃ : ({g} : Finset (Sym2 V)).card = 1 := Finset.card_singleton g
    omega

end Sym2

namespace SimpleGraph

variable {V : Type*} [Fintype V] (Y : SimpleGraph V)
  [DecidableRel Y.Adj]

attribute [local instance] Classical.propDecidable

/-- The clique bound used in `s5exnoiso`, Example 5.13 of [CGSS]: for a graph
of maximum degree at most `d ≥ 3`, its line graph has no clique larger than `d`. -/
theorem card_clique_lineGraph_le {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ v, Y.degree v ≤ d)
    (S : Finset Y.edgeSet) (hS : Y.lineGraph.IsClique S) : S.card ≤ d := by
  classical
  by_cases hsmall : S.card ≤ 3
  · exact hsmall.trans hd
  · let T := S.image Subtype.val
    have hcard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
    obtain ⟨v, hv⟩ := Sym2.exists_common_mem_of_card_gt_three T (by omega) (by
      rintro e he f hf
      obtain ⟨e, heS, rfl⟩ := Finset.mem_image.mp (show e ∈ S.image Subtype.val from he)
      obtain ⟨f, hfS, rfl⟩ := Finset.mem_image.mp (show f ∈ S.image Subtype.val from hf)
      by_cases hef : e = f
      · subst f
        rcases e with ⟨⟨a, b⟩, _⟩
        exact ⟨a, by simp⟩
      · exact (lineGraph_adj_iff_exists.mp (hS heS hfS hef)).2)
    have hsub : T ⊆ Y.incidenceFinset v := by
      intro e he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (show e ∈ S.image Subtype.val from he)
      exact (Y.mem_incidenceFinset v f.val).mpr
        ⟨f.property, hv f.val (Finset.mem_image.mpr ⟨f, hf, rfl⟩)⟩
    have hle := Finset.card_le_card hsub
    rw [hcard, Y.card_incidenceFinset_eq_degree] at hle
    exact hle.trans (hdeg v)

end SimpleGraph

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ} (D : Design P B v k b r lam)

/-- A point star gives an `r`-clique (`s5exnoiso`, Example 5.13 of [CGSS]). -/
theorem exists_clique_flagGraph_card_replication :
    ∃ S : Finset D.incidenceGraph.edgeSet, D.flagGraph.IsClique S ∧ S.card = r := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by
    rw [D.card_points]; have := D.one_lt_v; omega)
  let p : P := Classical.arbitrary P
  let f : {a : B // p ∈ D.block a} ↪ D.incidenceGraph.edgeSet :=
    { toFun := fun a ↦ ⟨s(Sum.inl p, Sum.inr a.val), a.property⟩
      inj' := by
        intro a d he
        have he' := congrArg Subtype.val he
        simp only [Sym2.eq_iff, Sum.inr.injEq, Sum.inl_ne_inr,
          false_and, or_false, true_and] at he'
        exact Subtype.ext he' }
  refine ⟨Finset.univ.map f, ?_, ?_⟩
  · intro a ha d hd had
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hd
    apply SimpleGraph.lineGraph_adj_iff_exists.mpr
    refine ⟨had, Sum.inl p, ?_⟩
    change Sum.inl p ∈ s(Sum.inl p, Sum.inr a.val) ∧
      Sum.inl p ∈ s(Sum.inl p, Sum.inr d.val)
    simp
  · simp only [Finset.card_map, Finset.card_univ, Fintype.card_subtype]
    exact D.card_blocksThrough p

/-- The non-isomorphism in `s5exnoiso`, Example 5.13 of [CGSS], whenever the
design replication exceeds the maximum degree of the proposed regular root. -/
theorem not_nonempty_iso_flagGraph_lineGraph_of_degree
    {V : Type*} [Fintype V] (Y : SimpleGraph V) [DecidableRel Y.Adj]
    {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ a, Y.degree a ≤ d) (hdr : d < r) :
    ¬ Nonempty (D.flagGraph ≃g Y.lineGraph) := by
  classical
  rintro ⟨e⟩
  obtain ⟨S, hS, hcard⟩ := D.exists_clique_flagGraph_card_replication
  have hT : Y.lineGraph.IsClique (S.map e.toEquiv.toEmbedding) := by
    intro a ha f hf haf
    obtain ⟨a, haS, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨f, hfS, rfl⟩ := Finset.mem_map.mp hf
    exact e.map_rel_iff.mpr (hS haS hfS (fun he ↦ haf (congrArg e he)))
  have hle := Y.card_clique_lineGraph_le hd hdeg _ hT
  rw [Finset.card_map, hcard] at hle
  omega

end Design
