/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.LineGraph
import LineGraphs.LineSystem.Models
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Representations in type A

Theorem 4.1 of [CGSS], following steps `s41pq`--`s41backip` of the Section 4 blueprint.
The bound is expressed by taking the bipartite graph on `Fin (n + 1)`.
-/

open scoped RealInnerProductSpace
open EuclideanSpace

namespace EuclideanSpace

/-- Theorem 4.1 of [CGSS], step `s41ip`: expand the products of coordinate differences. -/
theorem inner_sub_single_sub_single {n : ℕ} (i j k l : Fin n) :
    ⟪single i (1 : ℝ) - single j 1, single k 1 - single l 1⟫ =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) -
        (if j = k then 1 else 0) + (if j = l then 1 else 0) := by
  simp only [inner_sub_left, inner_sub_right, inner_single_left, PiLp.single_apply,
    map_one, one_mul]
  ring

end EuclideanSpace

namespace LineSystem.An

/-- Theorem 4.1 of [CGSS], step `s41pq`: roots are differences of distinct coordinates. -/
theorem mem_iff_exists_sub_single {n : ℕ} {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈ (An n).Φ ↔ ∃ i j, i ≠ j ∧ x = single i 1 - single j 1 := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.1.1, p.1.2, p.2, ?_⟩
    ext k
    simp [integerVector, anRoot, pairVector, Pi.single_apply, PiLp.single_apply]
    split_ifs <;> norm_num
  · rintro ⟨i, j, hij, rfl⟩
    exact sub_single_mem_An i j hij

end LineSystem.An

namespace SimpleGraph

noncomputable local instance {U : Type*} (Y : SimpleGraph U) : DecidableRel Y.Adj :=
  Classical.decRel _

variable {V : Type*} [DecidableEq V] {X : SimpleGraph V} [DecidableRel X.Adj]

/-- Theorem 4.1 of [CGSS], steps `s41sign`--`s41iso`: the roots determine a bipartite graph. -/
theorem IsRepresentedIn.nonempty_iso_lineGraph_of_An {n : ℕ}
    (hX : X.IsRepresentedIn (LineSystem.An n)) :
    ∃ Y : SimpleGraph (Fin (n + 1)), Y.IsBipartite ∧ Nonempty (X ≃g Y.lineGraph) := by
  classical
  obtain ⟨x, hx, hm⟩ := hX
  have hroots (u : V) := LineSystem.An.mem_iff_exists_sub_single.mp (hm u)
  choose p q hpq hxform using hroots
  have hcross (u v : V) : p u ≠ q v := by
    intro he
    have hn := hx.inner_nonneg u v
    rw [hxform u, hxform v, inner_sub_single_sub_single] at hn
    have hpu : p u ≠ p v := by intro h; exact hpq v (h.symm.trans he)
    have hqv : q u ≠ q v := by intro h; exact hpq u (he.trans h.symm)
    simp only [ite_eq_right hpu, ite_eq_left he, ite_eq_right hqv] at hn
    split_ifs at hn <;> norm_num at hn
  have hip (u v : V) : ⟪x u, x v⟫ =
      (if p u = p v then 1 else 0) + (if q u = q v then 1 else 0) := by
    rw [hxform u, hxform v, inner_sub_single_sub_single]
    simp [hcross u v, (hcross v u).symm]
  let Y : SimpleGraph (Fin (n + 1)) :=
    { Adj i j := ∃ u, (i = p u ∧ j = q u) ∨ (i = q u ∧ j = p u)
      symm.symm := by rintro i j ⟨u, h | h⟩ <;> exact ⟨u, by tauto⟩
      loopless.irrefl := by
        rintro i ⟨u, ⟨hi, hj⟩ | ⟨hi, hj⟩⟩
        · exact hpq u (hi.symm.trans hj)
        · exact hpq u (hj.symm.trans hi) }
  have hb : Y.IsBipartiteWith (Set.range p) (Set.range q) := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
      exact hcross u v hv.symm
    · rintro i j ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨Set.mem_range_self u, Set.mem_range_self u⟩
      · exact Or.inr ⟨Set.mem_range_self u, Set.mem_range_self u⟩
  let f : V → Y.edgeSet := fun u ↦ ⟨s(p u, q u), ⟨u, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      have he : s(p u, q u) = s(p v, q v) := congrArg Subtype.val huv
      rcases Sym2.eq_iff.mp he with ⟨hp, hq⟩ | ⟨hp, _⟩
      · apply hx.injective
        rw [hxform u, hxform v, hp, hq]
      · exact False.elim (hcross u v hp)
    · rintro ⟨⟨i, j⟩, he⟩
      obtain ⟨u, h | h⟩ := he
      · refine ⟨u, Subtype.ext ?_⟩
        change s(p u, q u) = s(i, j)
        rw [← h.1, ← h.2]
      · refine ⟨u, Subtype.ext ?_⟩
        change s(p u, q u) = s(i, j)
        rw [← h.1, ← h.2]
        exact Sym2.eq_swap
  refine ⟨Y, hb.isBipartite, ⟨{ toEquiv := Equiv.ofBijective f hf, map_rel_iff' := ?_ }⟩⟩
  intro u v
  change Y.lineGraph.Adj (f u) (f v) ↔ X.Adj u v
  rw [lineGraph_adj_iff_exists, hx.adj_iff, hip]
  have heq : f u = f v ↔ u = v := hf.1.eq_iff
  have hend : (∃ i, i ∈ (f u : Sym2 (Fin (n + 1))) ∧
      i ∈ (f v : Sym2 (Fin (n + 1)))) ↔
      p u = p v ∨ q u = q v := by
    change (∃ i, i ∈ s(p u, q u) ∧ i ∈ s(p v, q v)) ↔ _
    simp only [Sym2.mem_iff]
    constructor
    · rintro ⟨i, hi | hi, hj | hj⟩
      · exact Or.inl (hi.symm.trans hj)
      · exact False.elim (hcross u v (hi.symm.trans hj))
      · exact False.elim (hcross v u (hj.symm.trans hi))
      · exact Or.inr (hi.symm.trans hj)
    · rintro (h | h)
      · exact ⟨p u, Or.inl rfl, Or.inl h⟩
      · exact ⟨q u, Or.inr rfl, Or.inr h⟩
  rw [ne_eq, heq, hend]
  have hpqeq : p u = p v → q u = q v → u = v := by
    intro hp hq
    apply hx.injective
    rw [hxform u, hxform v, hp, hq]
  by_cases he : u = v
  · subst v
    norm_num
  by_cases hp : p u = p v <;> by_cases hq : q u = q v <;> simp_all

/-- Theorem 4.1 of [CGSS], step `s41backip`: orient a bipartite graph from one part
to the other and use coordinate differences for its edges. -/
theorem IsBipartite.lineGraph_isRepresentedIn_An {n : ℕ}
    {Y : SimpleGraph (Fin (n + 1))} (hY : Y.IsBipartite) :
    Y.lineGraph.IsRepresentedIn (LineSystem.An n) := by
  classical
  obtain ⟨P, Q, hPQ⟩ := hY.exists_isBipartiteWith
  have horient (e : Y.edgeSet) : ∃ i j, i ∈ P ∧ j ∈ Q ∧ s(i, j) = e.val := by
    rcases e with ⟨⟨i, j⟩, hij⟩
    rcases hPQ.mem_of_adj hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact ⟨i, j, hi, hj, rfl⟩
    · exact ⟨j, i, hj, hi, Sym2.eq_swap⟩
  choose p q hp hq he using horient
  have hcross (e f : Y.edgeSet) : p e ≠ q f := by
    intro h
    exact Set.disjoint_left.mp hPQ.disjoint (h ▸ hp e) (hq f)
  have hvec (e : Y.edgeSet) : Y.lineGraphVector e = single (p e) 1 + single (q e) 1 := by
    have hadj : Y.Adj (p e) (q e) := by
      apply Y.mem_edgeSet.mp
      rw [he e]
      exact e.property
    have he' : (⟨s(p e, q e), hadj⟩ : Y.edgeSet) = e := Subtype.ext (he e)
    simpa only [he'] using Y.lineGraphVector_mk hadj
  let x : Y.edgeSet → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun e ↦ single (p e) 1 - single (q e) 1
  have hip (e f : Y.edgeSet) : ⟪x e, x f⟫ =
      ⟪Y.lineGraphVector e, Y.lineGraphVector f⟫ := by
    dsimp only [x]
    rw [inner_sub_single_sub_single, hvec e, hvec f]
    simp [inner_add_left, inner_add_right, inner_single_left, PiLp.single_apply,
      hcross e f, (hcross f e).symm]
  refine ⟨x, ?_, fun e ↦ LineSystem.sub_single_mem_An (p e) (q e) (hcross e e)⟩
  apply isRepresentation_iff.mpr
  intro e f
  rw [hip]
  exact isRepresentation_iff.mp Y.lineGraph_isRepresentation e f

-- Theorem 4.1
/-- Theorem 4.1 of [CGSS]: representations in `Aₙ` are exactly line graphs of bipartite
graphs on `Fin (n + 1)`. The fixed vertex set includes any unused coordinates as isolates. -/
theorem isRepresentedIn_An_iff (n : ℕ) (_hn : 1 ≤ n) :
    X.IsRepresentedIn (LineSystem.An n) ↔
      ∃ Y : SimpleGraph (Fin (n + 1)), Y.IsBipartite ∧ Nonempty (X ≃g Y.lineGraph) := by
  constructor
  · exact IsRepresentedIn.nonempty_iso_lineGraph_of_An
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact hY.lineGraph_isRepresentedIn_An.comp_iso e

end SimpleGraph
