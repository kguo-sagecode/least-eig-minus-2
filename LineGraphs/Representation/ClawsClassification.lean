/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.ClawsCriteria

/-!
# Connected claw-free generalized line graphs

Assertions 3 and 4 of Remark 4.12 of [CGSS], `rem:4.12` in the blueprint.
The non-line-graph case is a complete graph with disjoint edges deleted.
-/

namespace SimpleGraph

/-- Step `s412clique`, Remark 4.12 of [CGSS]: a complete graph with
the `t` pairs indexed by `Fin t` removed. -/
private def cliqueCocktailGraph (s t : ℕ) : SimpleGraph (Fin s ⊕ (Fin t × Bool)) where
  Adj
    | .inl i, .inl j => i ≠ j
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr p, .inr q => p.1 ≠ q.1
  symm.symm := by
    rintro (i | p) (j | q) <;> simp_all [eq_comm]
  loopless.irrefl := by rintro (i | p) <;> simp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Y : SimpleGraph V) [DecidableRel Y.Adj] (a : V → ℕ)

/-- Steps `s412only` and `s412clique`, Remark 4.12 of [CGSS]: enumerate
the incident edges and petals when one endpoint accounts for all vertices. -/
private noncomputable def allAtIso (i : V)
    (hall : ∀ v, v ∈ generalizedLineGraphAt Y a i) :
    cliqueCocktailGraph (Y.degree i) (a i) ≃g generalizedLineGraph Y a := by
  classical
  let e : {f : Y.edgeSet // i ∈ f.val} ≃ Fin (Y.degree i) :=
    Fintype.equivFinOfCardEq (Y.card_incident_edge_subtype i)
  let f : Fin (Y.degree i) ⊕ (Fin (a i) × Bool) → GeneralizedLineGraphVertex Y a :=
    Sum.elim (fun k ↦ .inl (e.symm k).val) (fun p ↦ .inr ⟨i, p⟩)
  have hf : Function.Injective f := by
    rintro (k | p) (l | q) h
    · exact congrArg Sum.inl (e.symm.injective (Subtype.ext (Sum.inl.inj h)))
    · cases h
    · cases h
    · exact congrArg Sum.inr (by simpa [f] using h)
  have hs : Function.Surjective f := by
    rintro (g | ⟨j, k, b⟩)
    · exact ⟨.inl (e ⟨g, hall (.inl g)⟩), by simp [f]⟩
    · have hji : j = i := hall (.inr ⟨j, k, b⟩)
      subst j
      exact ⟨.inr (k, b), rfl⟩
  refine { toEquiv := Equiv.ofBijective f ⟨hf, hs⟩, map_rel_iff' := ?_ }
  rintro (k | p) (l | q)
  · change Y.lineGraph.Adj (e.symm k).val (e.symm l).val ↔ k ≠ l
    rw [lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨hne, _⟩ h
      exact hne (h ▸ rfl)
    · intro h
      exact ⟨fun he ↦ h (e.symm.injective (Subtype.ext he)), i,
        (e.symm k).property, (e.symm l).property⟩
  · change i ∈ (e.symm k).val.val ↔ True
    exact iff_true_intro (e.symm k).property
  · change i ∈ (e.symm l).val.val ↔ True
    exact iff_true_intro (e.symm l).property
  · change (i = i ∧ p.1.val ≠ q.1.val) ↔ p.1 ≠ q.1
    simp only [true_and, ne_eq, Fin.val_inj]

/-- Step `s412only`, Remark 4.12 of [CGSS]: a star on `s + 1` vertices
has centre degree `s`. -/
private theorem star_degree_center (s : ℕ) :
    (starGraph (0 : Fin (s + 1))).degree 0 = s := by
  simpa using (degree_starGraph_center (r := (0 : Fin (s + 1))))

/-- Step `s412ifK`, Remark 4.12 of [CGSS]: every vertex of the star
construction is attached at the centre. -/
private theorem star_all_at (s t : ℕ) :
    ∀ v, v ∈ generalizedLineGraphAt (starGraph (0 : Fin (s + 1)))
      (fun i ↦ if i = 0 then t else 0) 0 := by
  rintro (⟨⟨i, j⟩, hij⟩ | ⟨i, k, b⟩)
  · change 0 ∈ s(i, j)
    rcases (starGraph_adj.mp hij).2 with rfl | rfl <;> simp
  · change i = 0
    by_contra hi
    have hk := k.isLt
    simp [hi] at hk

-- Remark 4.12
/-- Step `s412clique` of Remark 4.12 of [CGSS]: the star construction is
isomorphic to the graph on `s` clique vertices and `t` nonadjacent pairs,
with every other pair adjacent. -/
theorem generalizedLineGraph_star_adj_description (s t : ℕ) :
    ∃ e : (Fin s ⊕ (Fin t × Bool)) ≃
        GeneralizedLineGraphVertex (starGraph (0 : Fin (s + 1)))
          (fun i ↦ if i = 0 then t else 0),
      ∀ u v, (generalizedLineGraph (starGraph (0 : Fin (s + 1)))
        (fun i ↦ if i = 0 then t else 0)).Adj (e u) (e v) ↔
        match u, v with
        | .inl i, .inl j => i ≠ j
        | .inl _, .inr _ => True
        | .inr _, .inl _ => True
        | .inr p, .inr q => p.1 ≠ q.1 := by
  have he : Nonempty (cliqueCocktailGraph s t ≃g
      generalizedLineGraph (starGraph (0 : Fin (s + 1)))
        (fun i ↦ if i = 0 then t else 0)) := by
    have f := allAtIso _ _ 0 (star_all_at s t)
    change cliqueCocktailGraph ((starGraph (0 : Fin (s + 1))).degree 0) t ≃g
      generalizedLineGraph (starGraph (0 : Fin (s + 1)))
        (fun i ↦ if i = 0 then t else 0) at f
    rw [star_degree_center] at f
    exact ⟨f⟩
  obtain ⟨e⟩ := he
  exact ⟨e.toEquiv, fun u v ↦ e.map_rel_iff⟩

omit [DecidableEq V] in
/-- Step `s412only`, Remark 4.12 of [CGSS]: enumerating the incident
edges identifies the graph with the star construction. -/
private theorem nonempty_iso_star_of_all_at (i : V)
    (hall : ∀ v, v ∈ generalizedLineGraphAt Y a i) :
    Nonempty (generalizedLineGraph Y a ≃g
      generalizedLineGraph (starGraph (0 : Fin (Y.degree i + 1)))
        (fun j ↦ if j = 0 then a i else 0)) := by
  classical
  have he : Nonempty (cliqueCocktailGraph (Y.degree i) (a i) ≃g
      generalizedLineGraph (starGraph (0 : Fin (Y.degree i + 1)))
        (fun j ↦ if j = 0 then a i else 0)) := by
    have f := allAtIso _ _ 0 (star_all_at (Y.degree i) (a i))
    change cliqueCocktailGraph ((starGraph (0 : Fin (Y.degree i + 1))).degree 0)
      (a i) ≃g generalizedLineGraph (starGraph (0 : Fin (Y.degree i + 1)))
        (fun j ↦ if j = 0 then a i else 0) at f
    rw [star_degree_center] at f
    exact ⟨f⟩
  exact ⟨(allAtIso Y a i hall).symm.trans he.some⟩

omit [Fintype V] [DecidableEq V] [DecidableRel Y.Adj] in
/-- Steps `s412leaf`, `s412closed` and `s412all`, Remark 4.12 of [CGSS]:
connectedness makes a positive endpoint's closed component exhaustive. -/
private theorem all_at_of_connected_clawFree [Finite V]
    (hc : (generalizedLineGraph Y a).Connected)
    (hcf : (generalizedLineGraph Y a).ClawFree) (i : V) (hi : 0 < a i) :
    ∀ v, v ∈ generalizedLineGraphAt Y a i := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hleaf := (generalizedLineGraph_clawFree_iff Y a).mp hcf
  have hedge {j : V} (hij : Y.Adj i j) {v : GeneralizedLineGraphVertex Y a}
      (hv : (generalizedLineGraph Y a).Adj (.inl ⟨s(i, j), hij⟩) v) :
      v ∈ generalizedLineGraphAt Y a i := by
    obtain ⟨haj, hdj⟩ := hleaf i j hi hij
    have huniq : ∀ f g : {e : Y.edgeSet // j ∈ e.val}, f = g :=
      Fintype.card_le_one_iff.mp (by rw [Y.card_incident_edge_subtype, hdj])
    rcases v with f | ⟨l, k, b⟩
    · obtain ⟨hne, l, hl, hlf⟩ := lineGraph_adj_iff_exists.mp hv
      rcases Sym2.mem_iff.mp hl with hli | hlj
      · exact hli ▸ hlf
      · exact (hne (congrArg Subtype.val (huniq ⟨⟨s(i, j), hij⟩, by simp⟩
          ⟨f, hlj ▸ hlf⟩))).elim
    · rcases Sym2.mem_iff.mp hv with hli | hlj
      · exact hli
      · have hk := k.isLt
        change l = j at hlj
        have hz : a l = 0 := (congrArg a hlj).trans haj
        omega
  refine hc.forall_of_adj_closed (P := fun v ↦ v ∈ generalizedLineGraphAt Y a i)
    (u := .inr ⟨i, ⟨0, hi⟩, false⟩) (by rfl) ?_
  rintro (⟨⟨j, l⟩, hjl⟩ | ⟨j, k, b⟩) v hat hv
  · rcases Sym2.mem_iff.mp hat with rfl | rfl
    · exact hedge hjl hv
    · have he : (⟨s(j, i), hjl⟩ : Y.edgeSet) = ⟨s(i, j), hjl.symm⟩ :=
        Subtype.ext Sym2.eq_swap
      exact hedge hjl.symm (he ▸ hv)
  · change j = i at hat
    subst j
    rcases v with f | p
    · exact hv
    · exact hv.1.symm

-- Remark 4.12
/-- Step `s412ifK` of Remark 4.12 of [CGSS]: attaching petals only at the
centre of a star gives a claw-free graph. -/
theorem generalizedLineGraph_star_clawFree (s t : ℕ) :
    (generalizedLineGraph (starGraph (0 : Fin (s + 1)))
      (fun i ↦ if i = 0 then t else 0)).ClawFree := by
  apply (generalizedLineGraph_clawFree_iff _ _).mpr
  intro i j hi hij
  have hi0 : i = 0 := by
    by_contra hi0
    simp [hi0] at hi
  subst i
  have hj : j ≠ 0 := hij.ne.symm
  exact ⟨by simp [hj], degree_starGraph_of_ne_center hj⟩

variable {X : SimpleGraph V} [DecidableRel X.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel X.Adj] in
-- Remark 4.12
/-- Remark 4.12 of [CGSS], blueprint assertion 3, step `s412three`: a connected
generalized line graph is claw-free exactly when it is a line graph or the
generalized line graph of a star with petals only at its centre. -/
theorem IsGeneralizedLineGraph.clawFree_iff (hX : X.IsGeneralizedLineGraph)
    (hc : X.Connected) :
    X.ClawFree ↔
      (∃ (m : ℕ) (Z : SimpleGraph (Fin m)), Nonempty (X ≃g Z.lineGraph)) ∨
      ∃ s t, Nonempty (X ≃g generalizedLineGraph (starGraph (0 : Fin (s + 1)))
        (fun i ↦ if i = 0 then t else 0)) := by
  classical
  constructor
  · intro hcf
    obtain ⟨m, Z, b, ⟨e⟩⟩ := hX
    by_cases hz : ∀ i, b i = 0
    · have hb : b = fun _ ↦ 0 := funext hz
      subst b
      exact Or.inl ⟨m, Z, ⟨e.trans (generalizedLineGraphZeroIso Z)⟩⟩
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      have hall := all_at_of_connected_clawFree Z b (e.connected_iff.mp hc)
        (e.clawFree_iff.mp hcf) i (Nat.pos_of_ne_zero hi)
      obtain ⟨f⟩ := nonempty_iso_star_of_all_at Z b i hall
      exact Or.inr ⟨Z.degree i, b i, ⟨e.trans f⟩⟩
  · rintro (⟨m, Z, ⟨e⟩⟩ | ⟨s, t, ⟨e⟩⟩)
    · exact e.clawFree_iff.mpr (lineGraph_clawFree Z)
    · exact e.clawFree_iff.mpr (generalizedLineGraph_star_clawFree s t)

-- Remark 4.12
/-- Remark 4.12 of [CGSS], blueprint assertion 4, step `s412four`: sufficiently large
connected claw-free graphs with least eigenvalue at least minus two are line
graphs or the stated star constructions. -/
theorem hoffman_of_clawFree (hc : X.Connected) (hcf : X.ClawFree)
    (hp : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef)
    (hlarge : 36 < Fintype.card V ∨ ∃ u, 28 < X.degree u) :
    (∃ (m : ℕ) (Z : SimpleGraph (Fin m)), Nonempty (X ≃g Z.lineGraph)) ∨
      ∃ s t, Nonempty (X ≃g generalizedLineGraph (starGraph (0 : Fin (s + 1)))
        (fun i ↦ if i = 0 then t else 0)) :=
  ((hoffman_of_large hc hp hlarge).clawFree_iff hc).mp hcf

end SimpleGraph
