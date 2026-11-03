/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Graphs named in Sections 2 and 3

The friendship graph (`cgss/notation.md` §5, not in Mathlib), and the edges of `K_{m,n}` and
`K_n` as pairs, which identify the lattice graph `L₂(m) = L(K_{m,m})` and the triangular graph
`T(m) = L(K_m)` of the notation table with graphs on pairs.

## Main definitions

* `SimpleGraph.friendship m`: `m` triangles sharing one vertex, on `2m+1` vertices.
* `SimpleGraph.completeBipartiteEdgeEquiv`: `V × W ≃ (completeBipartiteGraph V W).edgeSet`.
* `SimpleGraph.completeGraphEdgeEquiv`: the pairs `i < j` and the edges of `K_V`.
-/

namespace SimpleGraph

/-- The friendship graph: `n` triangles meeting in one vertex, represented by `none`. -/
def friendship (n : ℕ) : SimpleGraph (Option (Fin n × Bool)) where
  Adj
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some (i, s), some (j, t) => i = j ∧ s ≠ t
  symm.symm := by
    rintro (_ | ⟨i, s⟩) (_ | ⟨j, t⟩) <;> simp_all [eq_comm]
  loopless.irrefl := by rintro (_ | ⟨i, s⟩) <;> simp

instance (n : ℕ) : DecidableRel (friendship n).Adj := fun x y => by
  cases x <;> cases y <;> simp only [friendship] <;> infer_instance

variable {V W : Type*}

/-- The edges of `K_{V,W}` are the pairs `s(inl i, inr j)`. -/
noncomputable def completeBipartiteEdgeEquiv (V W : Type*) :
    V × W ≃ (completeBipartiteGraph V W).edgeSet :=
  Equiv.ofBijective (fun p => ⟨s(Sum.inl p.1, Sum.inr p.2), by simp⟩) ⟨by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    simpa using congrArg Subtype.val h, by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y =>
      rcases x with i | j <;> rcases y with k | l <;> simp at he
      · exact ⟨(i, l), rfl⟩
      · exact ⟨(k, j), Subtype.ext Sym2.eq_swap⟩⟩

@[simp] theorem coe_completeBipartiteEdgeEquiv (p : V × W) :
    (completeBipartiteEdgeEquiv V W p : Sym2 (V ⊕ W)) = s(Sum.inl p.1, Sum.inr p.2) := rfl

/-- Two edges of `K_{V,W}` meet when they share an end in `V` or in `W`. -/
theorem lineGraph_completeBipartiteGraph_adj (p q : V × W) :
    (completeBipartiteGraph V W).lineGraph.Adj (completeBipartiteEdgeEquiv V W p)
      (completeBipartiteEdgeEquiv V W q) ↔ p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2) := by
  rw [lineGraph_adj_iff_exists, Ne, (completeBipartiteEdgeEquiv V W).injective.eq_iff]
  simp only [coe_completeBipartiteEdgeEquiv, Sym2.mem_iff]
  constructor
  · rintro ⟨hne, x, hx, hy⟩
    refine ⟨hne, ?_⟩
    rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp_all
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, Sum.inl p.1, by simp [h]⟩
    · exact ⟨hne, Sum.inr p.2, by simp [h]⟩

/-- The edges of `K_V` on a linear order are the pairs `s(i, j)` with `i < j`. -/
noncomputable def completeGraphEdgeEquiv (V : Type*) [LinearOrder V] :
    {p : V × V // p.1 < p.2} ≃ (completeGraph V).edgeSet :=
  Equiv.ofBijective (fun p => ⟨s(p.1.1, p.1.2), by simpa using p.2.ne⟩) ⟨by
    rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
    have h' : s(i, j) = s(k, l) := congrArg Subtype.val h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (hij.trans hkl) (lt_irrefl _), by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := by simpa using he
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨⟨(x, y), h⟩, rfl⟩
      · exact ⟨⟨(y, x), h⟩, Subtype.ext Sym2.eq_swap⟩⟩

@[simp] theorem coe_completeGraphEdgeEquiv [LinearOrder V] (p : {p : V × V // p.1 < p.2}) :
    (completeGraphEdgeEquiv V p : Sym2 V) = s(p.1.1, p.1.2) := rfl

/-- Two edges of `K_V` meet when they share an end. -/
theorem lineGraph_completeGraph_adj [LinearOrder V] (p q : {p : V × V // p.1 < p.2}) :
    (completeGraph V).lineGraph.Adj (completeGraphEdgeEquiv V p) (completeGraphEdgeEquiv V q) ↔
      p ≠ q ∧ (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2) := by
  rw [lineGraph_adj_iff_exists, Ne, (completeGraphEdgeEquiv V).injective.eq_iff]
  simp only [coe_completeGraphEdgeEquiv, Sym2.mem_iff]
  constructor
  · rintro ⟨hne, x, hx, hy⟩
    refine ⟨hne, ?_⟩
    rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp_all
  · rintro ⟨hne, h | h | h | h⟩
    · exact ⟨hne, p.1.1, by simp [h]⟩
    · exact ⟨hne, p.1.1, by simp [h]⟩
    · exact ⟨hne, p.1.2, by simp [h]⟩
    · exact ⟨hne, p.1.2, by simp [h]⟩

/-- In the complement of `T(V) = L(K_V)`, two edges are adjacent when they are disjoint. -/
theorem compl_lineGraph_completeGraph_adj [LinearOrder V] (p q : {p : V × V // p.1 < p.2}) :
    (completeGraph V).lineGraphᶜ.Adj (completeGraphEdgeEquiv V p) (completeGraphEdgeEquiv V q) ↔
      p ≠ q ∧ ¬(p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2) := by
  rw [compl_adj, lineGraph_completeGraph_adj, Ne, (completeGraphEdgeEquiv V).injective.eq_iff]
  tauto

end SimpleGraph
