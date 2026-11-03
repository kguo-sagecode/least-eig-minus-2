/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C5Inclusions
import LineGraphs.Computations.C5Dn
import LineGraphs.Computations.C4Graphs
import LineGraphs.Computations.C4An

/-!
# Computation C5: inclusions and non-inclusions of equal rank

Computation C5 of `blueprint/sec3-rootsystems.tex`, for Theorem 3.6 of [CGSS]: the proper
isometric inclusions `A₈ ⊂ E₈`, `D₈ ⊂ E₈`, `A₇ ⊂ E₇` of equal rank
(`Computations/C5Inclusions.lean`), and the absence of isometric inclusions `Aℓ ⊂ Dℓ`
(`ℓ ≥ 4`), `A₆ ⊂ E₆`, `D₆ ⊂ E₆` and `D₇ ⊂ E₇`.

The obstructions go through the marked graphs (Lemma "marked inclusions",
`LineSystem.IsometricInclusion.orthGraphEmbedding`): an isometric inclusion embeds the
orthogonality graph of a marked star of the source, as an induced subgraph, in that of the image
star of the target, and C4 identifies the target graph for every ordered star.
* `Aℓ ⊂ Dℓ`: the void graph on `ℓ - 2` vertices would embed in the friendship graph with `ℓ - 3`
  triangles, whose cocliques have at most `ℓ - 3` vertices. This fills the first omission of
  errata Gap 13 (the paper does not exclude `Aℓ ⊂ Dℓ`).
* `A₆ ⊂ E₆`: a 4-coclique would embed in the `3 × 3` lattice graph; two of four cells share a row.
* `D₆ ⊂ E₆`, `D₇ ⊂ E₇`: the centre of the friendship graph has 6 (8) neighbours, the graphs of
  `E₆` (`E₇`) are regular of degree 4 (6).
-/

open scoped RealInnerProductSpace
open Module Submodule

namespace SimpleGraph

/-- A vertex adjacent to the images of an injective family has at least that many neighbours. -/
theorem card_le_degree_of_forall_adj {V α : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] [Fintype α] (v : V) (φ : α → V) (hφ : Function.Injective φ)
    (h : ∀ a, G.Adj v (φ a)) : Fintype.card α ≤ G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn φ (fun a _ => (mem_neighborFinset G v _).mpr (h a))
    hφ.injOn

/-- The cocliques of the friendship graph with `t ≥ 1` triangles have at most `t` vertices. -/
theorem friendship_card_le_of_embedding_bot {m t : ℕ} (ht : 1 ≤ t)
    (f : (⊥ : SimpleGraph (Fin m)) ↪g friendship t) : m ≤ t := by
  by_contra hlt
  rw [not_le] at hlt
  have hnadj : ∀ i j, ¬ (friendship t).Adj (f i) (f j) := fun i j h => (f.map_rel_iff.mp h)
  have hsome : ∀ i, ∃ p, f i = some p := by
    intro i
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by simp only [Fintype.card_fin]; omega) i
    cases hfi : f i with
    | some p => exact ⟨p, rfl⟩
    | none =>
      exfalso
      cases hfj : f j with
      | none => exact hj (f.injective (hfj.trans hfi.symm))
      | some q =>
        apply hnadj i j
        rw [hfi, hfj]
        trivial
  choose p hp using hsome
  have hinj : Function.Injective fun i => (p i).1 := by
    intro i j hij
    by_contra hne
    apply hnadj i j
    rw [hp i, hp j]
    refine ⟨hij, fun hs => hne (f.injective ?_)⟩
    rw [hp i, hp j, Prod.ext hij hs]
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at this
  omega

/-- The `3 × 3` lattice graph `L₂(3) = L(K_{3,3})` has no coclique of more than 3 vertices:
two of four cells share a row. -/
theorem lineGraph_completeBipartite_three_card_le_of_embedding_bot {m : ℕ}
    (f : (⊥ : SimpleGraph (Fin m)) ↪g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph) :
    m ≤ 3 := by
  by_contra hlt
  rw [not_le] at hlt
  let e := completeBipartiteEdgeEquiv (Fin 3) (Fin 3)
  obtain ⟨i, j, hij, hrow⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (e.symm (f i)).1) (by simp only [Fintype.card_fin]; omega)
  have hadj := (lineGraph_completeBipartiteGraph_adj (e.symm (f i)) (e.symm (f j))).mpr
    ⟨fun h => hij (f.injective (e.symm.injective h)), Or.inl hrow⟩
  simp only [e, Equiv.apply_symm_apply] at hadj
  exact f.map_rel_iff.mp hadj

end SimpleGraph

namespace LineSystem

-- Computation C5, step s3c5AD
/-- C5, step `s3c5AD` (errata Gap 13): there is no isometric inclusion `Aℓ ⊂ Dℓ` for `ℓ ≥ 4`. -/
theorem not_embeds_An_Dn {ℓ : ℕ} (hℓ : 4 ≤ ℓ) : IsEmpty (IsometricInclusion (An ℓ) (Dn ℓ)) := by
  constructor
  intro G
  let H := An.hyp24 (n := ℓ) (by omega)
  let H' := IsometricInclusion.targetHyp24 H G (isIndecomposable_Dn hℓ) (isStarClosed_Dn ℓ)
  obtain ⟨e₂⟩ := Hyp24.nonempty_orthGraph_iso_of_S_eq_Dn hℓ H' rfl
  have f := ((An.orthGraphIso (n := ℓ) (by omega)).toEmbedding.trans
    (IsometricInclusion.orthGraphEmbedding H H' G rfl rfl)).trans e₂.symm.toEmbedding
  have := SimpleGraph.friendship_card_le_of_embedding_bot (by omega) f
  omega

-- Computation C5, step s3c5Asix
/-- C5, step `s3c5Asix`: there is no isometric inclusion `A₆ ⊂ E₆`. -/
theorem not_embeds_An_E₆ : IsEmpty (IsometricInclusion (An 6) E₆) := by
  constructor
  intro G
  let H := An.hyp24 (n := 6) (by norm_num)
  let H' := IsometricInclusion.targetHyp24 H G isIndecomposable_E₆ isStarClosed_E₆
  obtain ⟨e₂⟩ := Hyp24.nonempty_latticeGraph_iso_of_S_eq_E₆ H' rfl
  have f := ((An.orthGraphIso (n := 6) (by norm_num)).toEmbedding.trans
    (IsometricInclusion.orthGraphEmbedding H H' G rfl rfl)).trans e₂.symm.toEmbedding
  have := SimpleGraph.lineGraph_completeBipartite_three_card_le_of_embedding_bot f
  omega

-- Computation C5, step s3c5Dsix
/-- C5, step `s3c5Dsix`: there is no isometric inclusion `D₆ ⊂ E₆`. -/
theorem not_embeds_Dn_E₆ : IsEmpty (IsometricInclusion (Dn 6) E₆) := by
  constructor
  intro G
  let H := Dn.hyp24 (n := 6) (by norm_num)
  let H' := IsometricInclusion.targetHyp24 H G isIndecomposable_E₆ isStarClosed_E₆
  let f := (Dn.orthGraphIso (n := 6) (by norm_num)).toEmbedding.trans
    (IsometricInclusion.orthGraphEmbedding H H' G rfl rfl)
  have hdeg := (H'.orthGraph_isSRGWith_of_S_eq_E₆ rfl).regular.degree_eq (f none)
  have h := H'.orthGraph.card_le_degree_of_forall_adj (f none) (fun x => f (some x))
    (f.injective.comp (Option.some_injective _)) (fun x => f.map_rel_iff.mpr trivial)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hdeg] at h
  omega

-- Computation C5, step s3c5Dseven
/-- C5, step `s3c5Dseven`: there is no isometric inclusion `D₇ ⊂ E₇`. -/
theorem not_embeds_Dn_E₇ : IsEmpty (IsometricInclusion (Dn 7) E₇) := by
  constructor
  intro G
  let H := Dn.hyp24 (n := 7) (by norm_num)
  let H' := IsometricInclusion.targetHyp24 H G isIndecomposable_E₇ isStarClosed_E₇
  let f := (Dn.orthGraphIso (n := 7) (by norm_num)).toEmbedding.trans
    (IsometricInclusion.orthGraphEmbedding H H' G rfl rfl)
  have hdeg := (H'.orthGraph_isSRGWith_of_S_eq_E₇ rfl).regular.degree_eq (f none)
  have h := H'.orthGraph.card_le_degree_of_forall_adj (f none) (fun x => f (some x))
    (f.injective.comp (Option.some_injective _)) (fun x => f.map_rel_iff.mpr trivial)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hdeg] at h
  omega

end LineSystem

namespace Computations.C5

open LineSystem

-- Computation C5
/-- Computation C5 of the blueprint: the proper isometric inclusions `A₈ ⊂ E₈`, `D₈ ⊂ E₈` and
`A₇ ⊂ E₇`, all of equal rank, and no isometric inclusions `Aℓ ⊂ Dℓ` (`ℓ ≥ 4`), `A₆ ⊂ E₆`,
`D₆ ⊂ E₆` or `D₇ ⊂ E₇`. -/
theorem inclusions_and_obstructions :
    ((∃ G : IsometricInclusion (An 8) E₈, G.IsProper) ∧
      finrank ℝ (span ℝ (An 8).Φ) = finrank ℝ (span ℝ E₈.Φ)) ∧
    ((∃ G : IsometricInclusion (Dn 8) E₈, G.IsProper) ∧
      finrank ℝ (span ℝ (Dn 8).Φ) = finrank ℝ (span ℝ E₈.Φ)) ∧
    ((∃ G : IsometricInclusion (An 7) E₇, G.IsProper) ∧
      finrank ℝ (span ℝ (An 7).Φ) = finrank ℝ (span ℝ E₇.Φ)) ∧
    (∀ ℓ, 4 ≤ ℓ → IsEmpty (IsometricInclusion (An ℓ) (Dn ℓ))) ∧
    IsEmpty (IsometricInclusion (An 6) E₆) ∧
    IsEmpty (IsometricInclusion (Dn 6) E₆) ∧
    IsEmpty (IsometricInclusion (Dn 7) E₇) :=
  ⟨⟨⟨_, An.inclusionE₈_isProper⟩, by rw [finrank_span_An, finrank_span_E₈]⟩,
    ⟨⟨_, Dn.inclusionE₈_isProper⟩, by rw [finrank_span_Dn (by norm_num), finrank_span_E₈]⟩,
    ⟨⟨_, An.inclusionE₇_isProper⟩, by rw [finrank_span_An, finrank_span_E₇]⟩,
    fun _ h => not_embeds_An_Dn h, not_embeds_An_E₆, not_embeds_Dn_E₆, not_embeds_Dn_E₇⟩

end Computations.C5
