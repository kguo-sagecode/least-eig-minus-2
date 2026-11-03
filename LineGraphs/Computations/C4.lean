/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C3
import LineGraphs.Computations.C4An
import LineGraphs.Computations.C4Dn
import LineGraphs.Computations.C4E6
import LineGraphs.Computations.C4E7
import LineGraphs.Computations.C4E8
import LineGraphs.Computations.ModelIsoProperties
import LineGraphs.Computations.C4E8Stars
import LineGraphs.Computations.C4Graphs

/-!
# Computation C4

The classical results are parametric. The exceptional results use finite certificates;
the two alternative E₈ presentations inherit the properties through the C3 isomorphisms.
The exceptional rows hold for every ordered star, by the reflection trees of
`C4E6Stars.lean`, `C4E7Stars.lean` and `C4E8Stars.lean`.

## Main statements

* `Computations.C4.model_data`: every model is nonempty, star-closed and indecomposable, with
  its rank; `A₁` has one line.
* `Computations.C4.marked_star_data`: the table of the blueprint for the marked star
  `(e₁ - e₂, e₂ - e₃)`, at `Fin` indices 0, 1, 2 (`An.hyp24`, `Dn.hyp24`, `E₆.hyp24Simple`,
  `E₇.hyp24Simple`, `E₈.hyp24Simple`).
* `Computations.C4.exceptional_star_data`: the exceptional rows for every ordered star, with
  `L₂(3)` for E₆ and the complement of `T(6)` for E₇.
-/

namespace LineSystem

/-- C4: the nine-coordinate E₈ model is indecomposable. -/
theorem isIndecomposable_E₈viaA₈ : E₈viaA₈.IsIndecomposable :=
  E₈viaA₈.isoE₈.isIndecomposable isIndecomposable_E₈

/-- C4: the Steiner E₈ model is indecomposable. -/
theorem isIndecomposable_E₈viaSteiner : E₈viaSteiner.IsIndecomposable :=
  E₈viaSteiner.isoE₈.isIndecomposable isIndecomposable_E₈

/-- C4: the nine-coordinate E₈ model is star-closed. -/
theorem isStarClosed_E₈viaA₈ : E₈viaA₈.IsStarClosed :=
  E₈viaA₈.isoE₈.isStarClosed isStarClosed_E₈

/-- C4: the Steiner E₈ model is star-closed. -/
theorem isStarClosed_E₈viaSteiner : E₈viaSteiner.IsStarClosed :=
  E₈viaSteiner.isoE₈.isStarClosed isStarClosed_E₈

/-- C4: model (A) is nonempty from rank 1. -/
theorem An.Φ_nonempty {n : ℕ} (hn : 1 ≤ n) : (An n).Φ.Nonempty :=
  ⟨_, sub_single_mem_An ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])⟩

/-- C4: model (D) is nonempty from rank 2. -/
theorem Dn.Φ_nonempty {n : ℕ} (hn : 2 ≤ n) : (Dn n).Φ.Nonempty :=
  ⟨_, add_single_mem_Dn ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])⟩

/-- C4: E₈ is nonempty. -/
theorem E₈.Φ_nonempty : E₈.Φ.Nonempty := ⟨_, E₈.hyp24.a_mem⟩

/-- C4: E₇ is nonempty. -/
theorem E₇.Φ_nonempty : E₇.Φ.Nonempty := ⟨_, E₇.hyp24.a_mem⟩

/-- C4: E₆ is nonempty. -/
theorem E₆.Φ_nonempty : E₆.Φ.Nonempty := ⟨_, E₆.hyp24.a_mem⟩

/-- C4: the nine-coordinate E₈ model is nonempty. -/
theorem E₈viaA₈.Φ_nonempty : E₈viaA₈.Φ.Nonempty :=
  ⟨_, (E₈viaA₈.isoE₈.toEquiv.symm ⟨_, E₈.hyp24.a_mem⟩).2⟩

/-- C4: the Steiner E₈ model is nonempty. -/
theorem E₈viaSteiner.Φ_nonempty : E₈viaSteiner.Φ.Nonempty :=
  ⟨_, (E₈viaSteiner.isoE₈.toEquiv.symm ⟨_, E₈.hyp24.a_mem⟩).2⟩

end LineSystem

namespace Computations.C4

open LineSystem Module Submodule SimpleGraph

-- Computation C4
/-- C4, the model data: every model is nonempty, star-closed and indecomposable in its range,
with the stated rank, and `A₁` has one line. -/
theorem model_data :
    ((An 1).numLines = 1 ∧ finrank ℝ (span ℝ (An 1).Φ) = 1) ∧
    (∀ n, 1 ≤ n → (An n).Φ.Nonempty ∧ (An n).IsStarClosed ∧ (An n).IsIndecomposable ∧
      finrank ℝ (span ℝ (An n).Φ) = n) ∧
    (∀ n, 4 ≤ n → (Dn n).Φ.Nonempty ∧ (Dn n).IsStarClosed ∧ (Dn n).IsIndecomposable ∧
      finrank ℝ (span ℝ (Dn n).Φ) = n) ∧
    (E₆.Φ.Nonempty ∧ E₆.IsStarClosed ∧ E₆.IsIndecomposable ∧ finrank ℝ (span ℝ E₆.Φ) = 6) ∧
    (E₇.Φ.Nonempty ∧ E₇.IsStarClosed ∧ E₇.IsIndecomposable ∧ finrank ℝ (span ℝ E₇.Φ) = 7) ∧
    (E₈.Φ.Nonempty ∧ E₈.IsStarClosed ∧ E₈.IsIndecomposable ∧ finrank ℝ (span ℝ E₈.Φ) = 8) ∧
    (E₈viaA₈.Φ.Nonempty ∧ E₈viaA₈.IsStarClosed ∧ E₈viaA₈.IsIndecomposable ∧
      finrank ℝ (span ℝ E₈viaA₈.Φ) = 8) ∧
    (E₈viaSteiner.Φ.Nonempty ∧ E₈viaSteiner.IsStarClosed ∧ E₈viaSteiner.IsIndecomposable ∧
      finrank ℝ (span ℝ E₈viaSteiner.Φ) = 8) :=
  ⟨⟨by rw [numLines_An], finrank_span_An 1⟩,
    fun _ hn => ⟨An.Φ_nonempty hn, isStarClosed_An _, isIndecomposable_An hn, finrank_span_An _⟩,
    fun _ hn => ⟨Dn.Φ_nonempty (by omega), isStarClosed_Dn _, isIndecomposable_Dn hn,
      finrank_span_Dn (by omega)⟩,
    ⟨E₆.Φ_nonempty, isStarClosed_E₆, isIndecomposable_E₆, finrank_span_E₆⟩,
    ⟨E₇.Φ_nonempty, isStarClosed_E₇, isIndecomposable_E₇, finrank_span_E₇⟩,
    ⟨E₈.Φ_nonempty, isStarClosed_E₈, isIndecomposable_E₈, finrank_span_E₈⟩,
    ⟨E₈viaA₈.Φ_nonempty, isStarClosed_E₈viaA₈, isIndecomposable_E₈viaA₈, finrank_span_E₈viaA₈⟩,
    ⟨E₈viaSteiner.Φ_nonempty, isStarClosed_E₈viaSteiner, isIndecomposable_E₈viaSteiner,
      finrank_span_E₈viaSteiner⟩⟩

-- Computation C4
/-- C4, the table of the blueprint for the marked star `a = e₁ - e₂`, `b = e₂ - e₃` (in `Fin`,
`e₀ - e₁` and `e₁ - e₂`): for `Aₙ` the graph on Γa is void on `n - 2` vertices, for `Dₙ` it is
the friendship graph of `n - 3` triangles, and for E₆, E₇, E₈ it is strongly regular with
`|Γa| = 9, 15, 27` and `|Δ| = 12, 30, 72` (6, 15, 36 lines). -/
theorem marked_star_data :
    (∀ n (hn : 2 ≤ n), (An.hyp24 hn).S = An n ∧
      (An.hyp24 hn).a =
        EuclideanSpace.single ⟨0, by omega⟩ 1 - EuclideanSpace.single ⟨1, by omega⟩ 1 ∧
      (An.hyp24 hn).b =
        EuclideanSpace.single ⟨1, by omega⟩ 1 - EuclideanSpace.single ⟨2, by omega⟩ 1 ∧
      Nonempty ((⊥ : SimpleGraph (Fin (n - 2))) ≃g (An.hyp24 hn).orthGraph) ∧
      (An.hyp24 hn).Γa.ncard = n - 2) ∧
    (∀ n (hn : 4 ≤ n), (Dn.hyp24 hn).S = Dn n ∧
      (Dn.hyp24 hn).a =
        EuclideanSpace.single ⟨0, by omega⟩ 1 - EuclideanSpace.single ⟨1, by omega⟩ 1 ∧
      (Dn.hyp24 hn).b =
        EuclideanSpace.single ⟨1, by omega⟩ 1 - EuclideanSpace.single ⟨2, by omega⟩ 1 ∧
      Nonempty (friendship (n - 3) ≃g (Dn.hyp24 hn).orthGraph) ∧
      (Dn.hyp24 hn).Γa.ncard = 2 * (n - 3) + 1) ∧
    (E₆.hyp24Simple.S = E₆ ∧
      E₆.hyp24Simple.a = EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1 ∧
      E₆.hyp24Simple.b = EuclideanSpace.single 1 1 - EuclideanSpace.single 2 1 ∧
      E₆.hyp24Simple.orthGraph.IsSRGWith 9 4 1 2 ∧
      E₆.hyp24Simple.Γa.ncard = 9 ∧ E₆.hyp24Simple.Δ.ncard = 12) ∧
    (E₇.hyp24Simple.S = E₇ ∧
      E₇.hyp24Simple.a = EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1 ∧
      E₇.hyp24Simple.b = EuclideanSpace.single 1 1 - EuclideanSpace.single 2 1 ∧
      E₇.hyp24Simple.orthGraph.IsSRGWith 15 6 1 3 ∧
      E₇.hyp24Simple.Γa.ncard = 15 ∧ E₇.hyp24Simple.Δ.ncard = 30) ∧
    (E₈.hyp24Simple.S = E₈ ∧
      E₈.hyp24Simple.a = EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1 ∧
      E₈.hyp24Simple.b = EuclideanSpace.single 1 1 - EuclideanSpace.single 2 1 ∧
      E₈.hyp24Simple.orthGraph.IsSRGWith 27 10 1 5 ∧
      E₈.hyp24Simple.Γa.ncard = 27 ∧ E₈.hyp24Simple.Δ.ncard = 72) :=
  ⟨fun _ hn => ⟨rfl, An.hyp24_a hn, An.hyp24_b hn, ⟨An.orthGraphIso hn⟩, An.card_Γa hn⟩,
    fun _ hn => ⟨rfl, Dn.hyp24_a hn, Dn.hyp24_b hn, ⟨Dn.orthGraphIso hn⟩, Dn.card_Γa hn⟩,
    ⟨rfl, E₆.hyp24Simple_a, E₆.hyp24Simple_b, E₆.hyp24Simple.orthGraph_isSRGWith_of_S_eq_E₆ rfl,
      E₆.hyp24Simple.card_Γa_of_S_eq_E₆ rfl, E₆.hyp24Simple.card_Δ_of_S_eq_E₆ rfl⟩,
    ⟨rfl, E₇.hyp24Simple_a, E₇.hyp24Simple_b, E₇.hyp24Simple.orthGraph_isSRGWith_of_S_eq_E₇ rfl,
      E₇.hyp24Simple.card_Γa_of_S_eq_E₇ rfl, E₇.hyp24Simple.card_Δ_of_S_eq_E₇ rfl⟩,
    ⟨rfl, E₈.hyp24Simple_a, E₈.hyp24Simple_b, E₈.hyp24Simple.orthGraph_isSRGWith_of_S_eq_E₈ rfl,
      E₈.hyp24Simple.card_Γa_of_S_eq_E₈ rfl, E₈.hyp24Simple.card_Δ_of_S_eq_E₈ rfl⟩⟩

-- Computation C4
/-- C4, the exceptional rows for **every** ordered star `(H.a, H.b)` of the fixed model: the
orthogonality graph is strongly regular with the stated parameters, `|Γa| = 9, 15, 27`,
`|Δ| = 12, 30, 72` (6, 15, 36 lines), and the graph is `L₂(3)` for E₆ and the complement of
`T(6)` for E₇. -/
theorem exceptional_star_data (H : Hyp24 (EuclideanSpace ℝ (Fin 8))) :
    (H.S = E₆ → H.orthGraph.IsSRGWith 9 4 1 2 ∧ H.Γa.ncard = 9 ∧ H.Δ.ncard = 12 ∧
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g H.orthGraph)) ∧
    (H.S = E₇ → H.orthGraph.IsSRGWith 15 6 1 3 ∧ H.Γa.ncard = 15 ∧ H.Δ.ncard = 30 ∧
      Nonempty ((completeGraph (Fin 6)).lineGraphᶜ ≃g H.orthGraph)) ∧
    (H.S = E₈ → H.orthGraph.IsSRGWith 27 10 1 5 ∧ H.Γa.ncard = 27 ∧ H.Δ.ncard = 72) :=
  ⟨fun hS => ⟨H.orthGraph_isSRGWith_of_S_eq_E₆ hS, H.card_Γa_of_S_eq_E₆ hS,
      H.card_Δ_of_S_eq_E₆ hS, H.nonempty_latticeGraph_iso_of_S_eq_E₆ hS⟩,
    fun hS => ⟨H.orthGraph_isSRGWith_of_S_eq_E₇ hS, H.card_Γa_of_S_eq_E₇ hS,
      H.card_Δ_of_S_eq_E₇ hS, H.nonempty_triangularGraph_compl_iso_of_S_eq_E₇ hS⟩,
    fun hS => ⟨H.orthGraph_isSRGWith_of_S_eq_E₈ hS, H.card_Γa_of_S_eq_E₈ hS,
      H.card_Δ_of_S_eq_E₈ hS⟩⟩

end Computations.C4
