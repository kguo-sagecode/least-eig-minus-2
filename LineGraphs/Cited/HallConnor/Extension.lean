/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cited.HallConnor.PointsInCliques
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-!
# The labelled Hall–Connor extension

The construction `hc:def:extension`, its parameters `hc:lem:extension-parameters`, and
the residual identity `hc:thm:extension` ([CGSS], Remark 5.12 and Example 5.13).
-/

open scoped BigOperators Matrix

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]

/-- The new points are all six-cliques, `hc:def:extension` ([CGSS], Remark 5.12). -/
abbrev SixClique (D : Design P B 15 5 21 7 2) := {S : Finset B // S ∈ D.sixCliques}

variable (D : Design P B 15 5 21 7 2)

/-- There are seven new points, `hc:lem:extension-parameters` ([CGSS], Remark 5.12). -/
theorem card_SixClique : Fintype.card D.SixClique = 7 := by
  simpa only [SixClique, Fintype.card_coe] using D.card_sixCliques

/-- Counting a predicate on the subtype of six-cliques, `hc:lem:extension-parameters`
([CGSS], Remark 5.12). -/
theorem card_filter_SixClique (f : Finset B → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun S : D.SixClique ↦ f S.1)).card =
      (D.sixCliques.filter f).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ S : D.sixCliques, if f S.1 then (1 : ℕ) else 0) = _
  rw [Finset.sum_coe_sort D.sixCliques (fun S ↦ if f S then (1 : ℕ) else 0)]
  simp

/-- Block–six-clique incidence, `hc:def:extension` ([CGSS], Remark 5.12). -/
def sixCliqueIncMatrix : Matrix B D.SixClique ℤ :=
  fun X S ↦ if X ∈ S.1 then 1 else 0

/-- The extended labelled blocks, `hc:def:extension` ([CGSS], Remark 5.12). -/
def hallConnorBlocks : Option B → Finset (P ⊕ D.SixClique)
  | none => (∅ : Finset P).disjSum Finset.univ
  | some X => (D.block X).disjSum (Finset.univ.filter (fun S ↦ X ∈ S.1))

/-- The four entries of the extended incidence matrix, `hc:def:extension`
([CGSS], Remark 5.12). -/
def hallConnorIncMatrix : Matrix (P ⊕ D.SixClique) (Option B) ℤ
  | Sum.inl p, some X => D.incMatrix p X
  | Sum.inl _, none => 0
  | Sum.inr S, some X => D.sixCliqueIncMatrix X S
  | Sum.inr _, none => 1

/-- Each extended block has seven points, `hc:lem:extension-parameters`
([CGSS], Remark 5.12). -/
theorem card_hallConnorBlocks (X : Option B) : (D.hallConnorBlocks X).card = 7 := by
  cases X with
  | none => simp [hallConnorBlocks, D.card_sixCliques]
  | some X =>
    simp only [hallConnorBlocks, Finset.card_disjSum, D.card_block]
    rw [D.card_filter_SixClique (fun S ↦ X ∈ S), D.card_sixCliques_through_block]

/-- Each extended point has replication seven, `hc:lem:extension-parameters`
([CGSS], Remark 5.12). -/
theorem card_blocksThrough_hallConnorBlocks (p : P ⊕ D.SixClique) :
    (Finset.univ.filter (fun X ↦ p ∈ D.hallConnorBlocks X)).card = 7 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  cases p with
  | inl p => simp [hallConnorBlocks, D.card_blocksThrough]
  | inr S => simp [hallConnorBlocks, ((D.mem_sixCliques S.1).mp S.2).card_eq]

/-- Each pair of distinct extended points lies in two blocks, `hc:lem:extension-parameters`
([CGSS], Remark 5.12). The four cases are old–old, old–new, new–old, and new–new. -/
theorem card_blocksThroughPair_hallConnorBlocks (p q : P ⊕ D.SixClique) (hpq : p ≠ q) :
    (Finset.univ.filter (fun X ↦ p ∈ D.hallConnorBlocks X ∧
      q ∈ D.hallConnorBlocks X)).card = 2 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hne : p ≠ q := fun h ↦ hpq (congrArg Sum.inl h)
      simp [hallConnorBlocks, D.card_blocksThroughPair p q hne]
    | inr S =>
      have he : Finset.univ.filter (fun X ↦ p ∈ D.block X ∧ X ∈ S.1) =
          S.1.filter (fun X ↦ p ∈ D.block X) := by ext X; simp [and_comm]
      simpa [hallConnorBlocks, he] using D.card_blocksThrough_in_sixClique S.2 p
  | inr S =>
    cases q with
    | inl q =>
      have he : Finset.univ.filter (fun X ↦ X ∈ S.1 ∧ q ∈ D.block X) =
          S.1.filter (fun X ↦ q ∈ D.block X) := by ext X; simp
      simpa [hallConnorBlocks, he] using D.card_blocksThrough_in_sixClique S.2 q
    | inr T =>
      have hST : S.1 ≠ T.1 := fun h ↦ hpq (congrArg Sum.inr (Subtype.ext h))
      have he : Finset.univ.filter (fun X ↦ X ∈ S.1 ∧ X ∈ T.1) = S.1 ∩ T.1 := by
        ext X
        simp
      simp [hallConnorBlocks, he, D.sixClique_inter_card S.2 T.2 hST]

/-- The full parameter check `hc:lem:extension-parameters`
([CGSS], Remark 5.12 and Example 5.13). -/
theorem hallConnorBlocks_parameters :
    Fintype.card (P ⊕ D.SixClique) = 22 ∧ Fintype.card (Option B) = 22 ∧
      (∀ X, (D.hallConnorBlocks X).card = 7) ∧
      (∀ p, (Finset.univ.filter (fun X ↦ p ∈ D.hallConnorBlocks X)).card = 7) ∧
      (∀ p q, p ≠ q → (Finset.univ.filter (fun X ↦
        p ∈ D.hallConnorBlocks X ∧ q ∈ D.hallConnorBlocks X)).card = 2) := by
  exact ⟨by simp [D.card_points, D.card_SixClique], by simp [D.card_blocks],
    D.card_hallConnorBlocks, D.card_blocksThrough_hallConnorBlocks,
    D.card_blocksThroughPair_hallConnorBlocks⟩

/-- The symmetric extension, `hc:def:extension-design` (Hall–Connor Theorems 2.1 and 3.2
at `k = 5`; [CGSS], Remark 5.12 and Example 5.13). -/
def hallConnorExtension : Design (P ⊕ D.SixClique) (Option B) 22 7 22 7 2 where
  card_points := D.hallConnorBlocks_parameters.1
  card_blocks := D.hallConnorBlocks_parameters.2.1
  block := D.hallConnorBlocks
  card_block := D.card_hallConnorBlocks
  card_blocksThrough := D.card_blocksThrough_hallConnorBlocks
  card_blocksThroughPair := D.card_blocksThroughPair_hallConnorBlocks
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

/-- Symmetry of the extension, `hcExtSymmetric` ([CGSS], Remark 5.12). -/
theorem hallConnorExtension_isSymmetric : D.hallConnorExtension.IsSymmetric := rfl

/-- Deleting the new block and its points recovers every old labelled block,
`hcExtResidual` of `hc:thm:extension` ([CGSS], Remark 5.12 and Example 5.13). -/
theorem hallConnorExtension_residual (X : B) :
    D.hallConnorExtension.block (some X) \ D.hallConnorExtension.block none =
      (D.block X).map Function.Embedding.inl := by
  ext p
  cases p <;> simp [hallConnorExtension, hallConnorBlocks]

end Design
