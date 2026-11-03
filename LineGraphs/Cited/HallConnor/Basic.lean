/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Labelled designs for the Hall–Connor theorem

The definitions `hc:def:design`, `hc:def:matrices`, and `hc:def:graph` of the Hall–Connor
blueprint. These are the design parameters used in Remark 5.12 and Example 5.13 of [CGSS].
-/

open scoped BigOperators Matrix

/-- Labelled two-designs (`hc:def:design`), as used in Remark 5.12 and Example 5.13 of
[CGSS]. Repeated blocks are allowed; positivity is part of the standing design hypotheses. -/
structure Design (P B : Type*) [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
    (v k b r lam : ℕ) where
  card_points : Fintype.card P = v
  card_blocks : Fintype.card B = b
  block : B → Finset P
  card_block : ∀ label, (block label).card = k
  card_blocksThrough : ∀ p, (Finset.univ.filter (fun label ↦ p ∈ block label)).card = r
  card_blocksThroughPair : ∀ p q, p ≠ q →
    (Finset.univ.filter (fun label ↦ p ∈ block label ∧ q ∈ block label)).card = lam
  one_lt_v : 1 < v
  one_lt_k : 1 < k
  b_pos : 0 < b

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
variable {v k b r lam : ℕ}

/-- Symmetry of a labelled design (`hc:def:design`; [CGSS], Section 5). -/
def IsSymmetric (_D : Design P B v k b r lam) : Prop := v = b

/-- The integral point-block incidence matrix (`hc:def:matrices`; [CGSS], Section 5). -/
def incMatrix (D : Design P B v k b r lam) : Matrix P B ℤ :=
  fun p label ↦ if p ∈ D.block label then 1 else 0

/-- The rational block Gram matrix (`hc:def:matrices`; [CGSS], Remark 5.12). -/
def G (D : Design P B v k b r lam) : Matrix B B ℚ :=
  (D.incMatrix.map (Int.castRingHom ℚ)).transpose * D.incMatrix.map (Int.castRingHom ℚ)

/-- Connor's matrix at block size five (`hc:def:matrices`; [CGSS], Remark 5.12). -/
def C (D : Design P B v k b r lam) : Matrix B B ℚ :=
  (35 : ℚ) • (1 : Matrix B B ℚ) - (7 : ℚ) • D.G +
    (10 : ℚ) • Matrix.of (fun _ _ ↦ (1 : ℚ))

/-- The graph of intersections of size one (`hc:def:graph`; [CGSS], Remark 5.12). -/
def Z (D : Design P B v k b r lam) : SimpleGraph B where
  Adj X Y := X ≠ Y ∧ (D.block X ∩ D.block Y).card = 1
  symm := ⟨fun X Y h ↦ ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun X h ↦ h.1 rfl⟩

/-- All six-cliques of the block graph (`hc:def:graph`; [CGSS], Remark 5.12). -/
def sixCliques (D : Design P B v k b r lam) : Finset (Finset B) :=
  Finset.univ.filter fun S ↦ S.card = 6 ∧
    ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → (D.block X ∩ D.block Y).card = 1

omit [DecidableEq B] in
/-- The point count `hcParPoint` in `hc:lem:parameters`: each point lies in seven labels
([CGSS], Remark 5.12 and Example 5.13). -/
theorem card_blocksThrough_of_pair_counts_15_5_2 (F : B → Finset P)
    (hv : Fintype.card P = 15) (hk : ∀ label, (F label).card = 5)
    (hlam : ∀ p q, p ≠ q →
      (Finset.univ.filter (fun label ↦ p ∈ F label ∧ q ∈ F label)).card = 2)
    (p : P) : (Finset.univ.filter (fun label ↦ p ∈ F label)).card = 7 := by
  have h := Finset.card_mul_eq_card_mul (fun q label ↦ q ∈ F label)
    (s := Finset.univ.erase p) (t := Finset.univ.filter (fun label ↦ p ∈ F label))
    (m := 2) (n := 4) (fun q hq ↦ ?_) (fun label hlabel ↦ ?_)
  · simp only [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, hv] at h
    omega
  · have hpq : p ≠ q := (Finset.mem_erase.mp hq).1.symm
    simpa [Finset.bipartiteAbove, Finset.filter_filter] using hlam p q hpq
  · have hp : p ∈ F label := (Finset.mem_filter.mp hlabel).2
    have he : (Finset.univ.erase p).bipartiteBelow (fun q label ↦ q ∈ F label) label =
        (F label).erase p := by
      ext q
      simp [Finset.bipartiteBelow, and_comm]
    rw [he, Finset.card_erase_of_mem hp, hk]

omit [DecidableEq B] in
/-- The total count `hcParTotal` in `hc:lem:parameters`: there are twenty-one labels
([CGSS], Remark 5.12 and Example 5.13). -/
theorem card_blocks_of_pair_counts_15_5_2 (F : B → Finset P)
    (hv : Fintype.card P = 15) (hk : ∀ label, (F label).card = 5)
    (hlam : ∀ p q, p ≠ q →
      (Finset.univ.filter (fun label ↦ p ∈ F label ∧ q ∈ F label)).card = 2) :
    Fintype.card B = 21 := by
  have h := Finset.card_mul_eq_card_mul (fun p label ↦ p ∈ F label)
    (s := Finset.univ) (t := Finset.univ) (m := 7) (n := 5)
    (fun p _ ↦ card_blocksThrough_of_pair_counts_15_5_2 F hv hk hlam p)
    (fun label _ ↦ by simpa [Finset.bipartiteBelow] using hk label)
  simp only [Finset.card_univ, hv] at h
  omega

/-- The forced parameters, `hc:lem:parameters` of the Hall–Connor blueprint
([CGSS], Remark 5.12 and Example 5.13). The preceding two counts provide `r = 7` and `b = 21`. -/
theorem exists_of_pair_counts_15_5_2 (F : B → Finset P)
    (hv : Fintype.card P = 15) (hk : ∀ label, (F label).card = 5)
    (hlam : ∀ p q, p ≠ q →
      (Finset.univ.filter (fun label ↦ p ∈ F label ∧ q ∈ F label)).card = 2) :
    ∃ D : Design P B 15 5 21 7 2, ∀ label, D.block label = F label := by
  exact ⟨{
    card_points := hv
    card_blocks := card_blocks_of_pair_counts_15_5_2 F hv hk hlam
    block := F
    card_block := hk
    card_blocksThrough := card_blocksThrough_of_pair_counts_15_5_2 F hv hk hlam
    card_blocksThroughPair := hlam
    one_lt_v := by decide
    one_lt_k := by decide
    b_pos := by decide }, fun _ ↦ rfl⟩

end Design
