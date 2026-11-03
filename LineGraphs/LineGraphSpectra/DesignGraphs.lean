/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignParameters
import LineGraphs.LineGraphSpectra.Nonbipartite

/-!
# Incidence and flag graphs of labelled designs

Definitions `def:flag` and lemma `lem:incidence`, used in Theorem 5.8 of [CGSS].
These use the Hall–Connor design structure. The graph definition agrees with
the auxiliary incidence graph in computations C13 and C15.
-/

open Matrix SimpleGraph

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ} (D : Design P B v k b r lam)

/-- Definition `def:flag`, Theorem 5.8 of [CGSS]: the point-block incidence graph. -/
def incidenceGraph : SimpleGraph (P ⊕ B) where
  Adj
    | .inl p, .inr label => p ∈ D.block label
    | .inr label, .inl p => p ∈ D.block label
    | _, _ => False
  symm.symm := by rintro (p | label) (q | other) <;> simp
  loopless.irrefl := by rintro (p | label) <;> simp

/-- Decidable incidence in `def:flag`, Theorem 5.8 of [CGSS]. -/
instance incidenceGraphDecidable : DecidableRel D.incidenceGraph.Adj := fun u w ↦ by
  cases u <;> cases w <;> dsimp [incidenceGraph] <;> infer_instance

/-- Definition `def:flag`, Theorem 5.8 of [CGSS]: the flag graph is the incidence line graph. -/
def flagGraph : SimpleGraph D.incidenceGraph.edgeSet := D.incidenceGraph.lineGraph

attribute [local instance] Classical.propDecidable

/-- Definition `def:flag`, Corollaries 5.9–5.11 of [CGSS]. Characterization means
membership in the family of flag graphs with the same parameters (Implicit hypothesis 6).
The design, candidate graphs and comparison designs range over vertex types in `Type`;
finite graphs in other universes can be relabelled into this universe. -/
def FlagGraphCharacterized {P B : Type} [Fintype P] [Fintype B]
    [DecidableEq P] [DecidableEq B] {v k b r lam : ℕ} (D : Design P B v k b r lam) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj],
    D.flagGraph.Cospectral X →
      ∃ (P₂ B₂ : Type) (_ : Fintype P₂) (_ : Fintype B₂)
        (_ : DecidableEq P₂) (_ : DecidableEq B₂) (D₂ : Design P₂ B₂ v k b r lam),
        Nonempty (X ≃g D₂.flagGraph)

/-- Step `s5igdeg` of `lem:incidence`, Theorem 5.8 of [CGSS]: point degree. -/
theorem incidenceGraph_degree_inl (p : P) : D.incidenceGraph.degree (.inl p) = r := by
  have hn : D.incidenceGraph.neighborFinset (.inl p) =
      (Finset.univ.filter (fun label ↦ p ∈ D.block label)).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext w
    rw [D.incidenceGraph.mem_neighborFinset]
    cases w <;> simp [incidenceGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, Finset.card_map,
    D.card_blocksThrough]

/-- Step `s5igdeg` of `lem:incidence`, Theorem 5.8 of [CGSS]: block degree. -/
theorem incidenceGraph_degree_inr (label : B) : D.incidenceGraph.degree (.inr label) = k := by
  have hn : D.incidenceGraph.neighborFinset (.inr label) =
      (D.block label).map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext w
    rw [D.incidenceGraph.mem_neighborFinset]
    cases w <;> simp [incidenceGraph]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, Finset.card_map, D.card_block]

/-- Step `s5igparts` of `lem:incidence`, Theorem 5.8 of [CGSS]: the point part. -/
def pointPart (_D : Design P B v k b r lam) : Set (P ⊕ B) := Set.range Sum.inl

/-- Step `s5igparts` of `lem:incidence`, Theorem 5.8 of [CGSS]: the block part. -/
def blockPart (_D : Design P B v k b r lam) : Set (P ⊕ B) := Set.range Sum.inr

/-- Step `s5igparts` of `lem:incidence`, Theorem 5.8 of [CGSS]: the point-part coordinates. -/
noncomputable def pointPartEquiv : P ≃ D.pointPart :=
  Equiv.ofInjective Sum.inl Sum.inl_injective

/-- Step `s5igparts` of `lem:incidence`, Theorem 5.8 of [CGSS]: the block-part coordinates. -/
noncomputable def blockPartEquiv : B ≃ D.blockPart :=
  Equiv.ofInjective Sum.inr Sum.inr_injective

/-- Step `s5igparts` of `lem:incidence`, Theorem 5.8 of [CGSS]: point-part size. -/
theorem card_pointPart : Nat.card D.pointPart = v := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr D.pointPartEquiv, D.card_points]

/-- Step `s5igparts` of `lem:incidence`, Theorem 5.8 of [CGSS]: block-part size. -/
theorem card_blockPart : Nat.card D.blockPart = b := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr D.blockPartEquiv, D.card_blocks]

/-- Step `s5igbip` of `lem:incidence`, Theorem 5.8 of [CGSS]: biregularity. -/
theorem incidenceGraph_isBiregularWith :
    D.incidenceGraph.IsBiregularWith D.pointPart D.blockPart r k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Set.disjoint_left.mpr (by rintro _ ⟨p, rfl⟩ ⟨label, h⟩; cases h)
    · rintro (p | label) (q | other) h
      · exact h.elim
      · exact Or.inl ⟨⟨p, rfl⟩, ⟨other, rfl⟩⟩
      · exact Or.inr ⟨⟨label, rfl⟩, ⟨q, rfl⟩⟩
      · exact h.elim
  · ext (p | label) <;> simp [pointPart, blockPart]
  · rintro _ ⟨p, rfl⟩
    exact D.incidenceGraph_degree_inl p
  · rintro _ ⟨label, rfl⟩
    exact D.incidenceGraph_degree_inr label

/-- Step `s5igbip` of `lem:incidence`, Theorem 5.8 of [CGSS]: no isolated vertices. -/
theorem incidenceGraph_degree_pos (w : P ⊕ B) : 0 < D.incidenceGraph.degree w := by
  cases w with
  | inl p => rw [D.incidenceGraph_degree_inl]; exact D.r_pos
  | inr label => rw [D.incidenceGraph_degree_inr]; have := D.one_lt_k; omega

/-- Step `s5igbip` of `lem:incidence`, Theorem 5.8 of [CGSS]: an incidence edge exists. -/
theorem incidenceGraph_edgeSet_nonempty : D.incidenceGraph.edgeSet.Nonempty := by
  have : Nonempty B := Fintype.card_pos_iff.mp (D.card_blocks.symm ▸ D.b_pos)
  let label : B := Classical.arbitrary B
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (D.block label).card by
    rw [D.card_block]
    have := D.one_lt_k
    omega)
  exact ⟨s(Sum.inl p, Sum.inr label), hp⟩

/-- Step `s5igconn` of `lem:incidence`, Theorem 5.8 of [CGSS]: connected incidence graph. -/
theorem incidenceGraph_connected : D.incidenceGraph.Connected := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by
    rw [D.card_points]
    have := D.one_lt_v
    omega)
  have hpoints (p q : P) : D.incidenceGraph.Reachable (.inl p) (.inl q) := by
    by_cases hpq : p = q
    · subst q
      exact .refl _
    · obtain ⟨label, hl⟩ := Finset.card_pos.mp (show 0 <
          (Finset.univ.filter (fun label ↦ p ∈ D.block label ∧ q ∈ D.block label)).card by
        rw [D.card_blocksThroughPair p q hpq]
        exact D.one_le_lam)
      have hp : D.incidenceGraph.Adj (.inl p) (.inr label) := (Finset.mem_filter.mp hl).2.1
      have hq : D.incidenceGraph.Adj (.inr label) (.inl q) := (Finset.mem_filter.mp hl).2.2
      exact hp.reachable.trans hq.reachable
  have hblock (label : B) : ∃ p : P, D.incidenceGraph.Adj (.inr label) (.inl p) := by
    exact Finset.card_pos.mp (by rw [D.card_block]; have := D.one_lt_k; omega)
  refine { preconnected := ?_, nonempty := inferInstance }
  rintro (p | label) (q | other)
  · exact hpoints p q
  · obtain ⟨q, hq⟩ := hblock other
    exact (hpoints p q).trans hq.symm.reachable
  · obtain ⟨p, hp⟩ := hblock label
    exact hp.reachable.trans (hpoints p q)
  · obtain ⟨p, hp⟩ := hblock label
    obtain ⟨q, hq⟩ := hblock other
    exact hp.reachable.trans ((hpoints p q).trans hq.symm.reachable)

/-- Step `s5igreg` of `lem:incidence`, Theorem 5.8 of [CGSS]: regularity of the root. -/
theorem incidenceGraph_isRegular_iff :
    (∃ d, D.incidenceGraph.IsRegularOfDegree d) ↔ r = k := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by
    rw [D.card_points]
    have := D.one_lt_v
    omega)
  have : Nonempty B := Fintype.card_pos_iff.mp (D.card_blocks.symm ▸ D.b_pos)
  constructor
  · rintro ⟨d, hd⟩
    have hp := hd (.inl (Classical.arbitrary P))
    have hb := hd (.inr (Classical.arbitrary B))
    rw [D.incidenceGraph_degree_inl] at hp
    rw [D.incidenceGraph_degree_inr] at hb
    exact hp.trans hb.symm
  · intro he
    refine ⟨k, ?_⟩
    rintro (p | label)
    · simpa [he] using D.incidenceGraph_degree_inl p
    · exact D.incidenceGraph_degree_inr label

/-- Step `s5igflag` of `lem:incidence`, Theorem 5.8 of [CGSS]: flag connectedness. -/
theorem flagGraph_connected : D.flagGraph.Connected :=
  (SimpleGraph.lineGraph_connected_iff_of_no_isolated D.incidenceGraph_edgeSet_nonempty
    (fun w ↦ (D.incidenceGraph.degree_pos_iff_exists_adj w).mp
      (D.incidenceGraph_degree_pos w))).mpr D.incidenceGraph_connected

/-- Step `s5igflag` of `lem:incidence`, Theorem 5.8 of [CGSS]: flag regularity. -/
theorem flagGraph_isRegularOfDegree : D.flagGraph.IsRegularOfDegree (r + k - 2) :=
  D.incidenceGraph_isBiregularWith.lineGraph_isRegularOfDegree

/-- Step `s5igflag` of `lem:incidence`, Theorem 5.8 of [CGSS]: number of flags. -/
theorem card_flagGraph : Fintype.card D.incidenceGraph.edgeSet = v * r := by
  have h := D.incidenceGraph_isBiregularWith.card_mul_degree_left
  rw [D.card_pointPart] at h
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card] using h.symm

/-- Step `s5igrank` of `lem:incidence`, Theorem 5.8 of [CGSS]: Gram positivity. -/
theorem posSemidef_two_add_adjMatrix_flagGraph :
    ((2 : ℝ) • (1 : Matrix D.incidenceGraph.edgeSet D.incidenceGraph.edgeSet ℝ) +
      D.flagGraph.adjMatrix ℝ).PosSemidef := by
  change ((2 : ℝ) • (1 : Matrix D.incidenceGraph.edgeSet D.incidenceGraph.edgeSet ℝ) +
    D.incidenceGraph.lineGraph.adjMatrix ℝ).PosSemidef
  rw [← D.incidenceGraph.transpose_edgeIncMatrix_mul]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (D.incidenceGraph.edgeIncMatrix ℝ)

/-- Step `s5igrank` of `lem:incidence`, Theorem 5.8 of [CGSS]: Gram rank. -/
theorem rank_two_add_adjMatrix_flagGraph :
    ((2 : ℝ) • (1 : Matrix D.incidenceGraph.edgeSet D.incidenceGraph.edgeSet ℝ) +
      D.flagGraph.adjMatrix ℝ).rank = v + b - 1 := by
  have h := D.incidenceGraph_isBiregularWith.card_eq_rank_add_one D.incidenceGraph_connected
  rw [Fintype.card_sum, D.card_points, D.card_blocks] at h
  exact Nat.eq_sub_of_add_eq h.symm

/-- The real cast in `s5igparts` and `s558bippick`, Theorem 5.8 of [CGSS]:
the biadjacency matrix in point-block coordinates is the real incidence matrix. -/
theorem biadjMatrix_submatrix_eq_realIncMatrix :
    (D.incidenceGraph.biadjMatrix D.pointPart D.blockPart ℝ).submatrix
      D.pointPartEquiv D.blockPartEquiv = D.realIncMatrix := by
  ext p label
  change (if p ∈ D.block label then (1 : ℝ) else 0) = D.realIncMatrix p label
  exact (D.realIncMatrix_apply p label).symm

/-- The coordinate identification at `s558bippick`, Theorem 5.8 of [CGSS], for Gram spectra. -/
theorem spectrumMultiset_biadjMatrix_mul_transpose :
    let N := D.incidenceGraph.biadjMatrix D.pointPart D.blockPart ℝ
    (N * Nᵀ).spectrumMultiset =
      {(r : ℝ) * k} + Multiset.replicate (v - 1) ((r : ℝ) - lam) := by
  let N := D.incidenceGraph.biadjMatrix D.pointPart D.blockPart ℝ
  have h := D.biadjMatrix_submatrix_eq_realIncMatrix
  have hg : D.realIncMatrix * D.realIncMatrixᵀ =
      (N * Nᵀ).submatrix D.pointPartEquiv D.pointPartEquiv := by
    rw [← h, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  rw [← D.spectrumMultiset_incMatrix_mul_transpose, hg,
    Matrix.spectrumMultiset_submatrix_equiv]

/-- The coordinate identification at `s558nbrem`, Theorem 5.8 of [CGSS], for ranks. -/
theorem rank_biadjMatrix :
    (D.incidenceGraph.biadjMatrix D.pointPart D.blockPart ℝ).rank = D.realIncMatrix.rank := by
  rw [← D.biadjMatrix_submatrix_eq_realIncMatrix, Matrix.rank_submatrix]

end Design
