/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Graphs.Basic
import LineGraphs.Representation.ClawsCriteria
import LineGraphs.Representation.GeneralizedRepresentation
import LineGraphs.Representation.Remarks
import LineGraphs.Representation.Valency
import LineGraphs.Computations.C20Classical
import LineGraphs.Computations.C20E6
import LineGraphs.Computations.C20E7
import LineGraphs.Computations.C7Data
import LineGraphs.Computations.C9Data

/-!
# Unnumbered claims of [CGSS], Section 4

Claims of [CGSS], Section 4, that had no Lean statement of their own, found by the statement audit
(`LineGraphs/AUDIT-statements.md`): three remarks among the definitions
(finding L1), the first clause of the remark after Theorem 4.1 (L3), the valency bounds of
Computation C20 (L4), and the agreement of the integer tables of C7 and C9 with the paper's
formulas (L5). Page references are to [CGSS], J. Algebra 43 (1976), 305–327. In the formulas for the
integer tables, the coordinates `e₁, e₂, …` are numbered from 1, as in the paper.

## Main definitions

* `SimpleGraph.topIsoLineGraphStar`: the isomorphism `K_n ≅ L(K_{1,n})` (p. 315).
* `SimpleGraph.cocktailPartyVector`: the vectors `e₀ + eᵢ` and `e₀ - eᵢ` of `CP(a)` (p. 316).
* `Computations.pairsT`, `Computations.C9.switchedSums`, `Computations.C7.tripledZ` and the like:
  the paper's formulas for the vectors of Theorem 4.3 and Examples 4.5 to 4.9, as integer lists.

## Main statements

* `SimpleGraph.nonempty_iso_top_lineGraph_star`: `K_n = L(K_{1,n})` (p. 315).
* `SimpleGraph.cocktailParty_isRepresentation`, `SimpleGraph.cocktailParty_isRepresentedIn_Dn`:
  `CP(a)` is represented by the set `{e₀ + eᵢ, e₀ - eᵢ}` (p. 316), and in `D_{1+a}`.
* `SimpleGraph.generalizedLineGraph_leastEigenvalue_eq_neg_two`: the least eigenvalue of
  `L(G; a₁, …, a_m)` is `-2` if the number of vertices exceeds `n = ∑ (1 + aᵢ)` (p. 316).
* `LineSystem.An.exists_isRepresentation_lineGraph_completeBipartite_of_maximal`: the maximal
  subsets of `A_n` with nonnegative inner products represent the graphs `L(K_{m,n+1-m})`
  (remark after Theorem 4.1, p. 316); `LineSystem.An.exists_maximal_isRepresentation_lineGraph`
  gives every `m` with `1 ≤ m ≤ n`.
* `SimpleGraph.IsRepresentedIn.degree_le_An`, `SimpleGraph.IsRepresentedIn.degree_le_Dn`,
  `SimpleGraph.IsRepresentedIn.degree_le_E₆`, `SimpleGraph.IsRepresentedIn.degree_le_E₇`: the
  valency bounds `ℓ - 1`, `2(ℓ - 2)`, 10 and 16 of Computation C20 of the blueprint
  (`comp:C20`). The paper states the bound 28 for `E₈` (Theorem 4.3, p. 317; this is
  `SimpleGraph.IsRepresentedIn.degree_le_28`), and the proof of Theorem 4.4 uses the bound 16 for
  a graph represented in `E₇` or `D₇` (p. 318).
* `Computations.C9.changIRoots_perm`, `Computations.C9.changIIRoots_perm`,
  `Computations.C9.changIIIRoots_perm`, `Computations.C9.schlafliRoots_perm`,
  `Computations.C9.shrikhandeRoots_perm`, `Computations.C9.clebschRoots_perm`,
  `Computations.C9.petersenRoots_perm`, `Computations.C7.roots_perm`: each integer table of C9 and
  C7 is, up to order, the list given by the paper's formula (Examples 4.5 to 4.9, pp. 318–319, and
  Theorem 4.3, p. 317), checked by the kernel.
-/

open scoped RealInnerProductSpace
open EuclideanSpace

namespace SimpleGraph

/-! ### The definitions of Section 4 (finding L1) -/

-- Section 4, before Theorem 4.1
/-- [CGSS], Section 4, before Theorem 4.1 (p. 315): the isomorphism `K_n ≅ L(K_{1,n})`, for
the star `K_{1,n} = completeBipartiteGraph (Fin 1) V`. The vertex `v` goes to the edge from the
centre to the leaf `v`; any two edges of the star meet at its centre. -/
noncomputable def topIsoLineGraphStar (V : Type*) :
    (⊤ : SimpleGraph V) ≃g (completeBipartiteGraph (Fin 1) V).lineGraph where
  toEquiv := (Equiv.uniqueProd V (Fin 1)).symm.trans (completeBipartiteEdgeEquiv (Fin 1) V)
  map_rel_iff' {v w} := by
    simp [lineGraph_completeBipartiteGraph_adj]

-- Section 4, before Theorem 4.1
/-- [CGSS], Section 4, before Theorem 4.1 (p. 315): "Note that `K_n = L(K_{1,n})`". -/
theorem nonempty_iso_top_lineGraph_star (V : Type*) :
    Nonempty ((⊤ : SimpleGraph V) ≃g (completeBipartiteGraph (Fin 1) V).lineGraph) :=
  ⟨topIsoLineGraphStar V⟩

-- Section 4, before Theorem 4.2
/-- [CGSS], Section 4, before Theorem 4.2 (p. 316): the vectors `e₀ ± eᵢ` of `CP(a)` in
`ℝ^{1+a}`, with `e₀` the coordinate `0`. The vertex `(i, b)` of `cocktailParty a`, for
`i : Fin a`, carries `e₀ + e_{i+1}`, or `e₀ - e_{i+1}` when `b` is true. -/
noncomputable def cocktailPartyVector (a : ℕ) (u : Fin a × Bool) :
    EuclideanSpace ℝ (Fin (a + 1)) :=
  single 0 1 + single u.1.succ (if u.2 then -1 else 1)

-- Section 4, before Theorem 4.2
/-- [CGSS], Section 4, before Theorem 4.2 (p. 316): `CP(a)` "is represented by the set
`{e₀ + eᵢ, e₀ - eᵢ | i = 1, …, a}`". -/
theorem cocktailParty_isRepresentation (a : ℕ) :
    (cocktailParty a).IsRepresentation (cocktailPartyVector a) := by
  apply isRepresentation_iff.mpr
  rintro ⟨i, b⟩ ⟨j, c⟩
  have h0 (k : Fin a) : (0 : Fin (a + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      simp only [cocktailPartyVector, inner_add_left, inner_add_right] <;>
      simp [cocktailParty, inner_single_left, h0, Ne.symm (h0 _)] <;> norm_num
  · have hs : i.succ ≠ j.succ := fun h ↦ hij (Fin.succ_injective _ h)
    have hu : (i, b) ≠ (j, c) := fun h ↦ hij (congrArg Prod.fst h)
    simp [cocktailPartyVector, cocktailParty, inner_add_left, inner_add_right,
      inner_single_left, h0, Ne.symm (h0 _), hs, hij, hu]

-- Section 4, before Theorem 4.2
/-- [CGSS], Section 4, before Theorem 4.2 (p. 316): `CP(a)` is represented in `D_{1+a}`.
It is the generalized line graph of one vertex with `a` petals
(`SimpleGraph.cocktailPartyGeneralizedIso`), which is represented in `Dₙ` for `n = 1 + a`
(`SimpleGraph.generalizedLineGraph_isRepresentedIn_Dn`). -/
theorem cocktailParty_isRepresentedIn_Dn (a : ℕ) :
    (cocktailParty a).IsRepresentedIn (LineSystem.Dn (1 + a)) := by
  have h := generalizedLineGraph_isRepresentedIn_Dn (⊥ : SimpleGraph (Fin 1)) (fun _ ↦ a)
  rw [Fin.sum_univ_one] at h
  obtain ⟨x, hx, hm⟩ := h
  exact ⟨fun u ↦ x (cocktailPartyGeneralizedIso a u),
    hx.comp_iso (cocktailPartyGeneralizedIso a), fun u ↦ hm _⟩

-- Section 4, before Theorem 4.2
/-- [CGSS], Section 4, before Theorem 4.2 (p. 316): "the least eigenvalue of
`L(G; a₁, …, a_m)` is `-2` if the number of vertices exceeds `n`", where `n = ∑ (1 + aᵢ)` is the
dimension of the representation on p. 316 (`SimpleGraph.generalizedLineGraph_isRepresentation`
and `SimpleGraph.IsRepresentation.leastEigenvalue_eq_neg_two_of_finrank_lt`). -/
theorem generalizedLineGraph_leastEigenvalue_eq_neg_two {V : Type*} [Fintype V] [DecidableEq V]
    (Y : SimpleGraph V) [DecidableRel Y.Adj] (a : V → ℕ)
    [Nonempty (GeneralizedLineGraphVertex Y a)]
    (h : ∑ i, (1 + a i) < Fintype.card (GeneralizedLineGraphVertex Y a)) :
    (generalizedLineGraph Y a).leastEigenvalue = -2 := by
  apply (Y.generalizedLineGraph_isRepresentation a).leastEigenvalue_eq_neg_two_of_finrank_lt
  rw [finrank_euclideanSpace, Fintype.card_sigma]
  simpa [Nat.add_comm] using h

/-! ### The valencies of Computation C20 (finding L4) -/

variable {V : Type*} [Fintype V] [DecidableEq V] {X : SimpleGraph V} [DecidableRel X.Adj]

-- Computation C20
/-- Computation C20 of the blueprint (`comp:C20`), for `A_ℓ`: every vertex of a graph represented
in `A_ℓ` has at most `ℓ - 1` neighbours, since `|N_r| = 2(ℓ - 1)` (`LineSystem.An.card_N`).
[CGSS] states the valency bound only for `E₈` (Theorem 4.3, p. 317), from Lemma 3.7. -/
theorem IsRepresentedIn.degree_le_An {n : ℕ} (hX : X.IsRepresentedIn (LineSystem.An n))
    (u : V) : X.degree u ≤ n - 1 :=
  hX.degree_le_of_card_N_le (LineSystem.isStarClosed_An n)
    (fun _ hr ↦ (LineSystem.An.card_N hr).le) u

-- Computation C20
/-- Computation C20 of the blueprint (`comp:C20`), for `D_ℓ`: every vertex of a graph represented
in `D_ℓ` has at most `2(ℓ - 2)` neighbours, since `|N_r| = 4(ℓ - 2)` (`LineSystem.Dn.card_N`).
The proof of Theorem 4.4 of [CGSS] applies Lemma 3.7 to a graph represented in `E₇` or `D₇`
(p. 318). -/
theorem IsRepresentedIn.degree_le_Dn {n : ℕ} (hX : X.IsRepresentedIn (LineSystem.Dn n))
    (u : V) : X.degree u ≤ 2 * (n - 2) :=
  hX.degree_le_of_card_N_le (LineSystem.isStarClosed_Dn n)
    (fun _ hr ↦ by rw [LineSystem.Dn.card_N hr]; omega) u

-- Computation C20
/-- Computation C20 of the blueprint (`comp:C20`), for `E₆`: every vertex of a graph represented
in `E₆` has at most 10 neighbours, since `|N_r| = 20` (`LineSystem.E₆.card_N`). -/
theorem IsRepresentedIn.degree_le_E₆ (hX : X.IsRepresentedIn LineSystem.E₆) (u : V) :
    X.degree u ≤ 10 :=
  hX.degree_le_of_card_N_le LineSystem.isStarClosed_E₆
    (fun _ hr ↦ (LineSystem.E₆.card_N hr).le) u

-- Computation C20
/-- Computation C20 of the blueprint (`comp:C20`), for `E₇`: every vertex of a graph represented
in `E₇` has at most 16 neighbours, since `|N_r| = 32` (`LineSystem.E₇.card_N`). This is the bound
of the proof of Theorem 4.4 of [CGSS] (p. 318), from Lemma 3.7. -/
theorem IsRepresentedIn.degree_le_E₇ (hX : X.IsRepresentedIn LineSystem.E₇) (u : V) :
    X.degree u ≤ 16 :=
  hX.degree_le_of_card_N_le LineSystem.isStarClosed_E₇
    (fun _ hr ↦ (LineSystem.E₇.card_N hr).le) u

end SimpleGraph

namespace LineSystem.An

open SimpleGraph

/-- Classical adjacency decisions for the line graphs below, as in
`LineGraphs/Representation/Remarks.lean`. -/
noncomputable local instance decidableAdjSection4 {I : Type*} (Y : SimpleGraph I) :
    DecidableRel Y.Adj :=
  Classical.decRel _

-- Remark after Theorem 4.1
/-- Step `s4rarep` of the remark after Theorem 4.1 of [CGSS] (p. 316), with the sides of the
bipartition numbered: the vectors of `Σ_P`, indexed by the edges of `K_{m,n+1-m}` for `m = |P|`,
represent its line graph. -/
theorem exists_equiv_sigmaP_isRepresentation {n : ℕ} (P : Set (Fin (n + 1))) :
    ∃ e : (completeBipartiteGraph (Fin P.ncard) (Fin (n + 1 - P.ncard))).edgeSet ≃ sigmaP P,
      (completeBipartiteGraph (Fin P.ncard) (Fin (n + 1 - P.ncard))).lineGraph.IsRepresentation
        (fun u ↦ (e u : EuclideanSpace ℝ (Fin (n + 1)))) := by
  classical
  have hc := Set.ncard_add_ncard_compl P
  simp only [Nat.card_fin] at hc
  -- Number the two sides `P` and `Pᶜ` of the bipartition.
  let eP : Fin P.ncard ≃ P :=
    (finCongr (Nat.card_coe_set_eq P)).symm.trans (Finite.equivFin P).symm
  let eQ : Fin (n + 1 - P.ncard) ≃ ↥Pᶜ :=
    (finCongr (by rw [Nat.card_coe_set_eq]; omega)).trans (Finite.equivFin ↥Pᶜ).symm
  let f₁ := completeBipartiteEdgeEquiv (Fin P.ncard) (Fin (n + 1 - P.ncard))
  let f₂ := completeBipartiteEdgeEquiv P ↥Pᶜ
  -- The line graphs of the two complete bipartite graphs are isomorphic.
  let G : (completeBipartiteGraph (Fin P.ncard) (Fin (n + 1 - P.ncard))).lineGraph ≃g
      (completeBipartiteGraph P ↥Pᶜ).lineGraph :=
    { toEquiv := f₁.symm.trans ((Equiv.prodCongr eP eQ).trans f₂)
      map_rel_iff' := by
        intro u v
        obtain ⟨p, rfl⟩ := f₁.surjective u
        obtain ⟨q, rfl⟩ := f₁.surjective v
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, f₂, f₁,
          lineGraph_completeBipartiteGraph_adj, Prod.map, ne_eq, Prod.ext_iff,
          eP.injective.eq_iff, eQ.injective.eq_iff] }
  have hx := (isRepresentation_lineGraph_completeBipartite_sigmaP P).comp_iso G
  refine ⟨Equiv.ofBijective (fun u ↦ ⟨_, ?_⟩) ⟨?_, ?_⟩, hx⟩
  · exact ⟨_, (f₂.symm (G u)).1.property, _, (f₂.symm (G u)).2.property, rfl⟩
  · intro u v h
    exact hx.injective (congrArg Subtype.val h)
  · rintro ⟨z, p, hp, q, hq, rfl⟩
    refine ⟨G.symm (f₂ (⟨p, hp⟩, ⟨q, hq⟩)), ?_⟩
    simp only [RelIso.apply_symm_apply, Equiv.symm_apply_apply, f₂]

-- Remark after Theorem 4.1
/-- [CGSS], the remark after Theorem 4.1 (p. 316), first clause: "The maximal subsets of
`A_n` with nonnegative inner products represent the graphs `L(K_{m,n+1-m})`", for some
`1 ≤ m ≤ n`. It combines `LineSystem.An.nonneg_subset_maximal_iff` with
`LineSystem.An.isRepresentation_lineGraph_completeBipartite_sigmaP`, in the shape of
`LineSystem.Dn.exists_isRepresentation_generalizedLineGraph_top_of_maximal`. -/
theorem exists_isRepresentation_lineGraph_completeBipartite_of_maximal {n : ℕ} (hn : 1 ≤ n)
    {sigma : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hsigma : Maximal (An n).IsNonnegSubset sigma) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧
      ∃ e : (completeBipartiteGraph (Fin m) (Fin (n + 1 - m))).edgeSet ≃ sigma,
        (completeBipartiteGraph (Fin m) (Fin (n + 1 - m))).lineGraph.IsRepresentation
          (fun u ↦ (e u : EuclideanSpace ℝ (Fin (n + 1)))) := by
  obtain ⟨P, hP1, hPn, rfl⟩ := (nonneg_subset_maximal_iff hn).mp hsigma
  exact ⟨P.ncard, hP1, hPn, exists_equiv_sigmaP_isRepresentation P⟩

-- Remark after Theorem 4.1
/-- [CGSS], the remark after Theorem 4.1 (p. 316), first clause, in the other direction:
for every `1 ≤ m ≤ n`, the graph `L(K_{m,n+1-m})` is represented by a maximal subset of `A_n`
with nonnegative inner products. -/
theorem exists_maximal_isRepresentation_lineGraph {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ∃ sigma : Set (EuclideanSpace ℝ (Fin (n + 1))), Maximal (An n).IsNonnegSubset sigma ∧
      ∃ e : (completeBipartiteGraph (Fin m) (Fin (n + 1 - m))).edgeSet ≃ sigma,
        (completeBipartiteGraph (Fin m) (Fin (n + 1 - m))).lineGraph.IsRepresentation
          (fun u ↦ (e u : EuclideanSpace ℝ (Fin (n + 1)))) := by
  obtain ⟨P, -, rfl⟩ := Set.exists_subset_card_eq (s := (Set.univ : Set (Fin (n + 1))))
    (n := m) (by rw [Set.ncard_univ, Nat.card_fin]; omega)
  exact ⟨sigmaP P, (nonneg_subset_maximal_iff hn).mpr ⟨P, hm, hmn, rfl⟩,
    exists_equiv_sigmaP_isRepresentation P⟩

end LineSystem.An

/-! ### The tables of C7 and C9 against the paper's formulas (finding L5) -/

namespace Computations

/-- For [CGSS], Theorem 4.3 and Examples 4.5 to 4.9: the pairs `{i, j}` of `T(n, 2)`, as `(i, j)`
with `1 ≤ i < j ≤ n`, in the paper's numbering of the coordinates from 1. -/
def pairsT (n : ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 n).flatMap fun i ↦ (List.range' (i + 1) (n - i)).map ((i, ·))

namespace C9

/-- For [CGSS], Examples 4.5 to 4.9 (pp. 318–319): the vector `eᵢ + eⱼ` of `ℝ⁸`, doubled, that is
`2(eᵢ + eⱼ)`, with the coordinates numbered from 1 as in the paper. -/
def doubledSum (i j : ℕ) : IntVector :=
  (List.range' 1 8).map fun k ↦ if k = i ∨ k = j then 2 else 0

/-- For [CGSS], Examples 4.5 to 4.9 (pp. 318–319): the vector `½ ∑ₖ eₖ - eᵢ - eⱼ` of `ℝ⁸`,
doubled, that is `(1, …, 1) - 2eᵢ - 2eⱼ`, with the coordinates numbered from 1. -/
def doubledHalfSum (i j : ℕ) : IntVector :=
  (List.range' 1 8).map fun k ↦ if k = i ∨ k = j then -1 else 1

/-- For [CGSS], Examples 4.5, 4.7 and 4.9 (pp. 318–319): the vectors
`eᵢ + eⱼ` for the pairs `{i, j}` of `P`, doubled, where those of the switching set `S` are switched
into `½ ∑ₖ eₖ - eᵢ - eⱼ`. -/
def switchedSums (P S : List (ℕ × ℕ)) : List IntVector :=
  P.map fun p ↦ if p ∈ S ∨ (p.2, p.1) ∈ S then doubledHalfSum p.1 p.2 else doubledSum p.1 p.2

-- Example 4.5
/-- [CGSS], Example 4.5 (pp. 318–319): the table of Chang I is, up to order, `L(K₈)` represented
by `{eᵢ + eⱼ ; {i, j} ∈ T(8, 2)}`, switched with respect to `{eᵢ + e_{4+i} ; i = 1, 2, 3, 4}`,
doubled. -/
theorem changIRoots_perm :
    changIRoots.Perm (switchedSums (pairsT 8) ((List.range' 1 4).map fun i ↦ (i, 4 + i))) := by
  decide +kernel

-- Example 4.5
/-- [CGSS], Example 4.5 (pp. 318–319): the table of Chang II is, up to order, `L(K₈)` switched
with respect to `{eᵢ + e_{i+1} ; i = 1, 2, …, 8 mod 8}`, doubled. -/
theorem changIIRoots_perm :
    changIIRoots.Perm
      (switchedSums (pairsT 8) ((List.range' 1 8).map fun i ↦ (i, i % 8 + 1))) := by
  decide +kernel

-- Example 4.5
/-- [CGSS], Example 4.5 (pp. 318–319): the table of Chang III is, up to order, `L(K₈)` switched
with respect to `{e₁ + e₂, e₂ + e₃, e₃ + e₁} ∪ {e₄ + e₅, e₅ + e₆, e₆ + e₇, e₇ + e₈, e₈ + e₄}`,
doubled. -/
theorem changIIIRoots_perm :
    changIIIRoots.Perm (switchedSums (pairsT 8)
      [(1, 2), (2, 3), (3, 1), (4, 5), (5, 6), (6, 7), (7, 8), (8, 4)]) := by
  decide +kernel

-- Example 4.6
/-- [CGSS], Example 4.6 (p. 319): the table of the Schläfli graph is, up to order,
`{eᵢ + eⱼ ; {i, j} ∈ T(6, 2)} ∪ {½ ∑ eₖ - eᵢ - e₇ ; i ∈ T(6, 1)}`
`∪ {½ ∑ eₖ - eᵢ - e₈ ; i ∈ T(6, 1)}`, doubled, with the coefficient `½` of the second set for the
printed `⅓` (`cgss/errata.md`, Error 2). -/
theorem schlafliRoots_perm :
    schlafliRoots.Perm ((pairsT 6).map (fun p ↦ doubledSum p.1 p.2) ++
      (List.range' 1 6).map (doubledHalfSum · 7) ++
      (List.range' 1 6).map (doubledHalfSum · 8)) := by
  decide +kernel

-- Example 4.7
/-- [CGSS], Example 4.7 (p. 319): the table of the Shrikhande graph is, up to order,
`L(K₄,₄)` represented by `{eᵢ + eⱼ ; i = 1, 2, 3, 4 ; j = 5, 6, 7, 8}`, switched with respect to
`{eᵢ + e_{4+i} ; i = 1, 2, 3, 4}`, doubled. -/
theorem shrikhandeRoots_perm :
    shrikhandeRoots.Perm (switchedSums
      ((List.range' 1 4).flatMap fun i ↦ (List.range' 5 4).map ((i, ·)))
      ((List.range' 1 4).map fun i ↦ (i, 4 + i))) := by
  decide +kernel

-- Example 4.8
/-- [CGSS], Example 4.8 (p. 319): the table of the Clebsch graph is, up to order,
`{eᵢ + e₅} ∪ {eᵢ + e₆} ∪ {½ ∑ eₖ - eᵢ - e₇} ∪ {½ ∑ eₖ - eᵢ - e₈}`, for `i ∈ T(4, 1)`, doubled. -/
theorem clebschRoots_perm :
    clebschRoots.Perm ((List.range' 1 4).map (doubledSum · 5) ++
      (List.range' 1 4).map (doubledSum · 6) ++
      (List.range' 1 4).map (doubledHalfSum · 7) ++
      (List.range' 1 4).map (doubledHalfSum · 8)) := by
  decide +kernel

-- Example 4.9
/-- [CGSS], Example 4.9 (p. 319): the table of the Petersen graph is, up to order,
`L(K₃,₃)` plus an isolated vertex, represented by
`{e₄ + e₈} ∪ {eᵢ + eⱼ ; i = 1, 2, 3 ; j = 5, 6, 7}`, switched with respect to
`{eᵢ + e_{4+i} ; i = 1, 2, 3}`, doubled. -/
theorem petersenRoots_perm :
    petersenRoots.Perm (switchedSums
      ((4, 8) :: (List.range' 1 3).flatMap fun i ↦ (List.range' 5 3).map ((i, ·)))
      ((List.range' 1 3).map fun i ↦ (i, 4 + i))) := by
  decide +kernel

end C9

namespace C7

/-- For [CGSS], Theorem 4.3 (p. 317): the vector `-e₉ + eₕ` of `ℝ⁹`, tripled, with the
coordinates numbered from 1 as in the paper. -/
def tripledY (h : ℕ) : IntVector :=
  (List.range' 1 9).map fun k ↦ if k = h then 3 else if k = 9 then -3 else 0

/-- For [CGSS], Theorem 4.3 (p. 317): the vector `-e₉ - eᵢ - eⱼ + ⅓ ∑_{l=1}^{9} e_l` of
`ℝ⁹`, tripled, that is `(1, …, 1) - 3e₉ - 3eᵢ - 3eⱼ`. -/
def tripledZ (i j : ℕ) : IntVector :=
  (List.range' 1 9).map fun k ↦ if k = i ∨ k = j ∨ k = 9 then -2 else 1

-- Theorem 4.3
/-- [CGSS], Theorem 4.3 (p. 317): the table of C7 is, up to order, the `8 + 28` vectors
`-e₉ + eₕ`, `{h} ∈ T(8, 1)`, and `-e₉ - eᵢ - eⱼ + ⅓ ∑_{l=1}^{9} e_l`, `{i, j} ∈ T(8, 2)`,
tripled. -/
theorem roots_perm :
    roots.Perm ((List.range' 1 8).map tripledY ++ (pairsT 8).map fun p ↦ tripledZ p.1 p.2) := by
  decide +kernel

end C7

end Computations
