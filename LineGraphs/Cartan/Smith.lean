/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.SmithGram

/-!
# The Smith graphs

Theorem 3.8 of [CGSS], Corollary D (`thm:3.8`, `cor:D`) of the Remark 3.11 blueprint.
The classification is an equivalence at largest eigenvalue exactly two. The graph models
are the existing `smithA`, `smithD`, and `smithE₆`, `smithE₇`, `smithE₈`:

* `smithA ℓ` is the cycle on `Fin (ℓ + 1)`, with `ℓ ≥ 2`.
* `smithD ℓ` is on `Fin (ℓ - 4 + 1) ⊕ Fin 4`, with `ℓ ≥ 4`.
* The exceptional models are on `ArmVertex ![2, 2, 2]`, `ArmVertex ![1, 3, 3]`, and
  `ArmVertex ![1, 2, 5]`, respectively. `ArmVertex a` is `Option ((r : Fin 3) × Fin (a r))`.

The proof follows steps `rDunit` through `rDtransport`: the weighted dichotomy supplies
an affine obstruction, unit weights exclude its four weighted families, and equality in
Rayleigh monotonicity makes the containment an isomorphism. The converse transports the
previously proved spectral values. `smith_exists_gram` supplies the spanning realization;
the imported `smith_gram_delete_basis` already proves every deletion in every realization.
-/

open Matrix

namespace WeightedGraph

variable {ι κ : Type*}

-- Theorem 3.8
/-- Corollary D, step `rDequal` of the blueprint for Theorem 3.8 of [CGSS]: reindexing
weighted vertices induces the same isomorphism of support graphs. -/
def supportReindexIso (X : WeightedGraph ι) (e : ι ≃ κ) :
    X.support ≃g (X.reindex e).support where
  toEquiv := e
  map_rel_iff' := by
    intro i j
    simp [support, reindex, Matrix.reindex_apply]

-- Theorem 3.8
/-- Corollary D, steps `rDproper` and `rDequal` of the blueprint for Theorem 3.8 of
[CGSS]: equality in Rayleigh monotonicity turns a containment into a support isomorphism. -/
theorem Contains.nonempty_iso_of_maxRayleigh_eq
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    {X : WeightedGraph ι} {Y : WeightedGraph κ} {e : κ ↪ ι} (he : X.Contains Y e)
    (hconn : X.support.Connected)
    (hmax : maxRayleigh Y.isHermitian = maxRayleigh X.isHermitian) :
    Nonempty (Y.support ≃g X.support) := by
  obtain ⟨hsurj, hweights⟩ := he.eq_of_maxRayleigh_eq hconn hmax
  exact ⟨{
    toEquiv := Equiv.ofBijective e ⟨e.injective, hsurj⟩
    map_rel_iff' := by
      intro i j
      change (0 < X.weights (e i) (e j)) ↔ 0 < Y.weights i j
      rw [hweights i j] }⟩

-- Theorem 3.8
/-- Corollary D, steps `rDunit` and `rDobstructionUnit` of the blueprint for Theorem 3.8
of [CGSS]: an affine obstruction with weights at most one is isomorphic to a Smith graph.
The bound excludes the endpoint, fork, middle, and triple weighted obstructions. -/
theorem IsAffineObstruction.nonempty_iso_smith {X : WeightedGraph ι}
    (hX : X.IsAffineObstruction) (hunit : ∀ i j, X.weights i j ≤ 1) :
    (∃ ℓ, 2 ≤ ℓ ∧ Nonempty (X.support ≃g SimpleGraph.smithA ℓ)) ∨
    (∃ ℓ, 4 ≤ ℓ ∧ Nonempty (X.support ≃g SimpleGraph.smithD ℓ)) ∨
    Nonempty (X.support ≃g SimpleGraph.smithE₆) ∨
    Nonempty (X.support ≃g SimpleGraph.smithE₇) ∨
    Nonempty (X.support ≃g SimpleGraph.smithE₈) := by
  have hsqrt2 : ¬ Real.sqrt 2 ≤ 1 := by norm_num
  have hsqrt3 : ¬ Real.sqrt 3 ≤ 1 := by norm_num
  cases hX with
  | cycle ℓ hℓ e h =>
    subst X
    left
    refine ⟨ℓ, hℓ, ?_⟩
    simpa only [support_unit] using
      (⟨(supportReindexIso (unit (SimpleGraph.smithA ℓ)) e).symm⟩ : Nonempty _)
  | d ℓ hℓ e h =>
    subst X
    exact Or.inr (Or.inl ⟨ℓ, hℓ, ⟨(supportReindexIso (affineD ℓ) e).symm⟩⟩)
  | e₆ e h =>
    subst X
    apply Or.inr ∘ Or.inr ∘ Or.inl
    simpa only [support_unit] using
      (⟨(supportReindexIso (unit SimpleGraph.smithE₆) e).symm⟩ : Nonempty _)
  | e₇ e h =>
    subst X
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    simpa only [support_unit] using
      (⟨(supportReindexIso (unit SimpleGraph.smithE₇) e).symm⟩ : Nonempty _)
  | e₈ e h =>
    subst X
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    simpa only [support_unit] using
      (⟨(supportReindexIso (unit SimpleGraph.smithE₈) e).symm⟩ : Nonempty _)
  | ends m hm e h =>
    subst X
    exfalso
    apply hsqrt2
    have hb := hunit (e ⟨0, by omega⟩) (e ⟨1, by omega⟩)
    simp only [WeightedGraph.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at hb
    simp [endPath, path] at hb
  | fork k hk e h =>
    subst X
    exfalso
    apply hsqrt2
    have hlast : k - 1 + 1 = k := by omega
    have hb := hunit (e (.inl ⟨k - 1, by omega⟩)) (e (.inl ⟨k, by omega⟩))
    simp only [WeightedGraph.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at hb
    simp [WeightedGraph.fork, attachLeaves, path, hlast] at hb
  | middle e h =>
    subst X
    exfalso
    apply hsqrt2
    have hb := hunit (e 2) (e 3)
    simp only [WeightedGraph.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at hb
    simp [middlePath, path] at hb
  | triple e h =>
    subst X
    exfalso
    apply hsqrt3
    have hb := hunit (e 0) (e 1)
    simp only [WeightedGraph.reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at hb
    simp [triplePath, path] at hb

end WeightedGraph

namespace SimpleGraph

-- Theorem 3.8
/-- Corollary D, step `rDtransport` of the blueprint for Theorem 3.8 of [CGSS]: a graph
isomorphism preserves the largest adjacency eigenvalue by Rayleigh reindexing. -/
theorem Iso.maxRayleigh_eq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    {X : SimpleGraph ι} {Y : SimpleGraph κ} [DecidableRel X.Adj] [DecidableRel Y.Adj]
    (e : X ≃g Y) :
    maxRayleigh (X.isHermitian_adjMatrix ℝ) = maxRayleigh (Y.isHermitian_adjMatrix ℝ) := by
  have h := (X.isHermitian_adjMatrix ℝ).maxRayleigh_reindex e.toEquiv
  have hmatrix : Matrix.reindex e.toEquiv e.toEquiv (X.adjMatrix ℝ) = Y.adjMatrix ℝ :=
    e.reindex_adjMatrix ℝ
  simpa only [hmatrix] using h.symm

-- Theorem 3.8
/-- Theorem 3.8 of [CGSS], Corollary D (`thm:3.8`, `cor:D`) of the Remark 3.11 blueprint:
a finite connected simple graph has largest adjacency eigenvalue two if and only if it
is isomorphic to one of the Smith graphs. This is step `rDclassification`, including both
`rDforward` (weighted dichotomy and strict monotonicity) and `rDbackward` (reindexing).
The cycle `smithA ℓ` has `ℓ + 1` vertices, so its bound is `ℓ ≥ 2`. -/
theorem smith {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : SimpleGraph ι) [DecidableRel X.Adj] (hconn : X.Connected) :
    maxRayleigh (X.isHermitian_adjMatrix ℝ) = 2 ↔
      (∃ ℓ, 2 ≤ ℓ ∧ Nonempty (X ≃g smithA ℓ)) ∨
      (∃ ℓ, 4 ≤ ℓ ∧ Nonempty (X ≃g smithD ℓ)) ∨
      Nonempty (X ≃g smithE₆) ∨ Nonempty (X ≃g smithE₇) ∨ Nonempty (X ≃g smithE₈) := by
  classical
  constructor
  · intro hmax
    have hconn' : (WeightedGraph.unit X).support.Connected := by simpa using hconn
    have hweights : ∀ i j, (WeightedGraph.unit X).support.Adj i j →
        (WeightedGraph.unit X).weights i j = 1 ∨
        (WeightedGraph.unit X).weights i j = Real.sqrt 2 ∨
        (WeightedGraph.unit X).weights i j = Real.sqrt 3 := by
      intro i j hij
      left
      have hij' : X.Adj i j := by simpa using hij
      exact ite_eq_left hij'
    rcases (WeightedGraph.affine_or_dynkin hconn' hweights).1 with hobs | hdynkin
    · obtain ⟨κ, hfin, hne, Y, hY, e, he⟩ := hobs
      have hunit : ∀ i j, Y.weights i j ≤ 1 := by
        intro i j
        apply (he i j).trans
        change X.adjMatrix ℝ (e i) (e j) ≤ 1
        simp only [adjMatrix_apply]
        split_ifs <;> norm_num
      obtain ⟨f⟩ := he.nonempty_iso_of_maxRayleigh_eq hconn'
        (hY.maxRayleigh_eq_two.trans hmax.symm)
      have f' : X ≃g Y.support := by simpa only [WeightedGraph.support_unit] using f.symm
      rcases hY.nonempty_iso_smith hunit with
        ⟨ℓ, hℓ, ⟨g⟩⟩ | ⟨ℓ, hℓ, ⟨g⟩⟩ | hg | hg | hg
      · exact Or.inl ⟨ℓ, hℓ, ⟨f'.trans g⟩⟩
      · exact Or.inr (Or.inl ⟨ℓ, hℓ, ⟨f'.trans g⟩⟩)
      · obtain ⟨g⟩ := hg
        exact Or.inr (Or.inr (Or.inl ⟨f'.trans g⟩))
      · obtain ⟨g⟩ := hg
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f'.trans g⟩)))
      · obtain ⟨g⟩ := hg
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f'.trans g⟩)))
    · have hlt : maxRayleigh (X.isHermitian_adjMatrix ℝ) < 2 :=
        hdynkin.maxRayleigh_lt_two
      rw [hmax] at hlt
      exact (lt_irrefl _ hlt).elim
  · rintro (⟨ℓ, hℓ, ⟨e⟩⟩ | ⟨ℓ, _, ⟨e⟩⟩ | he | he | he)
    · exact e.maxRayleigh_eq.trans (smithA_maxRayleigh ℓ hℓ)
    · exact e.maxRayleigh_eq.trans (smithD_maxRayleigh ℓ)
    · obtain ⟨e⟩ := he
      exact e.maxRayleigh_eq.trans smithE₆_maxRayleigh
    · obtain ⟨e⟩ := he
      exact e.maxRayleigh_eq.trans smithE₇_maxRayleigh
    · obtain ⟨e⟩ := he
      exact e.maxRayleigh_eq.trans smithE₈_maxRayleigh

-- Theorem 3.8
/-- Theorem 3.8 of [CGSS], Corollary D, step `rDrealize` of the Remark 3.11 blueprint:
at largest adjacency eigenvalue two, `2I - B` has a spanning realization by vectors of
norm `√2` in dimension `m - 1`. The imported `smith_gram_delete_basis` proves the basis
assertion for every deletion in every realization. -/
theorem smith_exists_gram {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : SimpleGraph ι) [DecidableRel X.Adj] (hconn : X.Connected)
    (hmax : maxRayleigh (X.isHermitian_adjMatrix ℝ) = 2) :
    ∃ v : ι → EuclideanSpace ℝ (Fin (Fintype.card ι - 1)),
      gram ℝ v = (2 : ℝ) • 1 - X.adjMatrix ℝ ∧
      Submodule.span ℝ (Set.range v) = ⊤ ∧ ∀ i, ‖v i‖ = Real.sqrt 2 := by
  obtain ⟨v, hgram, hspan, hnorm⟩ := (WeightedGraph.unit X).exists_gram_card_sub_one
    (by simpa using hconn) hmax
  refine ⟨v, hgram, hspan, fun i ↦ ?_⟩
  rw [norm_eq_sqrt_real_inner, hnorm i]

end SimpleGraph
