/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.AffineSpectrum
import LineGraphs.Cartan.UnweightedTrees

/-!
# Dynkin supports below the affine threshold

The support-recognition step of the weighted dichotomy and its application to
finite Cartan matrices.
-/

namespace WeightedGraph

open Matrix SimpleGraph

variable {ι κ : Type*}

/-- A weighted graph is determined by its matrix of weights. -/
@[ext]
theorem ext {X Y : WeightedGraph ι} (h : X.weights = Y.weights) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

open scoped Classical in
/-- `def:affine`, Remark 3.11 of [CGSS]: every edge of the affine D graph has unit weight. -/
theorem affineD_eq_unit (ℓ : ℕ) : affineD ℓ = unit (smithD ℓ) := by
  classical
  have hweights (i j : Fin (ℓ - 4 + 1) ⊕ Fin 4) :
      (affineD ℓ).weights i j = 0 ∨ (affineD ℓ).weights i j = 1 := by
    rcases i with i | i <;> rcases j with j | j
    · dsimp only [affineD, attachLeaves, path]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · dsimp only [affineD, attachLeaves]
      split_ifs <;> norm_num
    · dsimp only [affineD, attachLeaves]
      split_ifs <;> norm_num
    · exact Or.inl rfl
  apply ext
  funext i j
  simp only [unit, SimpleGraph.adjMatrix, smithD, support, Matrix.of_apply]
  rcases hweights i j with h | h <;> simp only [h] <;> norm_num

/-- Containment of an affine obstruction, with its finite nonempty vertex type and
specified vertex injection retained. -/
def ContainsAffineObstruction (X : WeightedGraph ι) : Prop :=
  ∃ (τ : Type) (_ : Fintype τ) (_ : Nonempty τ) (Y : WeightedGraph τ),
    Y.IsAffineObstruction ∧ ∃ e : τ ↪ ι, X.Contains Y e

/-- Exclusion of all affine obstructions excludes each specified containment. -/
theorem not_contains_of_no_affine {X : WeightedGraph ι}
    (hno : ¬ X.ContainsAffineObstruction) {τ : Type} [Finite τ] [Nonempty τ]
    {Y : WeightedGraph τ} (hY : Y.IsAffineObstruction) (e : τ ↪ ι) : ¬ X.Contains Y e := by
  let _ := Fintype.ofFinite τ
  exact fun h => hno ⟨τ, inferInstance, inferInstance, Y, hY, e, h⟩

/-- Affine-obstruction exclusion is preserved by a vertex reindexing. -/
theorem not_containsAffineObstruction_reindex {X : WeightedGraph ι}
    (hno : ¬ X.ContainsAffineObstruction) (e : ι ≃ κ) :
    ¬ (X.reindex e).ContainsAffineObstruction := by
  rintro ⟨τ, hfin, hnonempty, Y, hY, f, hf⟩
  apply hno
  refine ⟨τ, hfin, hnonempty, Y, hY, f.trans e.symm.toEmbedding, ?_⟩
  exact hf

variable [Fintype ι] [DecidableEq ι] [Nonempty ι] {X : WeightedGraph ι}

/-- A weighted graph below the affine threshold contains none of the affine obstructions. -/
theorem not_contains_affine_of_maxRayleigh_lt_two
    (hmax : maxRayleigh X.isHermitian < 2) [Finite κ] [Nonempty κ]
    {Y : WeightedGraph κ} (hY : Y.IsAffineObstruction) (e : κ ↪ ι) : ¬ X.Contains Y e := by
  classical
  let _ := Fintype.ofFinite κ
  intro h
  have hle := maxRayleigh_mono h
  rw [hY.maxRayleigh_eq_two] at hle
  exact (not_le_of_gt hmax) hle

/-- A graph below the affine spectral threshold contains no affine obstruction. -/
theorem not_containsAffineObstruction_of_maxRayleigh_lt_two
    (hmax : maxRayleigh X.isHermitian < 2) : ¬ X.ContainsAffineObstruction := by
  rintro ⟨τ, hfin, hnonempty, Y, hY, e, he⟩
  exact not_contains_affine_of_maxRayleigh_lt_two hmax hY e he

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Excluding affine obstructions forces acyclic support when all edge weights are at least one. -/
theorem support_isAcyclic_of_no_affine
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hno : ¬ X.ContainsAffineObstruction) : X.support.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨hn, e, he⟩ := hp.exists_cycle_embedding
  have he' := (X.unit_contains_iff_support_embedding hweights (cycleGraph p.length) e).mpr he
  have hobs : (unit (cycleGraph p.length)).IsAffineObstruction := by
    obtain ⟨k, hk⟩ : ∃ k, p.length = k + 1 := ⟨p.length - 1, by omega⟩
    rw [hk]
    exact .cycle k (by omega) (Equiv.refl _) rfl
  have : Nonempty (Fin p.length) := ⟨⟨0, by omega⟩⟩
  exact not_contains_of_no_affine hno hobs e he'

/-- If every edge weight is at least one and the maximum Rayleigh quotient is below two,
the support is acyclic. -/
theorem support_isAcyclic_of_maxRayleigh_lt_two
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hmax : maxRayleigh X.isHermitian < 2) : X.support.IsAcyclic := by
  exact support_isAcyclic_of_no_affine hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax)

omit [DecidableEq ι] [Nonempty ι] in
/-- A connected support with weights at least one and no affine obstruction has a finite Dynkin
support labelling. -/
theorem dynkin_support_of_no_affine (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hno : ¬ X.ContainsAffineObstruction) :
    Nonempty (pathGraph (Fintype.card ι) ≃g X.support) ∨
      (∃ c, 0 < c ∧ Nonempty (armTree ![1, 1, c] ≃g X.support)) ∨
      Nonempty (armTree ![1, 2, 2] ≃g X.support) ∨
      Nonempty (armTree ![1, 2, 3] ≃g X.support) ∨
      Nonempty (armTree ![1, 2, 4] ≃g X.support) := by
  classical
  apply dynkin_labelling_of_no_affine hconn (support_isAcyclic_of_no_affine hweights hno)
  · intro ℓ hℓ ⟨e⟩
    have hc := (X.unit_contains_iff_support_embedding hweights (smithD ℓ) e.toEmbedding).mpr
      (fun _ _ h => e.toHom.map_adj h)
    rw [← affineD_eq_unit] at hc
    exact not_contains_of_no_affine hno
      (.d ℓ hℓ (Equiv.refl _) rfl) e.toEmbedding hc
  · rintro ⟨e⟩
    exact not_contains_of_no_affine hno (.e₆ (Equiv.refl _) rfl) e.toEmbedding
      ((X.unit_contains_iff_support_embedding hweights smithE₆ e.toEmbedding).mpr
        (fun _ _ h => e.toHom.map_adj h))
  · rintro ⟨e⟩
    exact not_contains_of_no_affine hno (.e₇ (Equiv.refl _) rfl) e.toEmbedding
      ((X.unit_contains_iff_support_embedding hweights smithE₇ e.toEmbedding).mpr
        (fun _ _ h => e.toHom.map_adj h))
  · rintro ⟨e⟩
    exact not_contains_of_no_affine hno (.e₈ (Equiv.refl _) rfl) e.toEmbedding
      ((X.unit_contains_iff_support_embedding hweights smithE₈ e.toEmbedding).mpr
        (fun _ _ h => e.toHom.map_adj h))

/-- The support-recognition step of the weighted dichotomy below eigenvalue two. -/
theorem dynkin_support_of_maxRayleigh_lt_two (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hmax : maxRayleigh X.isHermitian < 2) :
    Nonempty (pathGraph (Fintype.card ι) ≃g X.support) ∨
      (∃ c, 0 < c ∧ Nonempty (armTree ![1, 1, c] ≃g X.support)) ∨
      Nonempty (armTree ![1, 2, 2] ≃g X.support) ∨
      Nonempty (armTree ![1, 2, 3] ≃g X.support) ∨
      Nonempty (armTree ![1, 2, 4] ≃g X.support) := by
  exact dynkin_support_of_no_affine hconn hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax)

end WeightedGraph

namespace Matrix.IsFiniteCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {M : Matrix ι ι ℤ}

omit [Nonempty ι] in
/-- Every edge of a finite Cartan weighted support has weight at least one. -/
theorem one_le_weight (hM : M.IsFiniteCartan) {i j : ι}
    (hij : hM.weightedGraph.support.Adj i j) : 1 ≤ hM.weightedGraph.weights i j := by
  rcases hM.weightedGraph_weight_mem hij with h | h | h <;> rw [h] <;> norm_num

/-- A finite Cartan matrix has acyclic support. -/
theorem support_isAcyclic (hM : M.IsFiniteCartan) : hM.weightedGraph.support.IsAcyclic :=
  WeightedGraph.support_isAcyclic_of_maxRayleigh_lt_two
    (fun _ _ h => hM.one_le_weight h) hM.maxRayleigh_weightedGraph_lt_two

/-- A nonempty indecomposable finite Cartan matrix has one of the finite Dynkin support shapes. -/
theorem dynkin_support (hM : M.IsFiniteCartan) (hind : M.IsIndecomposable) :
    Nonempty (SimpleGraph.pathGraph (Fintype.card ι) ≃g hM.weightedGraph.support) ∨
      (∃ c, 0 < c ∧ Nonempty (SimpleGraph.armTree ![1, 1, c] ≃g hM.weightedGraph.support)) ∨
      Nonempty (SimpleGraph.armTree ![1, 2, 2] ≃g hM.weightedGraph.support) ∨
      Nonempty (SimpleGraph.armTree ![1, 2, 3] ≃g hM.weightedGraph.support) ∨
      Nonempty (SimpleGraph.armTree ![1, 2, 4] ≃g hM.weightedGraph.support) := by
  apply WeightedGraph.dynkin_support_of_maxRayleigh_lt_two _
    (fun _ _ h => hM.one_le_weight h) hM.maxRayleigh_weightedGraph_lt_two
  rw [hM.weightedGraph_support]
  exact (Matrix.isIndecomposable_iff_connected_support M hM.zero_comm).mp hind

end Matrix.IsFiniteCartan
