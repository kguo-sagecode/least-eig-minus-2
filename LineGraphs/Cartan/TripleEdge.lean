/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.ObstructionFree

/-!
# The triple-edge case of the weighted dichotomy

A √3 edge cannot be extended by a further edge below the affine threshold.
-/

namespace WeightedGraph

open Matrix

variable {ι : Type*} (X : WeightedGraph ι)

/-- A √3 edge followed by a unit-or-larger edge contains the triple-path obstruction. -/
theorem contains_triplePath_of_two_edges {u v w : ι}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hfirst : Real.sqrt 3 ≤ X.weights u v) (hsecond : 1 ≤ X.weights v w) :
    ∃ e : Fin 3 ↪ ι, X.Contains triplePath e := by
  let f : Fin 3 → ι := ![u, v, w]
  have hinj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨f, hinj⟩, ?_⟩
  have hfirst' : Real.sqrt 3 ≤ X.weights v u := by rwa [X.symmetric.apply u v]
  have hsecond' : 1 ≤ X.weights w v := by rwa [X.symmetric.apply v w]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triplePath, path, f, X.diag] <;>
    first | exact hfirst | exact hfirst' | exact hsecond | exact hsecond' | exact X.nonneg _ _

variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Without affine obstructions, the endpoints of a heavy triple edge exhaust a connected
support. -/
theorem eq_or_eq_of_sqrt_three_le_weight_of_no_affine (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hno : ¬ X.ContainsAffineObstruction) {u v : ι}
    (huv : Real.sqrt 3 ≤ X.weights u v) : ∀ z, z = u ∨ z = v := by
  classical
  have huvpos : 0 < X.weights u v := lt_of_lt_of_le (by positivity) huv
  have huvadj : X.support.Adj u v := huvpos
  have hvu : Real.sqrt 3 ≤ X.weights v u := by rwa [X.symmetric.apply u v]
  have hneighbor {a b : ι} (hab : Real.sqrt 3 ≤ X.weights a b)
      (hne : a ≠ b) {z : ι} (hbz : X.support.Adj b z) : z = a := by
    by_contra hza
    have haz : a ≠ z := fun h => hza h.symm
    obtain ⟨e, he⟩ := X.contains_triplePath_of_two_edges hne haz hbz.ne hab
      (hweights _ _ hbz)
    exact not_contains_of_no_affine hno (.triple (Equiv.refl _) rfl) e he
  have hstep {x y : ι} (hxy : X.support.Adj x y) : (x = u ∨ x = v) = (y = u ∨ y = v) := by
    apply propext
    constructor
    · rintro (rfl | rfl)
      · right
        exact hneighbor hvu huvadj.ne.symm hxy
      · left
        exact hneighbor huv huvadj.ne hxy
    · rintro (rfl | rfl)
      · right
        exact hneighbor hvu huvadj.ne.symm hxy.symm
      · left
        exact hneighbor huv huvadj.ne hxy.symm
  intro z
  have heq := hconn.constant_of_edge_eq (f := fun z => z = u ∨ z = v)
    (fun {_ _} h => hstep h) u z
  exact heq ▸ Or.inl rfl

/-- In a connected graph with edge weights at least one and maximum Rayleigh value below two,
the endpoints of an edge of weight at least √3 are all the vertices. -/
theorem eq_or_eq_of_sqrt_three_le_weight (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hmax : maxRayleigh X.isHermitian < 2) {u v : ι}
    (huv : Real.sqrt 3 ≤ X.weights u v) : ∀ z, z = u ∨ z = v := by
  exact eq_or_eq_of_sqrt_three_le_weight_of_no_affine X hconn hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax) huv

/-- The weighted Dynkin G₂ graph consists of one √3 edge. -/
noncomputable def tripleEdge : WeightedGraph (Fin 2) :=
  path 2 (fun _ => Real.sqrt 3) (fun _ => Real.sqrt_nonneg _)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A triple edge in an affine-obstruction-free connected graph gives the weighted G₂ labelling. -/
theorem eq_tripleEdge_reindex_of_weight_eq_sqrt_three_of_no_affine (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hno : ¬ X.ContainsAffineObstruction) {u v : ι}
    (huv : X.weights u v = Real.sqrt 3) :
    ∃ e : Fin 2 ≃ ι, X = tripleEdge.reindex e := by
  classical
  have hall := X.eq_or_eq_of_sqrt_three_le_weight_of_no_affine hconn hweights hno huv.ge
  have hne : u ≠ v := by
    intro h
    subst v
    have hpos : (0 : ℝ) < Real.sqrt 3 := by positivity
    rw [X.diag] at huv
    exact hpos.ne huv
  let f : Fin 2 → ι := ![u, v]
  have hinj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hsurj : Function.Surjective f := by
    intro z
    rcases hall z with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  let e : Fin 2 ≃ ι := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  apply ext
  funext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  simp only [reindex, Matrix.reindex_apply, submatrix_apply, e.symm_apply_apply]
  have hvu : X.weights v u = Real.sqrt 3 := (X.symmetric.apply u v).trans huv
  change X.weights (f i) (f j) = tripleEdge.weights i j
  fin_cases i <;> fin_cases j <;> simp [f, tripleEdge, path, X.diag, huv, hvu]

/-- A √3 edge determines the entire weighted graph below the affine threshold. -/
theorem eq_tripleEdge_reindex_of_weight_eq_sqrt_three (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j → 1 ≤ X.weights i j)
    (hmax : maxRayleigh X.isHermitian < 2) {u v : ι}
    (huv : X.weights u v = Real.sqrt 3) :
    ∃ e : Fin 2 ≃ ι, X = tripleEdge.reindex e := by
  exact eq_tripleEdge_reindex_of_weight_eq_sqrt_three_of_no_affine X hconn hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax) huv

end WeightedGraph
