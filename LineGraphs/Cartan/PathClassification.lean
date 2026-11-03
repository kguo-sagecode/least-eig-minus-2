/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.WeightedPaths
import LineGraphs.Cartan.TripleEdge

/-!
# Classification of weighted paths below two

The path case of the weighted dichotomy, with the location of the exceptional
edge retained. Reversal of terminal edges is deferred to matrix orientation.
-/

namespace WeightedGraph

open Matrix SimpleGraph

variable {n : ℕ} (Y : WeightedGraph (Fin n))

/-- The support and consecutive entries determine a weighted path completely. -/
theorem eq_path_of_consecutive (hsupport : Y.support = pathGraph n)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hedges : ∀ i (hi : i + 1 < n), Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩ = w i) :
    Y = path n w hw := by
  apply ext
  funext i j
  change Y.weights i j = if i.val + 1 = j.val then w i.val
    else if j.val + 1 = i.val then w j.val else 0
  split_ifs with hij hji
  · have hj : j = ⟨i.val + 1, by omega⟩ := Fin.ext hij.symm
    rw [hj]
    exact hedges i.val (by omega)
  · have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext hji.symm
    rw [hi, Y.symmetric.apply]
    exact hedges j.val (by omega)
  · apply le_antisymm
    · apply le_of_not_gt
      intro h
      have hadj : Y.support.Adj i j := h
      rw [hsupport, pathGraph_adj] at hadj
      exact hadj.elim hij hji
    · exact Y.nonneg _ _

/-- A path with exactly one designated √2 edge and all other weights one. -/
noncomputable def singleDoublePath (n k : ℕ) : WeightedGraph (Fin n) :=
  path n (fun i => if i = k then Real.sqrt 2 else 1)
    (by intro i; split_ifs <;> positivity)

variable [Nonempty (Fin n)]

/-- A Cartan-weighted path without affine obstructions has a finite Dynkin weighted labelling. -/
theorem path_classification_of_no_affine (hsupport : Y.support = pathGraph n)
    (hweights : ∀ i j, Y.support.Adj i j →
      Y.weights i j = 1 ∨ Y.weights i j = Real.sqrt 2 ∨ Y.weights i j = Real.sqrt 3)
    (hno : ¬ Y.ContainsAffineObstruction) :
    Y = path n (fun _ => 1) (by intro _; norm_num) ∨
      (∃ k, k + 1 < n ∧ (k = 0 ∨ k + 2 = n ∨ (n = 4 ∧ k = 1)) ∧
        Y = singleDoublePath n k) ∨
      ∃ e : Fin 2 ≃ Fin n, Y = tripleEdge.reindex e := by
  have hconn : Y.support.Connected := by
    rw [hsupport]
    exact ⟨pathGraph_preconnected n⟩
  have hunit (i j) (hij : Y.support.Adj i j) : 1 ≤ Y.weights i j := by
    rcases hweights i j hij with h | h | h <;> rw [h] <;> norm_num
  by_cases htriple : ∃ u v, Y.weights u v = Real.sqrt 3
  · obtain ⟨u, v, huv⟩ := htriple
    exact Or.inr (Or.inr
      (Y.eq_tripleEdge_reindex_of_weight_eq_sqrt_three_of_no_affine hconn hunit hno huv))
  have hadj (i : ℕ) (hi : i + 1 < n) :
      Y.support.Adj ⟨i, by omega⟩ ⟨i + 1, hi⟩ := by
    rw [hsupport, pathGraph_adj]
    exact Or.inl rfl
  have hunit' (i : ℕ) (hi : i + 1 < n) :
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩ := hunit _ _ (hadj i hi)
  have hcases (i : ℕ) (hi : i + 1 < n) :
      Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩ = 1 ∨
      Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩ = Real.sqrt 2 := by
    rcases hweights _ _ (hadj i hi) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (htriple ⟨_, _, h⟩).elim
  by_cases hdouble : ∃ (k : ℕ) (hk : k + 1 < n),
      Y.weights ⟨k, by omega⟩ ⟨k + 1, hk⟩ = Real.sqrt 2
  · obtain ⟨k, hk, hkw⟩ := hdouble
    have hposition := Y.heavy_edge_position_of_no_affine hunit' hno hk hkw.ge
    refine Or.inr (Or.inl ⟨k, hk, hposition, ?_⟩)
    apply eq_path_of_consecutive Y hsupport
    intro i hi
    by_cases hik : i = k
    · subst i
      simpa using hkw
    · simp only [hik, ite_false]
      rcases hcases i hi with h | h
      · exact h
      · exact (hik (Y.heavy_edge_unique_of_no_affine hunit' hno hi hk h.ge hkw.ge)).elim
  · left
    apply eq_path_of_consecutive Y hsupport
    intro i hi
    rcases hcases i hi with h | h
    · exact h
    · exact (hdouble ⟨i, hi, h⟩).elim

/-- A Cartan-weighted path below the affine threshold is a unit path, a path with
one permitted √2 edge, or the two-vertex √3 model. -/
theorem path_classification_of_maxRayleigh_lt_two (hsupport : Y.support = pathGraph n)
    (hweights : ∀ i j, Y.support.Adj i j →
      Y.weights i j = 1 ∨ Y.weights i j = Real.sqrt 2 ∨ Y.weights i j = Real.sqrt 3)
    (hmax : maxRayleigh Y.isHermitian < 2) :
    Y = path n (fun _ => 1) (by intro _; norm_num) ∨
      (∃ k, k + 1 < n ∧ (k = 0 ∨ k + 2 = n ∨ (n = 4 ∧ k = 1)) ∧
        Y = singleDoublePath n k) ∨
      ∃ e : Fin 2 ≃ Fin n, Y = tripleEdge.reindex e := by
  exact path_classification_of_no_affine Y hsupport hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax)

end WeightedGraph
