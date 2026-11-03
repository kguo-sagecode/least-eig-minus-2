/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.LabelledGraphs

/-!
# Attaching leaves

A uniform construction for the affine D and weighted-fork obstruction families.
-/

namespace WeightedGraph

variable {ι κ : Type*} [DecidableEq ι]

/-- Attach each new leaf `j` to `a j` by an edge of weight `w j`. -/
def attachLeaves (X : WeightedGraph ι) (a : κ → ι) (w : κ → ℝ)
    (hw : ∀ j, 0 ≤ w j) : WeightedGraph (ι ⊕ κ) where
  weights
    | .inl i, .inl j => X.weights i j
    | .inl i, .inr j => if i = a j then w j else 0
    | .inr i, .inl j => if j = a i then w i else 0
    | .inr _, .inr _ => 0
  symmetric := by
    apply Matrix.IsSymm.ext
    rintro (i | i) (j | j)
    · exact X.symmetric.apply i j
    all_goals rfl
  nonneg := by
    rintro (i | i) (j | j)
    · exact X.nonneg _ _
    · dsimp only
      split_ifs <;> first | exact hw _ | exact le_rfl
    · dsimp only
      split_ifs <;> first | exact hw _ | exact le_rfl
    · exact le_rfl
  diag := by
    rintro (i | i)
    · exact X.diag i
    · rfl

/-- Attaching positive-weight leaves to a connected graph preserves connectedness. -/
theorem attachLeaves_connected (X : WeightedGraph ι) (hX : X.support.Connected)
    (a : κ → ι) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) (hpos : ∀ j, 0 < w j) :
    (X.attachLeaves a w hw).support.Connected := by
  obtain ⟨i₀⟩ := hX.nonempty
  let f : X.support →g (X.attachLeaves a w hw).support :=
    { toFun := Sum.inl, map_rel' := fun h => h }
  apply ((X.attachLeaves a w hw).support.connected_iff_exists_forall_reachable).mpr
  refine ⟨Sum.inl i₀, ?_⟩
  rintro (i | j)
  · exact (hX i₀ i).map f
  · apply ((hX i₀ (a j)).map f).trans
    apply SimpleGraph.Adj.reachable
    change 0 < if a j = a j then w j else 0
    simpa only [ite_true] using hpos j

open Matrix in
/-- At an old vertex, the new leaves contribute their weighted coordinate sum. -/
theorem attachLeaves_mulVec_inl [Fintype ι] [Fintype κ]
    (X : WeightedGraph ι) (a : κ → ι) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (x : ι → ℝ) (y : κ → ℝ) (i : ι) :
    ((X.attachLeaves a w hw).weights *ᵥ Sum.elim x y) (Sum.inl i) =
      (X.weights *ᵥ x) i + ∑ j, if i = a j then w j * y j else 0 := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, attachLeaves, Sum.elim_inl,
    Sum.elim_inr, ite_mul, zero_mul]

open Matrix in
/-- At a new leaf, the only contribution is its old neighbour. -/
theorem attachLeaves_mulVec_inr [Fintype ι] [Fintype κ]
    (X : WeightedGraph ι) (a : κ → ι) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (x : ι → ℝ) (y : κ → ℝ) (j : κ) :
    ((X.attachLeaves a w hw).weights *ᵥ Sum.elim x y) (Sum.inr j) = w j * x (a j) := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, attachLeaves, Sum.elim_inl,
    Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, ite_mul]
  simp

end WeightedGraph
