/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.PathClassification
import LineGraphs.Cartan.WeightedArms

/-!
# Weighted Dynkin recognition below two

The recognition direction needed by Theorem A, before identifying the integer
orientations with Mathlib's named matrices. The double-path constructor retains
the terminal orientation and includes the four-vertex middle-edge case.
-/

namespace WeightedGraph

open Matrix SimpleGraph

variable {ι κ ν : Type*}

/-- Reindexing along an equivalence and then its inverse returns the original graph. -/
@[simp]
theorem reindex_symm_cancel (X : WeightedGraph ι) (e : ι ≃ κ) :
    (X.reindex e).reindex e.symm = X := by
  apply ext
  funext i j
  simp [reindex, Matrix.reindex_apply]

/-- Composition of equivalences composes weighted reindexings. -/
theorem reindex_trans (X : WeightedGraph ι) (e : ι ≃ κ) (f : κ ≃ ν) :
    (X.reindex e).reindex f = X.reindex (e.trans f) := by
  apply ext
  rfl

/-- A weight-preserving labelling by a finite Dynkin weighted graph. -/
inductive HasDynkinLabelling (X : WeightedGraph ι) : Prop
  | a (n : ℕ) (hn : 0 < n) (e : Fin n ≃ ι)
      (h : X = (path n (fun _ => 1) (by intro _; norm_num)).reindex e) : HasDynkinLabelling X
  | doublePath (n k : ℕ) (hk : k + 1 < n)
      (hposition : k = 0 ∨ k + 2 = n ∨ (n = 4 ∧ k = 1)) (e : Fin n ≃ ι)
      (h : X = (singleDoublePath n k).reindex e) : HasDynkinLabelling X
  | d (c : ℕ) (hc : 0 < c) (e : ArmVertex ![1, 1, c] ≃ ι)
      (h : X = (unit (armTree ![1, 1, c])).reindex e) : HasDynkinLabelling X
  | e₆ (e : ArmVertex ![1, 2, 2] ≃ ι)
      (h : X = (unit (armTree ![1, 2, 2])).reindex e) : HasDynkinLabelling X
  | e₇ (e : ArmVertex ![1, 2, 3] ≃ ι)
      (h : X = (unit (armTree ![1, 2, 3])).reindex e) : HasDynkinLabelling X
  | e₈ (e : ArmVertex ![1, 2, 4] ≃ ι)
      (h : X = (unit (armTree ![1, 2, 4])).reindex e) : HasDynkinLabelling X
  | g₂ (e : Fin 2 ≃ ι) (h : X = tripleEdge.reindex e) : HasDynkinLabelling X

variable [Fintype ι] [DecidableEq ι] [Nonempty ι] {X : WeightedGraph ι}

omit [Fintype ι] [DecidableEq ι] in
/-- A connected graph with Cartan weights and no affine obstruction has a finite Dynkin weighted
labelling. -/
theorem dynkin_labelling_of_no_affine [Finite ι] (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j →
      X.weights i j = 1 ∨ X.weights i j = Real.sqrt 2 ∨ X.weights i j = Real.sqrt 3)
    (hno : ¬ X.ContainsAffineObstruction) : X.HasDynkinLabelling := by
  classical
  let _ := Fintype.ofFinite ι
  have hunit (i j) (hij : X.support.Adj i j) : 1 ≤ X.weights i j := by
    rcases hweights i j hij with h | h | h <;> rw [h] <;> norm_num
  have harm {a : Fin 3 → ℕ} (hpos : ∀ r, 0 < a r)
      (e : armTree a ≃g X.support) : X = (unit (armTree a)).reindex e.toEquiv := by
    let Y := X.reindex e.toEquiv.symm
    have hs : Y.support = armTree a := by
      ext i j
      change X.support.Adj (e i) (e j) ↔ (armTree a).Adj i j
      exact e.map_rel_iff
    have hm : ¬ Y.ContainsAffineObstruction :=
      not_containsAffineObstruction_reindex hno e.toEquiv.symm
    have heq := Y.eq_unit_of_arm_support_of_no_affine hpos hs
      (fun i j h => hweights (e i) (e j) h) hm
    have hcancel : Y.reindex e.toEquiv = X := reindex_symm_cancel X e.toEquiv.symm
    exact hcancel.symm.trans (congrArg (fun Z => Z.reindex e.toEquiv) heq)
  rcases dynkin_support_of_no_affine hconn hunit hno with
    he | he | he | he | he
  · obtain ⟨e⟩ := he
    let Y := X.reindex e.toEquiv.symm
    have hs : Y.support = pathGraph (Fintype.card ι) := by
      ext i j
      change X.support.Adj (e i) (e j) ↔ _
      exact e.map_rel_iff
    have : Nonempty (Fin (Fintype.card ι)) := ⟨⟨0, Fintype.card_pos⟩⟩
    have hm : ¬ Y.ContainsAffineObstruction :=
      not_containsAffineObstruction_reindex hno e.toEquiv.symm
    have hcancel : Y.reindex e.toEquiv = X := reindex_symm_cancel X e.toEquiv.symm
    rcases Y.path_classification_of_no_affine hs
      (fun i j h => hweights (e i) (e j) h) hm with heq | ⟨k, hk, hposition, heq⟩ | ⟨f, heq⟩
    · exact .a _ Fintype.card_pos e.toEquiv
        (hcancel.symm.trans (congrArg (fun Z => Z.reindex e.toEquiv) heq))
    · exact .doublePath _ k hk hposition e.toEquiv
        (hcancel.symm.trans (congrArg (fun Z => Z.reindex e.toEquiv) heq))
    · exact .g₂ (f.trans e.toEquiv)
        ((hcancel.symm.trans (congrArg (fun Z => Z.reindex e.toEquiv) heq)).trans
          (reindex_trans tripleEdge f e.toEquiv))
  · obtain ⟨c, hc, ⟨e⟩⟩ := he
    exact .d c hc e.toEquiv (harm (a := ![1, 1, c]) (by intro r; fin_cases r <;> simp_all) e)
  · obtain ⟨e⟩ := he
    exact .e₆ e.toEquiv (harm (a := ![1, 2, 2]) (by intro r; fin_cases r <;> norm_num) e)
  · obtain ⟨e⟩ := he
    exact .e₇ e.toEquiv (harm (a := ![1, 2, 3]) (by intro r; fin_cases r <;> norm_num) e)
  · obtain ⟨e⟩ := he
    exact .e₈ e.toEquiv (harm (a := ![1, 2, 4]) (by intro r; fin_cases r <;> norm_num) e)

/-- Every connected graph with Cartan edge weights and maximum Rayleigh value below two
has a weight-preserving finite Dynkin labelling. -/
theorem dynkin_labelling_of_maxRayleigh_lt_two (hconn : X.support.Connected)
    (hweights : ∀ i j, X.support.Adj i j →
      X.weights i j = 1 ∨ X.weights i j = Real.sqrt 2 ∨ X.weights i j = Real.sqrt 3)
    (hmax : maxRayleigh X.isHermitian < 2) : X.HasDynkinLabelling := by
  exact dynkin_labelling_of_no_affine hconn hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax)

end WeightedGraph

namespace Matrix.IsFiniteCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {M : Matrix ι ι ℤ}

/-- The weighted graph of a nonempty indecomposable finite Cartan matrix has a finite
Dynkin labelling. Integer orientation and named-matrix recognition are separate remaining steps. -/
theorem weighted_classification (hM : M.IsFiniteCartan) (hind : M.IsIndecomposable) :
    hM.weightedGraph.HasDynkinLabelling := by
  apply WeightedGraph.dynkin_labelling_of_maxRayleigh_lt_two _
    (fun _ _ h => hM.weightedGraph_weight_mem h) hM.maxRayleigh_weightedGraph_lt_two
  rw [hM.weightedGraph_support]
  exact (Matrix.isIndecomposable_iff_connected_support M hM.zero_comm).mp hind

end Matrix.IsFiniteCartan
