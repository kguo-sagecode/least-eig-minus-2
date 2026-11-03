/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.WeightedClassification

/-!
# Spectral certificates for finite weighted Dynkin graphs

Proper containment in connected affine obstructions proves the strict bound two.
-/

namespace WeightedGraph

open Matrix SimpleGraph

private theorem path_weights_succ (n : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (i : ℕ) (hi : i + 1 < n) :
    (path n w hw).weights ⟨i, by omega⟩ ⟨i + 1, hi⟩ = w i := by
  simp [path]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [Nonempty ι] [Nonempty κ] {X : WeightedGraph ι} {Y : WeightedGraph κ}

/-- A smaller weighted graph contained in an affine obstruction
has maximum Rayleigh value below two. -/
theorem maxRayleigh_lt_two_of_contains_affine (hY : Y.IsAffineObstruction)
    {e : ι ↪ κ} (he : Y.Contains X e) (hcard : Fintype.card ι < Fintype.card κ) :
    maxRayleigh X.isHermitian < 2 := by
  classical
  have hnot : ¬ Function.Surjective e := by
    intro hsurj
    exact (not_le_of_gt hcard) (Fintype.card_le_of_surjective e hsurj)
  have hlt := maxRayleigh_strictMono he hY.connected (Or.inl hnot)
  rwa [hY.maxRayleigh_eq_two] at hlt

/-- Every nonempty unit path has maximum Rayleigh value less than two. -/
theorem unit_path_maxRayleigh_lt_two (n : ℕ) [Nonempty (Fin n)] :
    maxRayleigh (path n (fun _ => 1) (by intro _; norm_num)).isHermitian < 2 := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  let e := Fin.castLEEmb (show n ≤ n + 2 by omega)
  apply maxRayleigh_lt_two_of_contains_affine
    (Y := endPath (n + 2)) (.ends (n + 2) (by omega) (Equiv.refl _) rfl)
    (e := e) _ (by simp)
  apply contains_path_of_consecutive
  intro i hi
  change 1 ≤ (endPath (n + 2)).weights ⟨i, by omega⟩ ⟨i + 1, by omega⟩
  rw [endPath, path_weights_succ]
  split_ifs <;> norm_num

/-- A terminal √2 edge is below the affine threshold in either orientation. -/
theorem terminal_double_path_maxRayleigh_lt_two (n k : ℕ) [Nonempty (Fin n)]
    (hk : k + 1 < n) (hterminal : k = 0 ∨ k + 2 = n) :
    maxRayleigh (singleDoublePath n k).isHermitian < 2 := by
  have : Nonempty (Fin (n + 1)) := inferInstance
  rcases hterminal with hfirst | hlast
  · let e := intervalEmbedding (n + 1) 0 n (by omega)
    apply maxRayleigh_lt_two_of_contains_affine
      (Y := endPath (n + 1)) (.ends (n + 1) (by omega) (Equiv.refl _) rfl)
      (e := e) _ (by simp)
    apply contains_path_of_consecutive
    intro i hi
    change (if i = k then Real.sqrt 2 else 1) ≤
      (endPath (n + 1)).weights ⟨0 + i, by omega⟩ ⟨0 + i + 1, by omega⟩
    simp only [Nat.zero_add]
    rw [endPath, path_weights_succ]
    subst k
    split_ifs <;> norm_num
    all_goals omega
  · let e := intervalEmbedding (n + 1) 1 n (by omega)
    apply maxRayleigh_lt_two_of_contains_affine
      (Y := endPath (n + 1)) (.ends (n + 1) (by omega) (Equiv.refl _) rfl)
      (e := e) _ (by simp)
    apply contains_path_of_consecutive
    intro i hi
    change (if i = k then Real.sqrt 2 else 1) ≤
      (endPath (n + 1)).weights ⟨1 + i, by omega⟩ ⟨1 + i + 1, by omega⟩
    rw [endPath, path_weights_succ]
    split_ifs <;> norm_num
    all_goals omega

/-- The finite F₄ weighted path is a proper interval of the middle affine obstruction. -/
theorem middle_double_path_maxRayleigh_lt_two :
    maxRayleigh (singleDoublePath 4 1).isHermitian < 2 := by
  let e := intervalEmbedding 5 1 4 (by omega)
  apply maxRayleigh_lt_two_of_contains_affine (Y := middlePath)
    (.middle (Equiv.refl _) rfl) (e := e) _ (by decide)
  apply contains_path_of_consecutive
  intro i hi
  change (if i = 1 then Real.sqrt 2 else 1) ≤
    middlePath.weights ⟨1 + i, by omega⟩ ⟨1 + i + 1, by omega⟩
  rw [middlePath, path_weights_succ]
  have heq : 1 + i = 2 ↔ i = 1 := by omega
  simp only [heq]
  exact le_rfl

/-- The finite G₂ weighted edge is a proper subgraph of the triple affine path. -/
theorem tripleEdge_maxRayleigh_lt_two : maxRayleigh tripleEdge.isHermitian < 2 := by
  let e := Fin.castLEEmb (show 2 ≤ 3 by omega)
  apply maxRayleigh_lt_two_of_contains_affine (Y := triplePath)
    (.triple (Equiv.refl _) rfl) (e := e) _ (by decide)
  apply contains_path_of_consecutive
  intro i hi
  have hi0 : i = 0 := by change i + 1 < 2 at hi; omega
  subst i
  change Real.sqrt 3 ≤ triplePath.weights 0 1
  norm_num [triplePath, path]

/-- Truncating an affine E arm tree proves the strict spectral bound for each finite E model. -/
theorem finiteE_maxRayleigh_lt_two :
    maxRayleigh (unit (armTree ![1, 2, 2])).isHermitian < 2 ∧
      maxRayleigh (unit (armTree ![1, 2, 3])).isHermitian < 2 ∧
      maxRayleigh (unit (armTree ![1, 2, 4])).isHermitian < 2 := by
  have hle {a b : Fin 3 → ℕ} (hab : ∀ r, a r ≤ b r)
      (hobs : (unit (armTree b)).IsAffineObstruction)
      (hcard : Fintype.card (ArmVertex a) < Fintype.card (ArmVertex b)) :
      maxRayleigh (unit (armTree a)).isHermitian < 2 := by
    apply maxRayleigh_lt_two_of_contains_affine hobs
      (e := (armTreeEmbedding hab).toEmbedding) _ hcard
    apply ((unit (armTree b)).unit_contains_iff_support_embedding _ (armTree a) _).mpr
    · intro i j hij
      rw [support_unit]
      change (armTree b).Adj ((armTreeEmbedding hab) i) ((armTreeEmbedding hab) j)
      exact (armTreeEmbedding hab).map_rel_iff.mpr hij
    · intro i j hij
      change 1 ≤ (if (armTree b).Adj i j then (1 : ℝ) else 0)
      have h : (armTree b).Adj i j := by simpa only [support_unit] using hij
      simp only [h, ite_true, le_refl]
  constructor
  · exact hle (a := ![1, 2, 2]) (b := ![2, 2, 2]) (by decide)
      (.e₆ (Equiv.refl _) rfl) (by decide)
  constructor
  · exact hle (a := ![1, 2, 3]) (b := ![1, 3, 3]) (by decide)
      (.e₇ (Equiv.refl _) rfl) (by decide)
  · exact hle (a := ![1, 2, 4]) (b := ![1, 2, 5]) (by decide)
      (.e₈ (Equiv.refl _) rfl) (by decide)

end WeightedGraph
