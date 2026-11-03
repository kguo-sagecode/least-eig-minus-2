/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.ObstructionFree

/-!
# Weighted path obstructions

Specified interval embeddings for the endpoint-weighted and middle-weighted
affine paths in the weighted dichotomy.
-/

namespace WeightedGraph

open Matrix

variable {ι : Type*} (X : WeightedGraph ι)

/-- Consecutive edge inequalities suffice to contain a specified weighted path. -/
theorem contains_path_of_consecutive {m : ℕ} (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (e : Fin m ↪ ι)
    (hedges : ∀ i (hi : i + 1 < m),
      w i ≤ X.weights (e ⟨i, by omega⟩) (e ⟨i + 1, hi⟩)) : X.Contains (path m w hw) e := by
  intro i j
  change (if i.val + 1 = j.val then w i.val
    else if j.val + 1 = i.val then w j.val else 0) ≤ _
  split_ifs with hij hji
  · have hj : j = ⟨i.val + 1, by omega⟩ := Fin.ext hij.symm
    rw [hj]
    exact hedges i.val (by omega)
  · have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext hji.symm
    rw [hi, X.symmetric.apply]
    exact hedges j.val (by omega)
  · exact X.nonneg _ _

/-- The order-preserving inclusion of a consecutive interval of vertices. -/
def intervalEmbedding (n offset m : ℕ) (hm : offset + m ≤ n) : Fin m ↪ Fin n where
  toFun i := ⟨offset + i.val, by omega⟩
  inj' i j h := Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)

variable {n : ℕ} (Y : WeightedGraph (Fin n))

/-- Two edges of weight at least √2 contain an endpoint-weighted affine interval. -/
theorem contains_endPath_of_two_heavy_edges
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    {a b : ℕ} (hab : a < b) (hb : b + 1 < n)
    (haweight : Real.sqrt 2 ≤ Y.weights ⟨a, by omega⟩ ⟨a + 1, by omega⟩)
    (hbweight : Real.sqrt 2 ≤ Y.weights ⟨b, by omega⟩ ⟨b + 1, hb⟩) :
    ∃ e : Fin (b - a + 2) ↪ Fin n, Y.Contains (endPath (b - a + 2)) e := by
  let e := intervalEmbedding n a (b - a + 2) (by omega)
  refine ⟨e, ?_⟩
  apply contains_path_of_consecutive
  intro i hi
  change (if i = 0 ∨ i + 2 = b - a + 2 then Real.sqrt 2 else 1) ≤
    Y.weights ⟨a + i, by omega⟩ ⟨a + (i + 1), by omega⟩
  by_cases hi0 : i = 0
  · subst i
    simpa using haweight
  by_cases hilast : i + 2 = b - a + 2
  · have hi' : a + i = b := by omega
    simpa [hi', hilast, ← Nat.add_assoc] using hbweight
  · simp only [hi0, hilast, or_self, ite_false]
    simpa only [Nat.add_assoc] using
      hunit (a + i) (by omega)

/-- A heavy edge with two edges to its left and one to its right contains the middle obstruction. -/
theorem contains_middlePath_of_heavy_interior
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    {k : ℕ} (hk : 2 ≤ k) (hkn : k + 2 < n)
    (hweight : Real.sqrt 2 ≤ Y.weights ⟨k, by omega⟩ ⟨k + 1, by omega⟩) :
    ∃ e : Fin 5 ↪ Fin n, Y.Contains middlePath e := by
  let e := intervalEmbedding n (k - 2) 5 (by omega)
  refine ⟨e, ?_⟩
  apply contains_path_of_consecutive
  intro i hi
  change (if i = 2 then Real.sqrt 2 else 1) ≤
    Y.weights ⟨k - 2 + i, by omega⟩ ⟨k - 2 + (i + 1), by omega⟩
  by_cases hi2 : i = 2
  · subst i
    have hk2 : k - 2 + 2 = k := by omega
    have hk3 : k - 2 + 3 = k + 1 := by omega
    simpa [hk2, hk3] using hweight
  · simp only [hi2, ite_false]
    simpa only [Nat.add_assoc] using
      hunit (k - 2 + i) (by omega)

/-- The reverse five-vertex interval handles a heavy second edge. -/
theorem contains_middlePath_of_heavy_second
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    (hn : 5 ≤ n)
    (hweight : Real.sqrt 2 ≤ Y.weights ⟨1, by omega⟩ ⟨2, by omega⟩) :
    ∃ e : Fin 5 ↪ Fin n, Y.Contains middlePath e := by
  let e : Fin 5 ↪ Fin n := Fin.revPerm.toEmbedding.trans (Fin.castLEEmb hn)
  refine ⟨e, ?_⟩
  apply contains_path_of_consecutive
  intro i hi
  have hi' : i ≤ 3 := by change i + 1 < 5 at hi; omega
  interval_cases i
  · change 1 ≤ Y.weights ⟨4, by omega⟩ ⟨3, by omega⟩
    rw [Y.symmetric.apply ⟨3, by omega⟩ ⟨4, by omega⟩]
    exact hunit 3 (by omega)
  · change 1 ≤ Y.weights ⟨3, by omega⟩ ⟨2, by omega⟩
    rw [Y.symmetric.apply ⟨2, by omega⟩ ⟨3, by omega⟩]
    exact hunit 2 (by omega)
  · change Real.sqrt 2 ≤ Y.weights ⟨2, by omega⟩ ⟨1, by omega⟩
    rw [Y.symmetric.apply ⟨1, by omega⟩ ⟨2, by omega⟩]
    exact hweight
  · change 1 ≤ Y.weights ⟨1, by omega⟩ ⟨0, by omega⟩
    rw [Y.symmetric.apply ⟨0, by omega⟩ ⟨1, by omega⟩]
    exact hunit 0 (by omega)

variable [Nonempty (Fin n)]

omit [Nonempty (Fin n)] in
/-- A path without affine obstructions has at most one edge of weight at least √2. -/
theorem heavy_edge_unique_of_no_affine
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    (hno : ¬ Y.ContainsAffineObstruction)
    {a b : ℕ} (ha : a + 1 < n) (hb : b + 1 < n)
    (haweight : Real.sqrt 2 ≤ Y.weights ⟨a, by omega⟩ ⟨a + 1, ha⟩)
    (hbweight : Real.sqrt 2 ≤ Y.weights ⟨b, by omega⟩ ⟨b + 1, hb⟩) : a = b := by
  suffices hle : ∀ a b (hab : a < b) (hb : b + 1 < n),
      Real.sqrt 2 ≤ Y.weights ⟨a, by omega⟩ ⟨a + 1, by omega⟩ →
      Real.sqrt 2 ≤ Y.weights ⟨b, by omega⟩ ⟨b + 1, hb⟩ → False by
    rcases lt_trichotomy a b with h | h | h
    · exact (hle a b h hb haweight hbweight).elim
    · exact h
    · exact (hle b a h ha hbweight haweight).elim
  intro a b hab hb haweight hbweight
  obtain ⟨e, he⟩ := Y.contains_endPath_of_two_heavy_edges hunit hab hb haweight hbweight
  have : Nonempty (Fin (b - a + 2)) := ⟨⟨0, by omega⟩⟩
  exact not_contains_of_no_affine hno
    (.ends (b - a + 2) (by omega) (Equiv.refl _) rfl) e he

/-- Below the affine threshold, a path has at most one edge of weight at least √2. -/
theorem heavy_edge_unique_of_maxRayleigh_lt_two
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    (hmax : maxRayleigh Y.isHermitian < 2)
    {a b : ℕ} (ha : a + 1 < n) (hb : b + 1 < n)
    (haweight : Real.sqrt 2 ≤ Y.weights ⟨a, by omega⟩ ⟨a + 1, ha⟩)
    (hbweight : Real.sqrt 2 ≤ Y.weights ⟨b, by omega⟩ ⟨b + 1, hb⟩) : a = b := by
  exact heavy_edge_unique_of_no_affine Y hunit
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax) ha hb haweight hbweight

omit [Nonempty (Fin n)] in
/-- A heavy edge without affine obstructions is terminal or the middle edge on four vertices. -/
theorem heavy_edge_position_of_no_affine
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    (hno : ¬ Y.ContainsAffineObstruction)
    {k : ℕ} (hk : k + 1 < n)
    (hweight : Real.sqrt 2 ≤ Y.weights ⟨k, by omega⟩ ⟨k + 1, hk⟩) :
    k = 0 ∨ k + 2 = n ∨ (n = 4 ∧ k = 1) := by
  by_contra h
  have hk0 : k ≠ 0 := fun hk0 => h (Or.inl hk0)
  have hkn : k + 2 < n := by omega
  have hn : 5 ≤ n := by omega
  have hcontains : ∃ e : Fin 5 ↪ Fin n, Y.Contains middlePath e := by
    by_cases hk2 : 2 ≤ k
    · exact Y.contains_middlePath_of_heavy_interior hunit hk2 hkn hweight
    · have hk1 : k = 1 := by omega
      subst k
      exact Y.contains_middlePath_of_heavy_second hunit hn hweight
  obtain ⟨e, he⟩ := hcontains
  exact not_contains_of_no_affine hno (.middle (Equiv.refl _) rfl) e he

/-- Below the affine threshold a heavy path edge is terminal,
or is the middle edge on four vertices. -/
theorem heavy_edge_position_of_maxRayleigh_lt_two
    (hunit : ∀ i (hi : i + 1 < n),
      1 ≤ Y.weights ⟨i, by omega⟩ ⟨i + 1, hi⟩)
    (hmax : maxRayleigh Y.isHermitian < 2)
    {k : ℕ} (hk : k + 1 < n)
    (hweight : Real.sqrt 2 ≤ Y.weights ⟨k, by omega⟩ ⟨k + 1, hk⟩) :
    k = 0 ∨ k + 2 = n ∨ (n = 4 ∧ k = 1) := by
  exact heavy_edge_position_of_no_affine Y hunit
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax) hk hweight

end WeightedGraph
