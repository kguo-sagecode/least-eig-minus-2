/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.WeightedPaths

/-!
# Heavy edges on three-arm trees

Truncating the arm at a heavy edge and the other arms at their first vertices
gives the weighted-fork obstruction.
-/

namespace SimpleGraph

/-- A position on an arm, with position zero denoting the common centre. -/
def armPathVertex (a : Fin 3 → ℕ) (r : Fin 3) (i : Fin (a r + 1)) : ArmVertex a :=
  if h : i.val = 0 then none else some ⟨r, ⟨i.val - 1, by omega⟩⟩

/-- The positions on a specified arm, including the centre, are distinct. -/
theorem armPathVertex_injective (a : Fin 3 → ℕ) (r : Fin 3) :
    Function.Injective (armPathVertex a r) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg (fun z : ArmVertex a => z.map (fun x => x.2.val)) h
  dsimp [armPathVertex] at h'
  split_ifs at h' <;> simp_all
  all_goals omega

/-- Consecutive positions on an arm are adjacent. -/
theorem armPathVertex_adj (a : Fin 3 → ℕ) (r : Fin 3) (i : ℕ) (hi : i < a r) :
    (armTree a).Adj (armPathVertex a r ⟨i, by omega⟩)
      (armPathVertex a r ⟨i + 1, by omega⟩) := by
  by_cases hi0 : i = 0
  · subst i
    simp [armPathVertex, armTree]
  · simp [armPathVertex, armTree, hi0]
    omega

/-- Successor positions are exactly the zero-based arm vertices. -/
@[simp]
theorem armPathVertex_succ (a : Fin 3 → ℕ) (r : Fin 3) (i : Fin (a r)) :
    armPathVertex a r ⟨i.val + 1, by omega⟩ = some ⟨r, i⟩ := by
  simp [armPathVertex]

/-- Each arm-tree edge is a consecutive pair on one of the centre-based arm paths. -/
theorem armTree_adj_exists_consecutive {a : Fin 3 → ℕ} {x y : ArmVertex a}
    (hxy : (armTree a).Adj x y) :
    ∃ (r : Fin 3) (k : ℕ) (hk : k < a r),
      (x = armPathVertex a r ⟨k, by omega⟩ ∧
        y = armPathVertex a r ⟨k + 1, by omega⟩) ∨
      (y = armPathVertex a r ⟨k, by omega⟩ ∧
        x = armPathVertex a r ⟨k + 1, by omega⟩) := by
  rcases x with _ | ⟨r, i⟩ <;> rcases y with _ | ⟨s, j⟩
  · exact hxy.elim
  · have hj : j.val = 0 := hxy
    refine ⟨s, 0, by omega, Or.inl ⟨rfl, ?_⟩⟩
    have h := armPathVertex_succ a s j
    simpa only [hj] using h.symm
  · have hi : i.val = 0 := hxy
    refine ⟨r, 0, by omega, Or.inr ⟨rfl, ?_⟩⟩
    have h := armPathVertex_succ a r i
    simpa only [hi] using h.symm
  · change r = s ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) at hxy
    obtain ⟨hrs, hxy⟩ := hxy
    subst s
    rcases hxy with hij | hji
    · refine ⟨r, i.val + 1, by omega, Or.inl ⟨(armPathVertex_succ a r i).symm, ?_⟩⟩
      have h := armPathVertex_succ a r j
      simpa only [← hij] using h.symm
    · refine ⟨r, j.val + 1, by omega, Or.inr ⟨(armPathVertex_succ a r j).symm, ?_⟩⟩
      have h := armPathVertex_succ a r i
      simpa only [← hji] using h.symm

end SimpleGraph

namespace WeightedGraph

open Matrix SimpleGraph

variable {a : Fin 3 → ℕ} (Y : WeightedGraph (ArmVertex a))

/-- A heavy edge on one arm and first vertices on the other two arms contain a weighted fork. -/
theorem contains_fork_of_heavy_arm
    (hunit : ∀ i j, (armTree a).Adj i j → 1 ≤ Y.weights i j)
    (r s t : Fin 3) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hs : 0 < a s) (ht : 0 < a t) (k : ℕ) (hk : k < a r)
    (hweight : Real.sqrt 2 ≤ Y.weights (armPathVertex a r ⟨k, by omega⟩)
      (armPathVertex a r ⟨k + 1, by omega⟩)) :
    ∃ e : (Fin (k + 1 + 1) ⊕ Fin 2) ↪ ArmVertex a, Y.Contains (fork (k + 1)) e := by
  classical
  let p : Fin (k + 1 + 1) ↪ ArmVertex a :=
    (Fin.castLEEmb (show k + 1 + 1 ≤ a r + 1 by omega)).trans
      ⟨armPathVertex a r, armPathVertex_injective a r⟩
  let l : Fin 2 → ArmVertex a := ![some ⟨s, ⟨0, hs⟩⟩, some ⟨t, ⟨0, ht⟩⟩]
  let f : Fin (k + 1 + 1) ⊕ Fin 2 → ArmVertex a := Sum.elim p l
  have hleaf (j : Fin 2) : (armTree a).Adj none (l j) := by
    fin_cases j <;> rfl
  have hdisjoint (i : Fin (k + 1 + 1)) (j : Fin 2) : p i ≠ l j := by
    intro hij
    have heq := congrArg (fun z : ArmVertex a => z.map Sigma.fst) hij
    change (armPathVertex a r ⟨i.val, by omega⟩).map Sigma.fst = (l j).map Sigma.fst at heq
    fin_cases j <;> dsimp [armPathVertex, l] at heq <;> split_ifs at heq <;> simp_all
  have hlinj : Function.Injective l := by
    intro i j hij
    have heq := congrArg (fun z : ArmVertex a => z.map Sigma.fst) hij
    fin_cases i <;> fin_cases j <;> simp_all [l]
  have hinj : Function.Injective f := by
    rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (p.injective hij)
    · exact (hdisjoint i j hij).elim
    · exact (hdisjoint j i hij.symm).elim
    · exact congrArg Sum.inr (hlinj hij)
  have hpcontains : Y.Contains
      (path (k + 1 + 1) (fun i => if i + 1 = k + 1 then Real.sqrt 2 else 1)
        (by intro i; split_ifs <;> positivity)) p := by
    apply contains_path_of_consecutive
    intro b hb
    change (if b + 1 = k + 1 then Real.sqrt 2 else 1) ≤
      Y.weights (armPathVertex a r ⟨b, by omega⟩)
        (armPathVertex a r ⟨b + 1, by omega⟩)
    by_cases hbk : b = k
    · subst b
      simpa using hweight
    · simp only [Nat.add_right_cancel_iff, hbk, ite_false]
      exact hunit _ _ (armPathVertex_adj a r b (by omega))
  refine ⟨⟨f, hinj⟩, ?_⟩
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hpcontains i j
  · change (if i = 0 then (1 : ℝ) else 0) ≤ Y.weights (p i) (l j)
    by_cases hi : i = 0
    · subst i
      simpa [p, armPathVertex] using hunit _ _ (hleaf j)
    · simpa only [hi, ite_false] using Y.nonneg (p i) (l j)
  · change (if j = 0 then (1 : ℝ) else 0) ≤ Y.weights (l i) (p j)
    rw [Y.symmetric.apply (p j) (l i)]
    by_cases hj : j = 0
    · subst j
      simpa [p, armPathVertex] using hunit _ _ (hleaf i)
    · simpa only [hj, ite_false] using Y.nonneg (p j) (l i)
  · exact Y.nonneg _ _

/-- Without affine obstructions, every edge of a positive three-arm tree has weight less than √2. -/
theorem arm_edge_lt_sqrt_two_of_no_affine
    (hpos : ∀ r, 0 < a r)
    (hunit : ∀ i j, (armTree a).Adj i j → 1 ≤ Y.weights i j)
    (hno : ¬ Y.ContainsAffineObstruction) (r : Fin 3) (k : ℕ) (hk : k < a r) :
    Y.weights (armPathVertex a r ⟨k, by omega⟩)
      (armPathVertex a r ⟨k + 1, by omega⟩) < Real.sqrt 2 := by
  by_contra hn
  have hheavy := le_of_not_gt hn
  have hothers : ∃ s t : Fin 3, r ≠ s ∧ r ≠ t ∧ s ≠ t := by
    fin_cases r
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  obtain ⟨s, t, hrs, hrt, hst⟩ := hothers
  obtain ⟨e, he⟩ := Y.contains_fork_of_heavy_arm hunit r s t hrs hrt hst
    (hpos s) (hpos t) k hk hheavy
  exact not_contains_of_no_affine hno
    (.fork (k + 1) (by omega) (Equiv.refl _) rfl) e he

/-- Every arm edge has weight less than √2 below the affine threshold. -/
theorem arm_edge_lt_sqrt_two_of_maxRayleigh_lt_two
    (hpos : ∀ r, 0 < a r)
    (hunit : ∀ i j, (armTree a).Adj i j → 1 ≤ Y.weights i j)
    (hmax : maxRayleigh Y.isHermitian < 2) (r : Fin 3) (k : ℕ) (hk : k < a r) :
    Y.weights (armPathVertex a r ⟨k, by omega⟩)
      (armPathVertex a r ⟨k + 1, by omega⟩) < Real.sqrt 2 := by
  exact arm_edge_lt_sqrt_two_of_no_affine Y hpos hunit
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax) r k hk

/-- A positive three-arm support with Cartan weights and no affine obstruction has unit weights. -/
theorem eq_unit_of_arm_support_of_no_affine (hpos : ∀ r, 0 < a r) (hsupport : Y.support = armTree a)
    (hweights : ∀ i j, Y.support.Adj i j →
      Y.weights i j = 1 ∨ Y.weights i j = Real.sqrt 2 ∨ Y.weights i j = Real.sqrt 3)
    (hno : ¬ Y.ContainsAffineObstruction) : Y = unit (armTree a) := by
  have hunit (i j) (hij : (armTree a).Adj i j) : 1 ≤ Y.weights i j := by
    have hadj : Y.support.Adj i j := hsupport ▸ hij
    rcases hweights i j hadj with h | h | h <;> rw [h] <;> norm_num
  have hedge (i j) (hij : (armTree a).Adj i j) : Y.weights i j = 1 := by
    obtain ⟨r, k, hk, h | h⟩ := armTree_adj_exists_consecutive hij
    · obtain ⟨rfl, rfl⟩ := h
      have hlt := Y.arm_edge_lt_sqrt_two_of_no_affine hpos hunit hno r k hk
      rcases hweights _ _ (hsupport ▸ armPathVertex_adj a r k hk) with h | h | h
      · exact h
      · rw [h] at hlt
        exact (lt_irrefl _ hlt).elim
      · rw [h] at hlt
        have hsqrt : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
        exact (not_lt_of_ge hsqrt hlt).elim
    · obtain ⟨rfl, rfl⟩ := h
      rw [Y.symmetric.apply]
      have hlt := Y.arm_edge_lt_sqrt_two_of_no_affine hpos hunit hno r k hk
      rcases hweights _ _ (hsupport ▸ armPathVertex_adj a r k hk) with h | h | h
      · exact h
      · rw [h] at hlt
        exact (lt_irrefl _ hlt).elim
      · rw [h] at hlt
        have hsqrt : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
        exact (not_lt_of_ge hsqrt hlt).elim
  apply ext
  funext i j
  change Y.weights i j = if (armTree a).Adj i j then 1 else 0
  split_ifs with hij
  · exact hedge i j hij
  · apply le_antisymm
    · exact le_of_not_gt (fun h => hij (hsupport ▸ h))
    · exact Y.nonneg i j

/-- With Cartan edge weights and positive arm lengths, a three-arm support below the
affine threshold has only unit edges. -/
theorem eq_unit_of_arm_support (hpos : ∀ r, 0 < a r) (hsupport : Y.support = armTree a)
    (hweights : ∀ i j, Y.support.Adj i j →
      Y.weights i j = 1 ∨ Y.weights i j = Real.sqrt 2 ∨ Y.weights i j = Real.sqrt 3)
    (hmax : maxRayleigh Y.isHermitian < 2) : Y = unit (armTree a) := by
  exact eq_unit_of_arm_support_of_no_affine Y hpos hsupport hweights
    (not_containsAffineObstruction_of_maxRayleigh_lt_two hmax)

end WeightedGraph
