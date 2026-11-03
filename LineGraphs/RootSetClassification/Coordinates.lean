/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSystems.Defs
import LineGraphs.LineSystem.Models
import LineGraphs.LineSystem.ModelSpans
import LineGraphs.LineSystem.ClassicalModels

/-!
# Classical coordinate sets and signed coordinate reflections

`def:rem-classical` and `lem:rem-coordinate-reflections` in the blueprint for
Remark 3.11 of [CGSS]. Coordinates use `Fin n`; the paper's coordinate `i + 1`
is Lean's coordinate `i`. The A model is restricted to its root span, identified
below with the zero-sum hyperplane.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- The coordinate unit vector in `def:rem-classical` of Remark 3.11. -/
noncomputable def unit {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i 1

/-- Axis roots of a prescribed length, in `def:rem-classical` of Remark 3.11. -/
def axisRoots (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ i, x = c • unit i ∨ x = -(c • unit i)}

-- Remark 3.11, def:rem-classical
/-- The A root set of Remark 3.11 in its zero-sum span. -/
noncomputable def An (n : ℕ) : Set (span ℝ (LineSystem.An n).Φ) :=
  Subtype.val ⁻¹' (LineSystem.An n).Φ

/-- The B root set of Remark 3.11: signed axes and signed pairs. -/
noncomputable def Bn (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  axisRoots n 1 ∪ (LineSystem.Dn n).Φ

/-- The C root set of Remark 3.11: doubled signed axes and signed pairs. -/
noncomputable def Cn (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  axisRoots n 2 ∪ (LineSystem.Dn n).Φ

/-- The D root set of Remark 3.11: the signed two-coordinate roots. -/
noncomputable def Dn (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (LineSystem.Dn n).Φ

/-- The ambient span in `def:rem-classical` is precisely the zero-sum hyperplane. -/
theorem span_An_eq_ker_coordinateSum (n : ℕ) :
    span ℝ (LineSystem.An n).Φ = LinearMap.ker (LineSystem.coordinateSum (n + 1)) := by
  apply le_antisymm (LineSystem.span_An_le_ker_coordinateSum n)
  intro x hx
  have he : x = ∑ i : Fin n, x i.castSucc •
      (unit i.castSucc - unit (Fin.last n)) := by
    ext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · have hz : ∑ i, x i = 0 := hx
      rw [Fin.sum_univ_castSucc] at hz
      simp [unit]
      linarith
    · simp [unit, Pi.single_apply]
  rw [he]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span
    (LineSystem.sub_single_mem_An _ _ (Fin.castSucc_ne_last i)))

/-- The reflection formula, before choosing a proof that its root is nonzero.
This is the formula in `def:roots` of Remark 3.11. -/
noncomputable def reflect {n : ℕ} (r x : EuclideanSpace ℝ (Fin n)) :=
  x - (2 * ⟪r, x⟫ / ⟪r, r⟫) • r

/-- Step `rcoorddiff` of Remark 3.11: reflection in a coordinate difference swaps
the two coordinates. -/
theorem reflect_sub_unit {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    reflect (unit i - unit j) x k =
      if k = i then x j else if k = j then x i else x k := by
  have hnorm : ⟪unit i - unit j, unit i - unit j⟫ = (2 : ℝ) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    norm_num [unit, EuclideanSpace.inner_single_left, hij, hij.symm]
  rw [reflect, hnorm]
  simp only [inner_sub_left, unit, EuclideanSpace.inner_single_left,
    map_one, one_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs <;> simp_all

/-- Step `rcoordsum` of Remark 3.11: reflection in a coordinate sum swaps and
negates the two coordinates. -/
theorem reflect_add_unit {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    reflect (unit i + unit j) x k =
      if k = i then -x j else if k = j then -x i else x k := by
  have hnorm : ⟪unit i + unit j, unit i + unit j⟫ = (2 : ℝ) := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    norm_num [unit, EuclideanSpace.inner_single_left, hij, hij.symm]
  rw [reflect, hnorm]
  simp only [inner_add_left, unit, EuclideanSpace.inner_single_left,
    map_one, one_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply]
  split_ifs <;> simp_all

/-- Step `rcoordaxis` of Remark 3.11: every nonzero multiple of an axis has the
same reflection, negating exactly that coordinate. -/
theorem reflect_smul_unit {n : ℕ} (i : Fin n) {c : ℝ} (hc : c ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    reflect (c • unit i) x k = if k = i then -x i else x k := by
  simp only [reflect, real_inner_smul_left, real_inner_smul_right, unit,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply,
    ite_true, mul_one, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst k
    field_simp
    ring
  · simp

-- Remark 3.11, lem:rem-coordinate-reflections
/-- The three coordinate formulas in `lem:rem-coordinate-reflections`, steps
`rcoorddiff`, `rcoordsum`, and `rcoordaxis`, of Remark 3.11 of [CGSS]. -/
theorem coordinate_reflection {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    {c : ℝ} (hc : c ≠ 0) (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    (reflect (unit i - unit j) x k =
      if k = i then x j else if k = j then x i else x k) ∧
    (reflect (unit i + unit j) x k =
      if k = i then -x j else if k = j then -x i else x k) ∧
    (reflect (c • unit i) x k = if k = i then -x i else x k) :=
  ⟨reflect_sub_unit i j hij x k, reflect_add_unit i j hij x k,
    reflect_smul_unit i hc x k⟩

/-- A signed coordinate permutation for step `rcoordpatterns` of Remark 3.11.
The signs are attached to the source coordinates. -/
noncomputable def signedPermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : Fin n → Bool) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun k ↦ (LineSystem.rootSign (s (e.symm k)) : ℝ) * x (e.symm k))
  map_add' x y := by ext k; exact mul_add _ _ _
  map_smul' c x := by ext k; simp [mul_left_comm]

/-- The action on coordinate units in step `rcoordpatterns` of Remark 3.11. -/
theorem signedPermutation_unit {n : ℕ} (e : Equiv.Perm (Fin n)) (s : Fin n → Bool)
    (i : Fin n) : signedPermutation e s (unit i) =
      (LineSystem.rootSign (s i) : ℝ) • unit (e i) := by
  ext k
  change (LineSystem.rootSign (s (e.symm k)) : ℝ) * unit i (e.symm k) = _
  simp only [unit, PiLp.single_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : k = e i
  · subst k
    simp
  · have h' : e.symm k ≠ i := fun h' ↦ h (by
      simpa only [e.apply_symm_apply] using congrArg e h')
    simp [h, h']

/-- Step `rcoordpatterns`: signed coordinate permutations preserve each axis pattern. -/
theorem signedPermutation_mem_axisRoots {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : Fin n → Bool) (c : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ axisRoots n c) : signedPermutation e s x ∈ axisRoots n c := by
  obtain ⟨i, rfl | rfl⟩ := hx <;> refine ⟨e i, ?_⟩ <;>
    simp only [map_neg, map_smul, signedPermutation_unit] <;>
    cases s i <;> simp [LineSystem.rootSign]

/-- Step `rcoordpatterns`: signed coordinate permutations preserve the signed pairs. -/
theorem signedPermutation_mem_Dn {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Dn n) :
    signedPermutation e s x ∈ Dn n := by
  obtain ⟨a, rfl⟩ := hx
  let w : Fin n → ℤ := fun k ↦
    LineSystem.rootSign (s (e.symm k)) * LineSystem.dnRoot a (e.symm k)
  have hw : LineSystem.integerInner w w = 2 := by
    have he : ∑ k, w k * w k =
        ∑ k, LineSystem.dnRoot a (e.symm k) * LineSystem.dnRoot a (e.symm k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [w]
      cases s (e.symm k) <;> simp [LineSystem.rootSign]
    rw [LineSystem.integerInner, dotProduct, he,
      e.symm.sum_comp (fun k ↦ LineSystem.dnRoot a k * LineSystem.dnRoot a k)]
    exact LineSystem.integerInner_dnRoot_self a
  obtain ⟨b, hb⟩ := LineSystem.exists_dnRoot_of_inner_self w hw
  refine ⟨b, ?_⟩
  ext k
  simp [signedPermutation, LineSystem.integerVector, hb, w]

/-- The half-coordinate pattern occurring in `rcoordpatterns` of Remark 3.11. -/
def halfRoots (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i = 1 / 2 ∨ x i = -(1 / 2)}

/-- Step `rcoordpatterns`: signed permutations preserve all half-coordinate sign vectors. -/
theorem signedPermutation_mem_halfRoots {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ halfRoots n) :
    signedPermutation e s x ∈ halfRoots n := by
  intro k
  rcases hx (e.symm k) with h | h <;>
    cases hs : s (e.symm k) <;> simp [signedPermutation, LineSystem.rootSign, h, hs]

/-- Step `rcoordpermutation`: unsigned permutations preserve the coordinate sum. -/
theorem coordinateSum_signedPermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    LineSystem.coordinateSum n (signedPermutation e (fun _ ↦ false) x) =
      LineSystem.coordinateSum n x := by
  simp [LineSystem.coordinateSum, signedPermutation, LineSystem.rootSign, e.symm.sum_comp]

/-- Step `rcoordpermutation`: permutations preserve differences and hence the A roots. -/
theorem signedPermutation_mem_An {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ (LineSystem.An n).Φ) :
    signedPermutation e (fun _ ↦ false) x ∈ (LineSystem.An n).Φ := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, rfl⟩ := hx
  change signedPermutation e (fun _ ↦ false)
    (LineSystem.integerVector 1 (LineSystem.anRoot ⟨(i, j), hij⟩)) ∈ _
  have he : LineSystem.integerVector 1 (LineSystem.anRoot ⟨(i, j), hij⟩) =
      unit i - unit j := by
    ext k
    simp [LineSystem.integerVector, LineSystem.anRoot, LineSystem.pairVector,
      unit, Pi.single_apply, PiLp.single_apply]
    split_ifs <;> norm_num
  rw [he, map_sub, signedPermutation_unit, signedPermutation_unit]
  simpa [LineSystem.rootSign, unit] using
    LineSystem.sub_single_mem_An (e i) (e j) (e.injective.ne hij)

/-- Negating a root leaves its reflection unchanged (`lem:rem-reflection`). -/
theorem reflect_neg {n : ℕ} (r x : EuclideanSpace ℝ (Fin n)) :
    reflect (-r) x = reflect r x := by
  simp [reflect, inner_neg_left, neg_div, neg_smul]

/-- Step `rclrefA`: the difference reflection is an unsigned transposition. -/
theorem reflect_sub_unit_eq_signedPermutation {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : EuclideanSpace ℝ (Fin n)) :
    reflect (unit i - unit j) x =
      signedPermutation (Equiv.swap i j) (fun _ ↦ false) x := by
  ext k
  rw [reflect_sub_unit i j hij]
  by_cases hki : k = i
  · subst k
    simp [signedPermutation, LineSystem.rootSign]
  · by_cases hkj : k = j
    · subst k
      simp [signedPermutation, LineSystem.rootSign, hij.symm]
    · simp [signedPermutation, Equiv.swap_apply_def, LineSystem.rootSign, hki, hkj]

/-- Step `rclrefD`: the sum reflection is a transposition with two sign changes. -/
theorem reflect_add_unit_eq_signedPermutation {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : EuclideanSpace ℝ (Fin n)) :
    reflect (unit i + unit j) x =
      signedPermutation (Equiv.swap i j) (fun k ↦ decide (k = i ∨ k = j)) x := by
  ext k
  rw [reflect_add_unit i j hij]
  by_cases hki : k = i
  · subst k
    simp [signedPermutation, LineSystem.rootSign, hij.symm]
  · by_cases hkj : k = j
    · subst k
      simp [signedPermutation, LineSystem.rootSign, hij, hij.symm]
    · simp [signedPermutation, Equiv.swap_apply_def, LineSystem.rootSign, hki, hkj]

/-- Steps `rclrefB`, `rclrefC`: an axis reflection is a single sign change. -/
theorem reflect_smul_unit_eq_signedPermutation {n : ℕ} (i : Fin n)
    {c : ℝ} (hc : c ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    reflect (c • unit i) x =
      signedPermutation (Equiv.refl _) (fun k ↦ decide (k = i)) x := by
  ext k
  rw [reflect_smul_unit i hc]
  by_cases hki : k = i <;> simp [signedPermutation, LineSystem.rootSign, hki]

/-- The signed-pair coordinate description in `def:rem-classical` of Remark 3.11. -/
theorem dnRoot_eq_signed_units {n : ℕ} (a : LineSystem.DnIndex n) :
    LineSystem.integerVector 1 (LineSystem.dnRoot a) =
      (LineSystem.rootSign a.2.1 : ℝ) • unit a.1.val.1 +
      (LineSystem.rootSign a.2.2 : ℝ) • unit a.1.val.2 := by
  ext k
  simp [LineSystem.integerVector, LineSystem.dnRoot, LineSystem.pairVector,
    unit, Pi.single_apply, PiLp.single_apply]

/-- Steps `rclrefB`--`rclrefD`: every signed-pair reflection is a signed permutation. -/
theorem exists_signedPermutation_reflect_of_mem_Dn {n : ℕ}
    {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ Dn n) :
    ∃ e : Equiv.Perm (Fin n), ∃ s : Fin n → Bool,
      ∀ x, reflect r x = signedPermutation e s x := by
  obtain ⟨⟨⟨⟨i, j⟩, hij⟩, a, b⟩, rfl⟩ := hr
  change ∃ e s, ∀ x, reflect
    (LineSystem.integerVector 1 (LineSystem.dnRoot (⟨(i, j), hij⟩, a, b))) x = _
  rw [dnRoot_eq_signed_units]
  have hne : i ≠ j := ne_of_lt hij
  cases a <;> cases b <;> simp only [LineSystem.rootSign, Bool.false_eq_true,
    ite_false, ite_true, Int.cast_one, Int.cast_neg, one_smul, neg_smul]
  · exact ⟨Equiv.swap i j, fun k ↦ decide (k = i ∨ k = j),
      reflect_add_unit_eq_signedPermutation i j hne⟩
  · simpa only [← sub_eq_add_neg] using
      ⟨Equiv.swap i j, fun _ ↦ false, reflect_sub_unit_eq_signedPermutation i j hne⟩
  · refine ⟨Equiv.swap i j, fun _ ↦ false, fun x ↦ ?_⟩
    rw [show -unit i + unit j = -(unit i - unit j) by abel, reflect_neg]
    exact reflect_sub_unit_eq_signedPermutation i j hne x
  · refine ⟨Equiv.swap i j, fun k ↦ decide (k = i ∨ k = j), fun x ↦ ?_⟩
    rw [← neg_add, reflect_neg]
    exact reflect_add_unit_eq_signedPermutation i j hne x

end RootSetModel
