/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Coordinates
import LineGraphs.RootSystems.LineSystem

/-!
# The classical coordinate sets are root sets

The root-set part of `lem:classical` in the blueprint for Remark 3.11 of [CGSS].
The common axis-and-pair argument checks B and C together, with axis length 1 or 2.
The A and D checks reuse the coordinate proofs for the line-system models.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- Step `rclfiniteonly`: there are only finitely many signed axis roots. -/
theorem finite_axisRoots (n : ℕ) (c : ℝ) : (axisRoots n c).Finite := by
  have he : axisRoots n c =
      Set.range (fun i : Fin n ↦ c • unit i) ∪
      Set.range (fun i : Fin n ↦ -(c • unit i)) := by
    ext x
    simp only [axisRoots, Set.mem_ofPred_eq, Set.mem_union, Set.mem_range]
    aesop
  rw [he]
  exact (Set.finite_range _).union (Set.finite_range _)

/-- Step `rclfiniteonly`: a nonzero-length axis pattern excludes zero. -/
theorem zero_notMem_axisRoots {n : ℕ} {c : ℝ} (hc : c ≠ 0) :
    (0 : EuclideanSpace ℝ (Fin n)) ∉ axisRoots n c := by
  rintro ⟨i, hi | hi⟩
  · apply hc
    simpa [unit] using (congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) hi).symm
  · apply hc
    have he : (0 : ℝ) = -c := by
      simpa [unit] using congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) hi
    linarith

/-- Steps `rclaxisreduce`, `rctlengths`: the squared length of every axis root is `c²`. -/
theorem inner_self_of_mem_axisRoots {n : ℕ} {c : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ axisRoots n c) : ⟪x, x⟫ = c ^ 2 := by
  obtain ⟨i, rfl | rfl⟩ := hx <;>
    simp only [inner_neg_neg, real_inner_smul_left, real_inner_smul_right] <;>
    simp [unit, pow_two]

/-- Step `rclpairreduce`: a signed pair cannot be supported on one coordinate. -/
theorem smul_unit_notMem_Dn {n : ℕ} (i : Fin n) (c : ℝ) : c • unit i ∉ Dn n := by
  rintro ⟨a, ha⟩
  have hs (k : Fin n) (hk : k ≠ i) : LineSystem.dnRoot a k = 0 := by
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x k) ha
    have he' : (LineSystem.dnRoot a k : ℝ) = 0 := by
      simpa [LineSystem.integerVector, unit, Pi.single_apply, hk] using he
    exact_mod_cast he'
  have hi : a.1.val.1 = i := by
    by_contra h
    exact (LineSystem.dnRoot_ne_zero_iff a _).mpr (Or.inl rfl) (hs _ h)
  have hj : a.1.val.2 = i := by
    by_contra h
    exact (LineSystem.dnRoot_ne_zero_iff a _).mpr (Or.inr rfl) (hs _ h)
  exact (ne_of_lt a.1.property) (hi.trans hj.symm)

/-- Step `rclfinite`: each union of one nonzero axis pattern and the signed pairs is reduced. -/
theorem reduced_axisRoots_union_Dn {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ axisRoots n c ∪ Dn n)
    (t : ℝ) (ht : t • r ∈ axisRoots n c ∪ Dn n) : t = 1 ∨ t = -1 := by
  have solve (q : ℝ) (hq : q ≠ 0) (hrq : ⟪r, r⟫ = q)
      (htq : ⟪t • r, t • r⟫ = q) : t = 1 ∨ t = -1 := by
    rw [real_inner_smul_left, real_inner_smul_right, hrq] at htq
    have hs : t * t = 1 := by
      apply mul_right_cancel₀ hq
      nlinarith [htq]
    have hp : (t - 1) * (t + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · left; linarith
    · right; linarith
  rcases hr with hr | hr <;> rcases ht with ht | ht
  · exact solve _ (pow_ne_zero _ hc) (inner_self_of_mem_axisRoots hr)
      (inner_self_of_mem_axisRoots ht)
  · obtain ⟨i, rfl | rfl⟩ := hr
    · exact False.elim (smul_unit_notMem_Dn i (t * c) (by simpa [smul_smul] using ht))
    · exact False.elim (smul_unit_notMem_Dn i (-(t * c))
        (by simpa [smul_smul, smul_neg, neg_smul] using ht))
  · have ht0 : t ≠ 0 := by
      intro h
      subst t
      exact zero_notMem_axisRoots hc (by simpa using ht)
    obtain ⟨i, he | he⟩ := ht
    · have he' : r = (t⁻¹ * c) • unit i := by
        calc r = t⁻¹ • (t • r) := by simp [smul_smul, ht0]
             _ = (t⁻¹ * c) • unit i := by rw [he, smul_smul]
      exact False.elim (smul_unit_notMem_Dn i _ (he' ▸ hr))
    · have he' : r = (-(t⁻¹ * c)) • unit i := by
        calc r = t⁻¹ • (t • r) := by simp [smul_smul, ht0]
             _ = (-(t⁻¹ * c)) • unit i := by rw [he]; simp [smul_smul]
      exact False.elim (smul_unit_notMem_Dn i _ (he' ▸ hr))
  · exact solve 2 (by norm_num) ((LineSystem.Dn n).inner_self r hr)
      ((LineSystem.Dn n).inner_self (t • r) ht)

/-- Step `rclreflection`: all reflections in an axis-and-pair system preserve that system. -/
theorem reflection_mem_axisRoots_union_Dn {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    {r x : EuclideanSpace ℝ (Fin n)} (hr : r ∈ axisRoots n c ∪ Dn n)
    (hx : x ∈ axisRoots n c ∪ Dn n) : reflect r x ∈ axisRoots n c ∪ Dn n := by
  have he : ∃ e : Equiv.Perm (Fin n), ∃ s : Fin n → Bool,
      ∀ x, reflect r x = signedPermutation e s x := by
    rcases hr with hr | hr
    · obtain ⟨i, rfl | rfl⟩ := hr
      · exact ⟨Equiv.refl _, fun k ↦ decide (k = i),
          reflect_smul_unit_eq_signedPermutation i hc⟩
      · exact ⟨Equiv.refl _, fun k ↦ decide (k = i), fun x ↦
          (reflect_neg _ x).trans (reflect_smul_unit_eq_signedPermutation i hc x)⟩
    · exact exists_signedPermutation_reflect_of_mem_Dn hr
  obtain ⟨e, s, he⟩ := he
  rw [he]
  exact hx.elim (fun h ↦ Or.inl (signedPermutation_mem_axisRoots e s c h))
    (fun h ↦ Or.inr (signedPermutation_mem_Dn e s h))

/-- Steps `rclspanB`, `rclspanC`: any nonzero axis pattern spans the coordinate space. -/
theorem span_axisRoots_union_Dn {n : ℕ} {c : ℝ} (hc : c ≠ 0) :
    span ℝ (axisRoots n c ∪ Dn n) = ⊤ := by
  apply top_unique
  intro x _
  have hu (i : Fin n) : unit i ∈ span ℝ (axisRoots n c ∪ Dn n) := by
    have h := smul_mem (span ℝ (axisRoots n c ∪ Dn n)) c⁻¹
      (subset_span (show c • unit i ∈ axisRoots n c ∪ Dn n from Or.inl ⟨i, Or.inl rfl⟩))
    simpa [smul_smul, hc] using h
  have he : x = ∑ i, x i • unit i := by ext i; simp [unit, Pi.single_apply]
  rw [he]
  exact sum_mem fun i _ ↦ smul_mem _ _ (hu i)

/-- Step `rclinteger`: all coordinates of the classical models are integers. -/
theorem exists_integerVector_of_mem_axisRoots_union_Dn {n : ℕ} (c : ℤ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ axisRoots n (c : ℝ) ∪ Dn n) :
    ∃ w : Fin n → ℤ, x = LineSystem.integerVector 1 w := by
  rcases hx with hx | ⟨a, rfl⟩
  · obtain ⟨i, rfl | rfl⟩ := hx
    · refine ⟨Pi.single i c, ?_⟩
      ext k
      simp [LineSystem.integerVector, unit, Pi.single_apply, PiLp.single_apply]
    · refine ⟨Pi.single i (-c), ?_⟩
      ext k
      by_cases hki : k = i <;>
        simp [LineSystem.integerVector, unit, Pi.single_apply, hki]
  · exact ⟨LineSystem.dnRoot a, rfl⟩

/-- Steps `rclpairlengthtwo`, `rclpairB`, and `rclpairC`: the pairings are integral
when the axis length is 1 or 2. -/
theorem crystallographic_axisRoots_union_Dn {n : ℕ} {c : ℝ} (hc : c = 1 ∨ c = 2)
    {r s : EuclideanSpace ℝ (Fin n)} (hr : r ∈ axisRoots n c ∪ Dn n)
    (hs : s ∈ axisRoots n c ∪ Dn n) :
    ∃ z : ℤ, (z : ℝ) = 2 * ⟪r, s⟫ / ⟪r, r⟫ := by
  have hs' : ∃ w : Fin n → ℤ, s = LineSystem.integerVector 1 w := by
    rcases hc with rfl | rfl
    · exact exists_integerVector_of_mem_axisRoots_union_Dn 1 (by simpa using hs)
    · exact exists_integerVector_of_mem_axisRoots_union_Dn 2 (by simpa using hs)
  obtain ⟨w, rfl⟩ := hs'
  rcases hr with hr | hr
  · have hnorm := inner_self_of_mem_axisRoots hr
    rw [hnorm]
    obtain ⟨i, rfl | rfl⟩ := hr <;> rcases hc with rfl | rfl
    · refine ⟨2 * w i, ?_⟩
      simp [unit, EuclideanSpace.inner_single_left,
        LineSystem.integerVector]
    · refine ⟨w i, ?_⟩
      simp [unit, real_inner_smul_left, EuclideanSpace.inner_single_left,
        LineSystem.integerVector]
      ring
    · refine ⟨-(2 * w i), ?_⟩
      simp [unit, EuclideanSpace.inner_single_left,
        LineSystem.integerVector]
    · refine ⟨-w i, ?_⟩
      simp [unit, real_inner_smul_left, EuclideanSpace.inner_single_left,
        LineSystem.integerVector]
      ring
  · rw [(LineSystem.Dn n).inner_self r hr]
    obtain ⟨a, rfl⟩ := hr
    refine ⟨LineSystem.integerInner (LineSystem.dnRoot a) w, ?_⟩
    rw [LineSystem.inner_integerVector]
    ring

/-- The common root-set construction in `lem:classical` of Remark 3.11, assembling
`rclfinite`, `rclreflection`, `rclinteger`, and `rclspan` for B and C. -/
theorem isRootSet_axisRoots_union_Dn (n : ℕ) {c : ℝ} (hc : c = 1 ∨ c = 2) :
    IsRootSet (axisRoots n c ∪ Dn n) where
  finite := (finite_axisRoots n c).union (LineSystem.Dn n).finite
  zero_notMem := by
    have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
    rintro (h | h)
    · exact zero_notMem_axisRoots hc0 h
    · have hnorm := (LineSystem.Dn n).inner_self 0 h
      simp at hnorm
  span_eq_top := span_axisRoots_union_Dn (by rcases hc with rfl | rfl <;> norm_num)
  crystallographic := fun _ hr _ hs ↦ crystallographic_axisRoots_union_Dn hc hr hs
  reduced := fun _ hr t ht ↦ reduced_axisRoots_union_Dn
    (by rcases hc with rfl | rfl <;> norm_num) hr t ht
  reflection_mem := fun _ hr _ hs ↦ reflection_mem_axisRoots_union_Dn
    (by rcases hc with rfl | rfl <;> norm_num) hr hs

/-- The A case of `rclfinite`--`rclspan` in Remark 3.11, on the zero-sum hyperplane. -/
theorem An_isRootSet (n : ℕ) : IsRootSet (An n) :=
  (LineSystem.isStarClosed_An n).isRootSet_restrictSpan

/-- The B case of `lem:classical` in Remark 3.11. -/
theorem Bn_isRootSet (n : ℕ) : IsRootSet (Bn n) :=
  isRootSet_axisRoots_union_Dn n (Or.inl rfl)

/-- The C case of `lem:classical` in Remark 3.11, including C₂. -/
theorem Cn_isRootSet (n : ℕ) : IsRootSet (Cn n) :=
  isRootSet_axisRoots_union_Dn n (Or.inr rfl)

/-- The D case of `lem:classical` in Remark 3.11. The root-set assertion also holds
at ranks 2 and 3; rank at least 4 is required later for the classification list. -/
theorem Dn_isRootSet {n : ℕ} (hn : 2 ≤ n) : IsRootSet (Dn n) :=
  (LineSystem.isStarClosed_Dn n).isRootSet (LineSystem.span_Dn_eq_top hn)

-- Remark 3.11, lem:classical
/-- The root-set assertions of `lem:classical` of Remark 3.11 of [CGSS], in all
four construction ranges. -/
theorem classical_isRootSet :
    (∀ n, 1 ≤ n → IsRootSet (An n)) ∧
    (∀ n, 2 ≤ n → IsRootSet (Bn n)) ∧
    (∀ n, 2 ≤ n → IsRootSet (Cn n)) ∧
    (∀ n, 4 ≤ n → IsRootSet (Dn n)) :=
  ⟨fun n _ ↦ An_isRootSet n, fun n _ ↦ Bn_isRootSet n,
    fun n _ ↦ Cn_isRootSet n, fun _ hn ↦ Dn_isRootSet (by omega)⟩

end RootSetModel
