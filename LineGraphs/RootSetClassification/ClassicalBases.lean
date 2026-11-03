/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Basic
import LineGraphs.RootSetClassification.Classical

/-!
# The classical root bases

The telescoping argument `rclexpansions` and the basis argument `rclbase` in
`lem:classical` of the blueprint for Remark 3.11 of [CGSS]. Membership in a
natural-number span records the nonnegative integer expansions.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- Step `rclexpdiff` of Remark 3.11: consecutive differences telescope with
nonnegative integer coefficients. -/
theorem sub_mem_natSpan_of_le {V : Type*} [AddCommGroup V] {n : ℕ}
    (v : Fin (n + 1) → V) (i j : Fin (n + 1)) (hij : i ≤ j) :
    v i - v j ∈ span ℕ (Set.range (fun k : Fin n ↦ v k.castSucc - v k.succ)) := by
  induction j using Fin.induction generalizing i with
  | zero =>
    have hi : i = 0 := le_antisymm hij (Fin.zero_le i)
    simp [hi]
  | succ j ih =>
    by_cases hle : i ≤ j.castSucc
    · have he : v i - v j.succ =
          (v i - v j.castSucc) + (v j.castSucc - v j.succ) := by abel
      rw [he]
      exact add_mem (ih i hle) (subset_span (Set.mem_range_self j))
    · have hi : i = j.succ := by
        apply Fin.ext
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at hij hle ⊢
        omega
      simp [hi]

/-- The consecutive-difference family of `def:rem-classical` for A. -/
noncomputable def An.simpleRoot (n : ℕ) (i : Fin n) : span ℝ (LineSystem.An n).Φ :=
  ⟨unit i.castSucc - unit i.succ, subset_span
    (LineSystem.sub_single_mem_An _ _ (by intro h; have := congrArg Fin.val h; simp at this))⟩

/-- The B/C family of `def:rem-classical`, with a variable final axis. -/
noncomputable def axisSimpleRoots (n : ℕ) (c : ℝ) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
  Fin.lastCases (c • unit (Fin.last n)) (fun i ↦ unit i.castSucc - unit i.succ)

/-- The prescribed B base in `def:rem-classical`, in rank `n + 1`. -/
noncomputable def Bn.simpleRoot (n : ℕ) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := axisSimpleRoots n 1

/-- The prescribed C base in `def:rem-classical`, in rank `n + 1`. -/
noncomputable def Cn.simpleRoot (n : ℕ) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := axisSimpleRoots n 2

/-- The prescribed D base in `def:rem-classical`, in rank `n + 2`. -/
noncomputable def Dn.simpleRoot (n : ℕ) :
    Fin (n + 2) → EuclideanSpace ℝ (Fin (n + 2)) :=
  Fin.lastCases (unit (Fin.last n).castSucc + unit (Fin.last (n + 1)))
    (fun i ↦ unit i.castSucc - unit i.succ)

/-- Step `rclexpnegative`: the four sign patterns of a signed pair are a positive
difference, a positive sum, or the negative of one of these. -/
theorem mem_or_neg_mem_of_mem_Dn {n : ℕ}
    (N : Submodule ℕ (EuclideanSpace ℝ (Fin n)))
    (hsub : ∀ i j : Fin n, i < j → unit i - unit j ∈ N)
    (hadd : ∀ i j : Fin n, i < j → unit i + unit j ∈ N)
    {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ Dn n) : r ∈ N ∨ -r ∈ N := by
  obtain ⟨⟨⟨⟨i, j⟩, hij⟩, a, b⟩, rfl⟩ := hr
  change (LineSystem.integerVector 1 (LineSystem.dnRoot (⟨(i, j), hij⟩, a, b))) ∈ N ∨ _
  simp only [dnRoot_eq_signed_units]
  cases a <;> cases b <;> simp only [LineSystem.rootSign, Bool.false_eq_true,
    ite_false, ite_true, Int.cast_one, Int.cast_neg, one_smul, neg_smul]
  · exact Or.inl (hadd i j hij)
  · exact Or.inl (by simpa only [sub_eq_add_neg] using hsub i j hij)
  · right
    simpa only [neg_add, neg_neg, sub_eq_add_neg] using hsub i j hij
  · right
    simpa only [neg_add, neg_neg] using hadd i j hij

/-- Step `rclexpdiff` for the B and C candidate bases. -/
theorem sub_mem_natSpan_axisSimpleRoots (n : ℕ) (c : ℝ) (i j : Fin (n + 1))
    (hij : i ≤ j) : unit i - unit j ∈ span ℕ (Set.range (axisSimpleRoots n c)) := by
  apply span_mono (s := Set.range (fun k : Fin n ↦ unit k.castSucc - unit k.succ)) _
    (sub_mem_natSpan_of_le unit i j hij)
  rintro _ ⟨k, rfl⟩
  exact ⟨k.castSucc, by simp [axisSimpleRoots]⟩

/-- Step `rclexpBaxis`: each positive axis is in the natural span of the B base. -/
theorem unit_mem_natSpan_Bn (n : ℕ) (i : Fin (n + 1)) :
    unit i ∈ span ℕ (Set.range (Bn.simpleRoot n)) := by
  have hd := sub_mem_natSpan_axisSimpleRoots n 1 i (Fin.last n) (Fin.le_last i)
  have hl : unit (Fin.last n) ∈ span ℕ (Set.range (Bn.simpleRoot n)) := by
    simpa [Bn.simpleRoot, axisSimpleRoots] using
      (subset_span (Set.mem_range_self (f := Bn.simpleRoot n) (Fin.last n)))
  simpa only [Bn.simpleRoot, sub_add_cancel] using add_mem hd hl

/-- Step `rclexpCaxis`: each positive doubled axis is in the natural span of the C base. -/
theorem two_smul_unit_mem_natSpan_Cn (n : ℕ) (i : Fin (n + 1)) :
    (2 : ℝ) • unit i ∈ span ℕ (Set.range (Cn.simpleRoot n)) := by
  have hd := smul_mem (span ℕ (Set.range (Cn.simpleRoot n))) (2 : ℕ)
    (sub_mem_natSpan_axisSimpleRoots n 2 i (Fin.last n) (Fin.le_last i))
  have hl : (2 : ℝ) • unit (Fin.last n) ∈ span ℕ (Set.range (Cn.simpleRoot n)) := by
    simpa [Cn.simpleRoot, axisSimpleRoots] using
      (subset_span (Set.mem_range_self (f := Cn.simpleRoot n) (Fin.last n)))
  convert add_mem hd hl using 1
  simp only [two_smul]
  abel

/-- Step `rclexpdiff` for the D candidate base. -/
theorem sub_mem_natSpan_Dn (n : ℕ) (i j : Fin (n + 2)) (hij : i ≤ j) :
    unit i - unit j ∈ span ℕ (Set.range (Dn.simpleRoot n)) := by
  apply span_mono (s := Set.range (fun k : Fin (n + 1) ↦ unit k.castSucc - unit k.succ)) _
    (sub_mem_natSpan_of_le unit i j hij)
  rintro _ ⟨k, rfl⟩
  exact ⟨k.castSucc, by simp [Dn.simpleRoot]⟩

/-- Step `rclexpDlast`: the D base expands sums involving the final coordinate. -/
theorem add_last_mem_natSpan_Dn (n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    unit i + unit (Fin.last (n + 1)) ∈ span ℕ (Set.range (Dn.simpleRoot n)) := by
  have hp : i ≤ (Fin.last n).castSucc := by
    simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_last] at *
    omega
  have hd := sub_mem_natSpan_Dn n i (Fin.last n).castSucc hp
  have hl : unit (Fin.last n).castSucc + unit (Fin.last (n + 1)) ∈
      span ℕ (Set.range (Dn.simpleRoot n)) := by
    simpa [Dn.simpleRoot] using
      (subset_span (Set.mem_range_self (f := Dn.simpleRoot n) (Fin.last (n + 1))))
  convert add_mem hd hl using 1
  abel

/-- Step `rclexpDsum`: the remaining positive coordinate sums have nonnegative
integer expansions in the D base. -/
theorem add_mem_natSpan_Dn (n : ℕ) (i j : Fin (n + 2)) (hij : i < j) :
    unit i + unit j ∈ span ℕ (Set.range (Dn.simpleRoot n)) := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    exact add_last_mem_natSpan_Dn n i hij
  · have hj' : j < Fin.last (n + 1) := lt_of_le_of_ne (Fin.le_last j) hj
    have hd := sub_mem_natSpan_Dn n i (Fin.last (n + 1)) (Fin.le_last i)
    have hs := add_last_mem_natSpan_Dn n j hj'
    convert add_mem hd hs using 1
    abel

/-- Steps `rclexpansions`, `rclbase`: the displayed A family is a root base. -/
theorem An.base (n : ℕ) : (An_isRootSet n).IsBase (An.simpleRoot n) := by
  apply IsRootSet.isBase_of_mem_nat_span_or_neg_mem
  · intro i
    exact LineSystem.sub_single_mem_An _ _ (by intro h; have := congrArg Fin.val h; simp at this)
  · simpa using (LineSystem.finrank_span_An n).symm
  · intro r hr
    obtain ⟨⟨⟨i, j⟩, hij⟩, he⟩ := hr
    have hr' : (r : EuclideanSpace ℝ (Fin (n + 1))) = unit i - unit j := by
      rw [← he]
      ext k
      simp [LineSystem.integerVector, LineSystem.anRoot, LineSystem.pairVector,
        unit, Pi.single_apply, PiLp.single_apply]
      split_ifs <;> norm_num
    have lift_span (x : span ℝ (LineSystem.An n).Φ)
        (hx : (x : EuclideanSpace ℝ (Fin (n + 1))) ∈
          span ℕ (Set.range (fun k : Fin n ↦ unit k.castSucc - unit k.succ))) :
        x ∈ span ℕ (Set.range (An.simpleRoot n)) := by
      obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℕ).mp hx
      apply (mem_span_range_iff_exists_fun ℕ).mpr
      refine ⟨c, ?_⟩
      apply Subtype.ext
      simpa [An.simpleRoot] using hc
    rcases le_total i j with h | h
    · left
      apply lift_span
      rw [hr']
      exact sub_mem_natSpan_of_le unit i j h
    · right
      apply lift_span
      change -(r : EuclideanSpace ℝ (Fin (n + 1))) ∈ _
      rw [hr', neg_sub]
      exact sub_mem_natSpan_of_le unit j i h

/-- Steps `rclexpBaxis`, `rclexpBsum`, and `rclbase`: the displayed B family is a root base. -/
theorem Bn.base (n : ℕ) : (Bn_isRootSet (n + 1)).IsBase (Bn.simpleRoot n) := by
  apply IsRootSet.isBase_of_mem_nat_span_or_neg_mem
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact Or.inl ⟨Fin.last n, Or.inl (by simp [Bn.simpleRoot, axisSimpleRoots])⟩
    · change axisSimpleRoots n 1 j.castSucc ∈ _
      simp only [axisSimpleRoots, Fin.lastCases_castSucc]
      exact Or.inr (LineSystem.sub_single_mem_Dn _ _
        (by intro h; have := congrArg Fin.val h; simp at this))
  · simp
  · intro r hr
    rcases hr with hr | hr
    · obtain ⟨i, rfl | rfl⟩ := hr
      · left; simpa using unit_mem_natSpan_Bn n i
      · right; simpa using unit_mem_natSpan_Bn n i
    · apply mem_or_neg_mem_of_mem_Dn _ _ _ hr
      · exact fun i j hij ↦ sub_mem_natSpan_axisSimpleRoots n 1 i j hij.le
      · exact fun i j _ ↦ add_mem (unit_mem_natSpan_Bn n i) (unit_mem_natSpan_Bn n j)

/-- Steps `rclexpCaxis`, `rclexpCsum`, and `rclbase`: the displayed C family is a root base. -/
theorem Cn.base (n : ℕ) : (Cn_isRootSet (n + 1)).IsBase (Cn.simpleRoot n) := by
  apply IsRootSet.isBase_of_mem_nat_span_or_neg_mem
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact Or.inl ⟨Fin.last n, Or.inl (by simp [Cn.simpleRoot, axisSimpleRoots])⟩
    · change axisSimpleRoots n 2 j.castSucc ∈ _
      simp only [axisSimpleRoots, Fin.lastCases_castSucc]
      exact Or.inr (LineSystem.sub_single_mem_Dn _ _
        (by intro h; have := congrArg Fin.val h; simp at this))
  · simp
  · intro r hr
    rcases hr with hr | hr
    · obtain ⟨i, rfl | rfl⟩ := hr
      · exact Or.inl (two_smul_unit_mem_natSpan_Cn n i)
      · right; simpa using two_smul_unit_mem_natSpan_Cn n i
    · apply mem_or_neg_mem_of_mem_Dn _ _ _ hr
      · exact fun i j hij ↦ sub_mem_natSpan_axisSimpleRoots n 2 i j hij.le
      · intro i j hij
        have hd := sub_mem_natSpan_axisSimpleRoots n 2 i j hij.le
        have hs := two_smul_unit_mem_natSpan_Cn n j
        change unit i + unit j ∈ _
        have he : unit i + unit j = (unit i - unit j) + (2 : ℝ) • unit j := by
          simp only [two_smul]
          abel
        rw [he]
        exact add_mem hd hs

/-- Steps `rclexpDsum`, `rclexpDlast`, and `rclbase`: the displayed D family is a root base. -/
theorem Dn.base (n : ℕ) : (Dn_isRootSet (by omega : 2 ≤ n + 2)).IsBase (Dn.simpleRoot n) := by
  apply IsRootSet.isBase_of_mem_nat_span_or_neg_mem
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Dn, unit, Dn.simpleRoot, Fin.lastCases_last] using
        LineSystem.add_single_mem_Dn (Fin.last n).castSucc (Fin.last (n + 1))
          (Fin.castSucc_ne_last _)
    · simp only [Dn.simpleRoot, Fin.lastCases_castSucc]
      exact LineSystem.sub_single_mem_Dn _ _
        (by intro h; have := congrArg Fin.val h; simp at this)
  · simp
  · exact fun _ hr ↦ mem_or_neg_mem_of_mem_Dn _
      (fun i j hij ↦ sub_mem_natSpan_Dn n i j hij.le) (add_mem_natSpan_Dn n) hr

-- Remark 3.11, lem:classical
/-- The displayed bases in `lem:classical` of Remark 3.11. The B/C indices use
rank `n + 1` and the D indices use rank `n + 2`, so the endpoint coordinates are total. -/
theorem classical_base :
    (∀ n, (An_isRootSet n).IsBase (An.simpleRoot n)) ∧
    (∀ n, (Bn_isRootSet (n + 1)).IsBase (Bn.simpleRoot n)) ∧
    (∀ n, (Cn_isRootSet (n + 1)).IsBase (Cn.simpleRoot n)) ∧
    (∀ n, (Dn_isRootSet (by omega : 2 ≤ n + 2)).IsBase (Dn.simpleRoot n)) :=
  ⟨An.base, Bn.base, Cn.base, Dn.base⟩

end RootSetModel
