/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.Models
import LineGraphs.Computations.C5Inclusions

/-!
# Counts of the coordinate roots

Steps `rctA`--`rctG` of `lem:counts` in the blueprint for Remark 3.11 of
[CGSS]. Restriction to a specified subspace becomes a finite predicate on the
integer indices. The E₆ and E₇ predicates use the signs prescribed in `def:rem-exceptional`.
-/

open scoped RealInnerProductSpace
open Submodule

namespace RootSetModel

/-- Counting roots in a subspace, as in steps `rctE7int`--`rctE6half` of Remark 3.11. -/
theorem ncard_restrict_range {I V : Type*} (S : Set V) (f : I → V)
    (hf : Function.Injective f) :
    {x : S | x.val ∈ Set.range f}.ncard = {i | f i ∈ S}.ncard := by
  rw [Set.ncard_subtype]
  change (Set.range f ∩ S).ncard = _
  have he : f '' {i | f i ∈ S} = Set.range f ∩ S := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Set.mem_range_self i, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
  rw [← he]
  exact Set.ncard_image_of_injective _ hf

/-- Step `rctA`: the A model has `n(n+1)` roots in its zero-sum space. -/
theorem An_ncard (n : ℕ) : (An n).ncard = n * (n + 1) := by
  rw [An, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
  · exact LineSystem.ncard_Φ_An n
  · intro x hx
    exact ⟨⟨x, subset_span hx⟩, rfl⟩

/-- Step `rctpairs`: the signed two-coordinate pattern has `2n(n-1)` members. -/
theorem Dn_ncard (n : ℕ) : (Dn n).ncard = 2 * n * (n - 1) := by
  rw [Dn, LineSystem.ncard_Φ_Dn]
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.sub_zero, Nat.mul_one] at h
  nlinarith

/-- The axis parametrization used in step `rctaxes` of Remark 3.11. -/
theorem axisRoots_eq_range (n : ℕ) (c : ℝ) : axisRoots n c =
    Set.range (fun a : Fin n × Bool ↦ (c * (LineSystem.rootSign a.2 : ℝ)) • unit a.1) := by
  ext x
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨(i, false), by simp [LineSystem.rootSign]⟩
    · exact ⟨(i, true), by simp [LineSystem.rootSign]⟩
  · rintro ⟨⟨i, b⟩, rfl⟩
    refine ⟨i, ?_⟩
    cases b <;> simp [LineSystem.rootSign]

/-- Step `rctaxes`: a nonzero-length signed axis determines its coordinate and sign. -/
theorem axisRoot_injective {n : ℕ} {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (fun a : Fin n × Bool ↦
      (c * (LineSystem.rootSign a.2 : ℝ)) • unit a.1) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) h
  have hij : i = j := by
    by_contra hn
    cases a <;> cases b <;> simp [unit, LineSystem.rootSign, hn, hc] at hi
  subst j
  have he : c * (LineSystem.rootSign a : ℝ) = c * (LineSystem.rootSign b : ℝ) := by
    simpa [unit] using hi
  have hab : a = b := LineSystem.rootSign_injective
    (Int.cast_injective (mul_left_cancel₀ hc he))
  subst b
  rfl

/-- Step `rctaxes`: there are exactly `2n` axes at any prescribed nonzero length. -/
theorem axisRoots_ncard (n : ℕ) {c : ℝ} (hc : c ≠ 0) :
    (axisRoots n c).ncard = 2 * n := by
  rw [axisRoots_eq_range, Set.ncard_range_of_injective (axisRoot_injective hc),
    Nat.card_eq_fintype_card]
  simp [mul_comm]

/-- The disjointness of patterns used in `rctaxes` and `rctpairs` of Remark 3.11. -/
theorem disjoint_axisRoots_Dn (n : ℕ) (c : ℝ) : Disjoint (axisRoots n c) (Dn n) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨i, rfl | rfl⟩ hx
  · exact smul_unit_notMem_Dn i c hx
  · exact smul_unit_notMem_Dn i (-c) (by simpa only [neg_smul] using hx)

/-- The B root count in the table of `lem:counts`, Remark 3.11. -/
theorem Bn_ncard (n : ℕ) : (Bn n).ncard = 2 * n ^ 2 := by
  change (axisRoots n 1 ∪ Dn n).ncard = _
  rw [Set.ncard_union_eq (disjoint_axisRoots_Dn n 1)
    (finite_axisRoots n 1) (LineSystem.Dn n).finite,
    axisRoots_ncard n (by norm_num : (1 : ℝ) ≠ 0), Dn_ncard]
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_one_sub_one]; ring

/-- The C root count in the table of `lem:counts`, Remark 3.11, including rank two. -/
theorem Cn_ncard (n : ℕ) : (Cn n).ncard = 2 * n ^ 2 := by
  change (axisRoots n 2 ∪ Dn n).ncard = _
  rw [Set.ncard_union_eq (disjoint_axisRoots_Dn n 2)
    (finite_axisRoots n 2) (LineSystem.Dn n).finite,
    axisRoots_ncard n (by norm_num : (2 : ℝ) ≠ 0), Dn_ncard]
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_one_sub_one]; ring

/-- Steps `rctE8int`, `rctE8half`: the full E₈ root count is 240. -/
theorem E₈_ncard : E₈.ncard = 240 := LineSystem.ncard_Φ_E₈

/-- The signed E₇ index restriction in steps `rctE7int`, `rctE7half` of Remark 3.11. -/
abbrev E₇Index := {a : LineSystem.E₈Index |
  LineSystem.e₈Root a 6 + LineSystem.e₈Root a 7 = 0}

/-- The signed E₆ index restriction in steps `rctE6int`, `rctE6half` of Remark 3.11. -/
abbrev E₆Index := {a : LineSystem.E₈Index |
  LineSystem.e₈Root a 5 = LineSystem.e₈Root a 6 ∧
    LineSystem.e₈Root a 6 = -LineSystem.e₈Root a 7}

/-- The integer form of the E₇ subspace equation, used for `lem:counts`. -/
theorem integerVector_mem_e₇Space (v : Fin 8 → ℤ) :
    LineSystem.integerVector (1 / 2) v ∈ e₇Space ↔ v 6 + v 7 = 0 := by
  rw [mem_e₇Space]
  change (1 / 2 : ℝ) * (v 6 : ℝ) + (1 / 2 : ℝ) * (v 7 : ℝ) = 0 ↔ _
  rw [← mul_add, mul_eq_zero]
  norm_num
  exact_mod_cast (Iff.rfl : v 6 + v 7 = 0 ↔ v 6 + v 7 = 0)

/-- The integer form of the E₆ subspace equations, used for `lem:counts`. -/
theorem integerVector_mem_e₆Space (v : Fin 8 → ℤ) :
    LineSystem.integerVector (1 / 2) v ∈ e₆Space ↔ v 5 = v 6 ∧ v 6 = -v 7 := by
  rw [mem_e₆Space]
  change (1 / 2 : ℝ) * (v 5 : ℝ) = (1 / 2 : ℝ) * (v 6 : ℝ) ∧
    (1 / 2 : ℝ) * (v 6 : ℝ) = -((1 / 2 : ℝ) * (v 7 : ℝ)) ↔ _
  rw [← mul_neg, mul_right_inj' (by norm_num : (1 / 2 : ℝ) ≠ 0),
    mul_right_inj' (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  norm_cast

/-- Steps `rctE7first`--`rctE7half`: the signed E₇ restriction contains 126 roots. -/
theorem E₇_ncard : E₇.ncard = 126 := by
  have hinj : Function.Injective (fun a : LineSystem.E₈Index ↦
      LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a)) :=
    (LineSystem.integerVector_injective (by norm_num : (1 / 2 : ℝ) ≠ 0)).comp
      LineSystem.e₈Root_injective
  change {x : e₇Space | x.val ∈ Set.range
    (fun a : LineSystem.E₈Index ↦ LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a))}.ncard = _
  refine (ncard_restrict_range (e₇Space : Set _) _ hinj).trans ?_
  change {a : LineSystem.E₈Index |
    LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a) ∈ e₇Space}.ncard = 126
  simp only [integerVector_mem_e₇Space]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  change Fintype.card E₇Index = 126
  decide +kernel

/-- Steps `rctE6support`--`rctE6half`: the signed E₆ restriction contains 72 roots. -/
theorem E₆_ncard : E₆.ncard = 72 := by
  have hinj : Function.Injective (fun a : LineSystem.E₈Index ↦
      LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a)) :=
    (LineSystem.integerVector_injective (by norm_num : (1 / 2 : ℝ) ≠ 0)).comp
      LineSystem.e₈Root_injective
  change {x : e₆Space | x.val ∈ Set.range
    (fun a : LineSystem.E₈Index ↦ LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a))}.ncard = _
  refine (ncard_restrict_range (e₆Space : Set _) _ hinj).trans ?_
  change {a : LineSystem.E₈Index |
    LineSystem.integerVector (1 / 2) (LineSystem.e₈Root a) ∈ e₆Space}.ncard = 72
  simp only [integerVector_mem_e₆Space]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  change Fintype.card E₆Index = 72
  decide +kernel

/-- Steps `rctFlong`, `rctFshort`: support and signs uniquely recover an F₄ index. -/
theorem fRootEntries_injective : Function.Injective fRootEntries := by decide +kernel

/-- Steps `rctFlong`, `rctFshort`: F₄ has 48 roots. -/
theorem F₄_ncard : F₄.ncard = 48 := by
  have hinj : Function.Injective (fun a : F₄Index ↦
      LineSystem.integerVector (1 / 2) (fRootEntries a)) :=
    (LineSystem.integerVector_injective (by norm_num : (1 / 2 : ℝ) ≠ 0)).comp
      fRootEntries_injective
  rw [F₄_eq_range, Set.ncard_range_of_injective hinj,
    Nat.card_eq_fintype_card]
  decide +kernel

/-- Step `rctG`: the support, doubled coordinate, and signs recover the G₂ index. -/
theorem gRootEntries_injective : Function.Injective gRootEntries := by decide +kernel

/-- Step `rctG`: G₂ has twelve roots. -/
theorem G₂_ncard : G₂.ncard = 12 := by
  have hg : Function.Injective gRoot := by
    intro a b h
    exact gRootEntries_injective (LineSystem.integerVector_injective (by norm_num)
      (congrArg Subtype.val h))
  rw [G₂_eq_range, Set.ncard_range_of_injective hg, Nat.card_eq_fintype_card]
  decide +kernel

/-- The total root-count column of the table in `lem:counts` of Remark 3.11. -/
def rootCount {n : ℕ} : CartanMatrix.FiniteType n → ℕ
  | .a n _ => n * (n + 1)
  | .b n _ | .c n _ => 2 * n ^ 2
  | .d n _ => 2 * n * (n - 1)
  | .e₆ => 72
  | .e₇ => 126
  | .e₈ => 240
  | .f₄ => 48
  | .g₂ => 12

-- Remark 3.11, lem:counts
/-- The root-count assertions of `lem:counts` in Remark 3.11 of [CGSS]. -/
theorem root_counts {n : ℕ} (t : CartanMatrix.FiniteType n) : (roots t).ncard = rootCount t := by
  cases t with
  | a n _ => exact An_ncard n
  | b n _ => exact Bn_ncard n
  | c n _ => exact Cn_ncard n
  | d n _ => exact Dn_ncard n
  | e₆ => exact E₆_ncard
  | e₇ => exact E₇_ncard
  | e₈ => exact E₈_ncard
  | f₄ => exact F₄_ncard
  | g₂ => exact G₂_ncard

end RootSetModel
