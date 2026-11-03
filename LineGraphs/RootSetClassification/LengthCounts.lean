/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.RootCounts

/-!
# Counts by squared root length

Steps `rctlengths` and the short/long columns of `lem:counts` in the blueprint
for Remark 3.11 of [CGSS]. The statements count roots of every real squared length,
so lengths absent from the table have count zero.
-/

open scoped RealInnerProductSpace

namespace RootSetModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Counting a constant-length pattern, used in step `rctlengths` of Remark 3.11. -/
theorem ncard_length_of_constant (Φ : Set V) {b : ℝ} (hb : ∀ r ∈ Φ, ⟪r, r⟫ = b)
    (q : ℝ) : {r ∈ Φ | ⟪r, r⟫ = q}.ncard = if q = b then Φ.ncard else 0 := by
  classical
  by_cases hq : q = b
  · subst q
    have he : {r ∈ Φ | ⟪r, r⟫ = b} = Φ := by
      ext r
      exact ⟨And.left, fun hr ↦ ⟨hr, hb r hr⟩⟩
    rw [he]
    simp
  · have he : {r ∈ Φ | ⟪r, r⟫ = q} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro r ⟨hr, he⟩
      exact hq (he.symm.trans (hb r hr))
    rw [he]
    simp [hq]

/-- Add the two disjoint pattern counts, as in `lem:counts` of Remark 3.11. -/
theorem ncard_length_union {Φ Ψ : Set V} (hd : Disjoint Φ Ψ)
    (hΦ : Φ.Finite) (hΨ : Ψ.Finite) (q : ℝ) :
    {r ∈ Φ ∪ Ψ | ⟪r, r⟫ = q}.ncard =
      {r ∈ Φ | ⟪r, r⟫ = q}.ncard + {r ∈ Ψ | ⟪r, r⟫ = q}.ncard := by
  have he : {r ∈ Φ ∪ Ψ | ⟪r, r⟫ = q} =
      {r ∈ Φ | ⟪r, r⟫ = q} ∪ {r ∈ Ψ | ⟪r, r⟫ = q} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [he, Set.ncard_union_eq
    (hd.mono (fun _ h ↦ h.1) (fun _ h ↦ h.1)) (hΦ.sep _) (hΨ.sep _)]

/-- The B short and long counts in `lem:counts` of Remark 3.11. -/
theorem Bn_length_counts (n : ℕ) (q : ℝ) :
    {r ∈ Bn n | ⟪r, r⟫ = q}.ncard =
      (if q = 1 then 2 * n else 0) + (if q = 2 then 2 * n * (n - 1) else 0) := by
  change {r ∈ axisRoots n 1 ∪ Dn n | ⟪r, r⟫ = q}.ncard = _
  rw [ncard_length_union (disjoint_axisRoots_Dn n 1)
    (finite_axisRoots n 1) (LineSystem.Dn n).finite]
  rw [ncard_length_of_constant _ (fun _ hr ↦ inner_self_of_mem_axisRoots hr),
    ncard_length_of_constant (Dn n) (LineSystem.Dn n).inner_self,
    axisRoots_ncard n (by norm_num : (1 : ℝ) ≠ 0), Dn_ncard]
  norm_num

/-- The C short and long counts in `lem:counts` of Remark 3.11, including rank two. -/
theorem Cn_length_counts (n : ℕ) (q : ℝ) :
    {r ∈ Cn n | ⟪r, r⟫ = q}.ncard =
      (if q = 2 then 2 * n * (n - 1) else 0) + (if q = 4 then 2 * n else 0) := by
  change {r ∈ axisRoots n 2 ∪ Dn n | ⟪r, r⟫ = q}.ncard = _
  rw [ncard_length_union (disjoint_axisRoots_Dn n 2)
    (finite_axisRoots n 2) (LineSystem.Dn n).finite]
  rw [ncard_length_of_constant _ (fun _ hr ↦ inner_self_of_mem_axisRoots hr),
    ncard_length_of_constant (Dn n) (LineSystem.Dn n).inner_self,
    axisRoots_ncard n (by norm_num : (2 : ℝ) ≠ 0), Dn_ncard]
  norm_num [add_comm]

/-- The independent sign choices in step `rctFshort` of Remark 3.11. -/
theorem halfRoots_eq_range (n : ℕ) : halfRoots n =
    Set.range (fun s : Fin n → Bool ↦ LineSystem.integerVector (1 / 2)
      (fun i ↦ LineSystem.rootSign (s i))) := by
  classical
  ext x
  constructor
  · intro hx
    refine ⟨fun i ↦ decide (x i = -(1 / 2)), ?_⟩
    ext i
    rcases hx i with hi | hi <;>
      norm_num [LineSystem.integerVector, LineSystem.rootSign, hi]
  · rintro ⟨s, rfl⟩ i
    cases hs : s i <;> norm_num [LineSystem.integerVector, LineSystem.rootSign, hs]

/-- Step `rctFshort`: the half-coordinate pattern has `2ⁿ` independent sign choices. -/
theorem halfRoots_ncard (n : ℕ) : (halfRoots n).ncard = 2 ^ n := by
  have hinj : Function.Injective (fun s : Fin n → Bool ↦
      LineSystem.integerVector (1 / 2) (fun i ↦ LineSystem.rootSign (s i))) := by
    intro s t h
    have he := LineSystem.integerVector_injective (by norm_num : (1 / 2 : ℝ) ≠ 0) h
    funext i
    exact LineSystem.rootSign_injective (congrFun he i)
  rw [halfRoots_eq_range, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  simp

/-- The disjoint integer and half-coordinate patterns in step `rctFshort`. -/
theorem disjoint_F₄_integer_half : Disjoint (Dn 4 ∪ axisRoots 4 1) (halfRoots 4) := by
  apply Set.disjoint_left.mpr
  intro x hx hh
  obtain ⟨i, hi⟩ := exists_zero_coordinate_of_mem_F₄_integer hx
  rcases hh i with h | h <;> norm_num [hi] at h

/-- The F₄ short and long counts in `lem:counts` of Remark 3.11. -/
theorem F₄_length_counts (q : ℝ) : {r ∈ F₄ | ⟪r, r⟫ = q}.ncard =
    (if q = 1 then 24 else 0) + (if q = 2 then 24 else 0) := by
  rw [F₄, ncard_length_union disjoint_F₄_integer_half
    ((LineSystem.Dn 4).finite.union (finite_axisRoots 4 1))
    (F₄_finite.subset (fun _ h ↦ Or.inr h)),
    ncard_length_union (disjoint_axisRoots_Dn 4 1).symm
      (LineSystem.Dn 4).finite (finite_axisRoots 4 1)]
  rw [ncard_length_of_constant (Dn 4) (LineSystem.Dn 4).inner_self,
    ncard_length_of_constant _ (fun _ hr ↦ inner_self_of_mem_axisRoots hr),
    ncard_length_of_constant _ (fun _ hr ↦ inner_self_of_mem_halfRoots_four hr),
    Dn_ncard, axisRoots_ncard 4 (by norm_num : (1 : ℝ) ≠ 0), halfRoots_ncard]
  by_cases h₁ : q = 1 <;> by_cases h₂ : q = 2 <;> norm_num [h₁, h₂]

/-- Transfer a filtered root count to its injective indices, as in step `rctG`. -/
theorem ncard_range_filter {I W : Type*} (f : I → W) (hf : Function.Injective f)
    (p : W → Prop) : {x ∈ Set.range f | p x}.ncard = {i | p (f i)}.ncard := by
  have he := ncard_restrict_range {x | p x} f hf
  rw [Set.ncard_subtype] at he
  exact he

/-- Step `rctG`: six G₂ roots have squared length two and six have squared length six. -/
theorem G₂_length_counts_two_six :
    {r ∈ G₂ | ⟪r, r⟫ = 2}.ncard = 6 ∧ {r ∈ G₂ | ⟪r, r⟫ = 6}.ncard = 6 := by
  have hg : Function.Injective gRoot := by
    intro a b h
    exact gRootEntries_injective (LineSystem.integerVector_injective (by norm_num)
      (congrArg Subtype.val h))
  have he (a : G₂Index) : ⟪gRoot a, gRoot a⟫ =
      (LineSystem.integerInner (gRootEntries a) (gRootEntries a) : ℝ) := by
    change ⟪LineSystem.integerVector 1 (gRootEntries a),
      LineSystem.integerVector 1 (gRootEntries a)⟫ = _
    rw [LineSystem.inner_integerVector]
    ring
  constructor <;> rw [G₂_eq_range, ncard_range_filter _ hg] <;>
    simp only [he] <;> norm_cast <;>
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] <;> decide +kernel

/-- All squared-length counts for G₂ in `lem:counts` of Remark 3.11. -/
theorem G₂_length_counts (q : ℝ) : {r ∈ G₂ | ⟪r, r⟫ = q}.ncard =
    (if q = 2 then 6 else 0) + (if q = 6 then 6 else 0) := by
  by_cases h₂ : q = 2
  · subst q
    simpa using G₂_length_counts_two_six.1
  by_cases h₆ : q = 6
  · subst q
    simpa using G₂_length_counts_two_six.2
  have he : {r ∈ G₂ | ⟪r, r⟫ = q} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro r ⟨hr, he⟩
    rcases gRoots_inner_self hr with h | h
    · exact h₂ (he.symm.trans h)
    · exact h₆ (he.symm.trans h)
  rw [he]
  simp [h₂, h₆]

/-- The full length-count table in `lem:counts` of Remark 3.11. -/
noncomputable def lengthCount {n : ℕ} (t : CartanMatrix.FiniteType n) (q : ℝ) : ℕ :=
  match t with
  | .b n _ => (if q = 1 then 2 * n else 0) + (if q = 2 then 2 * n * (n - 1) else 0)
  | .c n _ => (if q = 2 then 2 * n * (n - 1) else 0) + (if q = 4 then 2 * n else 0)
  | .f₄ => (if q = 1 then 24 else 0) + (if q = 2 then 24 else 0)
  | .g₂ => (if q = 2 then 6 else 0) + (if q = 6 then 6 else 0)
  | t => if q = 2 then rootCount t else 0

-- Remark 3.11, lem:counts
/-- The short, long, and one-length counts of `lem:counts` in Remark 3.11 of [CGSS]. -/
theorem length_counts {n : ℕ} (t : CartanMatrix.FiniteType n) (q : ℝ) :
    {r ∈ roots t | ⟪r, r⟫ = q}.ncard = lengthCount t q := by
  cases t with
  | a n hn =>
    change {r ∈ An n | ⟪r, r⟫ = q}.ncard = if q = 2 then n * (n + 1) else 0
    rw [ncard_length_of_constant (An n) (fun r hr ↦ (LineSystem.An n).inner_self r hr),
      An_ncard]
  | b n _ => exact Bn_length_counts n q
  | c n _ => exact Cn_length_counts n q
  | d n hn =>
    change {r ∈ Dn n | ⟪r, r⟫ = q}.ncard = if q = 2 then 2 * n * (n - 1) else 0
    rw [ncard_length_of_constant (Dn n) (LineSystem.Dn n).inner_self, Dn_ncard]
  | e₆ =>
    change {r ∈ E₆ | ⟪r, r⟫ = q}.ncard = if q = 2 then 72 else 0
    rw [ncard_length_of_constant E₆ (fun r hr ↦ LineSystem.E₈.inner_self r hr), E₆_ncard]
  | e₇ =>
    change {r ∈ E₇ | ⟪r, r⟫ = q}.ncard = if q = 2 then 126 else 0
    rw [ncard_length_of_constant E₇ (fun r hr ↦ LineSystem.E₈.inner_self r hr), E₇_ncard]
  | e₈ =>
    change {r ∈ E₈ | ⟪r, r⟫ = q}.ncard = if q = 2 then 240 else 0
    rw [ncard_length_of_constant E₈ LineSystem.E₈.inner_self, E₈_ncard]
  | f₄ => exact F₄_length_counts q
  | g₂ => exact G₂_length_counts q

end RootSetModel
