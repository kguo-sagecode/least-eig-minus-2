/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.ComponentClosure

/-!
# Stars with two original Hadamard roots

The counting and coordinate leaves `s6eQr` and `s6ethird` of blueprint Lemma `lem:6-E7`,
Section 6 of [CGSS]. Each adjacent line contributes exactly one root at inner product minus
one. The third root has coordinates zero or twice the original magnitude, so is new.
-/

open scoped BigOperators RealInnerProductSpace
open Finset

namespace Matrix.IsHadamard

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℤ} (hH : H.IsHadamard)
  (hn : 16 ∣ n) (hn16 : 16 ≤ n) (ha : H.AgreeSixteenths)

/-- Steps `s6eQlines`, `s6eQone`, `s6eQnone` and `s6eQr` of `lem:6-E7`: each original
root has `2n - 4` partners at inner product minus one, all in its component. -/
theorem ncard_component_inner_eq_neg_one (K : H.hadamardGraph.ConnectedComponent)
    {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ (hH.componentLineSystem hn hn16 ha K).Φ) :
    {s | s ∈ (hH.componentLineSystem hn hn16 ha K).Φ ∧ ⟪r, s⟫ = -1}.ncard = 2 * n - 4 := by
  classical
  let A : Set (HadamardPair n × Bool) :=
    {q | q.1 ∈ K.supp ∧ ⟪r, LineSystem.signedVec H.hadamardRoot q⟫ = -1}
  have he : LineSystem.signedVec H.hadamardRoot '' A =
      {s | s ∈ (hH.componentLineSystem hn hn16 ha K).Φ ∧ ⟪r, s⟫ = -1} := by
    ext s
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨(⟨q.1, hq.1⟩, q.2), rfl⟩, hq.2⟩
    · rintro ⟨⟨⟨p, b⟩, rfl⟩, hp⟩
      exact ⟨(p, b), ⟨p.property, hp⟩, rfl⟩
  rw [← he, Set.ncard_image_of_injective A (hH.signed_hadamardRoot_injective hn hn16 ha)]
  obtain ⟨⟨p, b⟩, rfl⟩ := hr
  have hterm (q : HadamardPair n) :
      (∑ c : Bool, if q ∈ K.supp ∧
        ⟪LineSystem.signedVec (fun p : K.supp ↦ H.hadamardRoot p) (p, b),
          LineSystem.signedVec H.hadamardRoot (q, c)⟫ = -1 then (1 : ℕ) else 0) =
        if q ≠ p.val ∧ ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ≠ 0 then 1 else 0 := by
    rw [Fintype.sum_bool]
    by_cases hpq : p.val = q
    · subst q
      cases b <;> simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
        inner_neg_left, inner_neg_right, hH.inner_hadamardRoot_self (by omega)] <;> norm_num
    · have hh := hH.inner_hadamardRoot_mem hn hn16 ha p q hpq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with hh | hh | hh
      · cases b <;> simp [LineSystem.signedVec, hh]
      all_goals
        have hq := hH.mem_component_of_inner_ne_zero K p.property
          (show ⟪H.hadamardRoot p, H.hadamardRoot q⟫ ≠ 0 by rw [hh]; norm_num)
        cases b <;> simp only [LineSystem.signedVec, Bool.false_eq_true, ite_false, ite_true,
          inner_neg_left, inner_neg_right, hh] <;> norm_num [hq, Ne.symm hpq]
  rw [Set.ncard_eq_toFinset_card']
  have hA : A.toFinset = univ.filter fun q : HadamardPair n × Bool ↦ q.1 ∈ K.supp ∧
      ⟪LineSystem.signedVec (fun p : K.supp ↦ H.hadamardRoot p) (p, b),
        LineSystem.signedVec H.hadamardRoot q⟫ = -1 := by
    ext q
    simp [A]
  rw [hA, card_filter, Fintype.sum_prod_type]
  simp_rw [hterm]
  rw [← card_filter]
  exact hH.card_adj_lineSystem hn hn16 ha p

/-- Step `s6enotK` of `lem:6-E7`, in every order: a sum of two original roots cannot
be an original root, since its coordinates are zero or twice the original magnitude. -/
theorem add_not_mem_lineSystem {r s : EuclideanSpace ℝ (Fin n)}
    (hr : r ∈ (hH.lineSystem hn hn16 ha).Φ) (hs : s ∈ (hH.lineSystem hn hn16 ha).Φ) :
    r + s ∉ (hH.lineSystem hn hn16 ha).Φ := by
  intro ht
  let c : Fin n := ⟨0, by omega⟩
  have hr' := hH.lineSystem_apply_mem hn hn16 ha r hr c
  have hs' := hH.lineSystem_apply_mem hn hn16 ha s hs c
  have ht' := hH.lineSystem_apply_mem hn hn16 ha (r + s) ht c
  have ha' : 0 < Real.sqrt (2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  change r c + s c = _ ∨ r c + s c = _ at ht'
  rcases hr' with hr' | hr' <;> rcases hs' with hs' | hs' <;>
    rcases ht' with ht' | ht' <;> linarith

/-- Step `s6eentries` of `lem:6-E7`: at order 16 the third root has exactly four
nonzero coordinates, each contributing one half to its squared norm. -/
theorem card_support_add_lineSystem (horder : n = 16) {r s : EuclideanSpace ℝ (Fin n)}
    (hr : r ∈ (hH.lineSystem hn hn16 ha).Φ) (hs : s ∈ (hH.lineSystem hn hn16 ha).Φ)
    (hrs : ⟪r, s⟫ = -1) : (univ.filter fun c ↦ (r + s) c ≠ 0).card = 4 := by
  classical
  subst n
  have ha2 : Real.sqrt (2 / (16 : ℝ)) ^ 2 = 1 / 8 := by norm_num
  have hnorm : ⟪r + s, r + s⟫ = 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right,
      (hH.lineSystem hn hn16 ha).inner_self r hr,
      (hH.lineSystem hn hn16 ha).inner_self s hs, real_inner_comm r s, hrs]
    norm_num
  have hsum : (∑ c : Fin 16, ((r + s) c) ^ 2) = 2 := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two] using hnorm
  have hsq (c : Fin 16) : ((r + s) c) ^ 2 =
      if (r + s) c ≠ 0 then (1 / 2 : ℝ) else 0 := by
    by_cases hz : (r + s) c = 0
    · simp [hz]
    · simp only [ne_eq, hz, not_false_eq_true, ite_true]
      have hr' := hH.lineSystem_apply_mem hn hn16 ha r hr c
      have hs' := hH.lineSystem_apply_mem hn hn16 ha s hs c
      change (r c + s c) ^ 2 = 1 / 2
      rcases hr' with hr' | hr' <;> rcases hs' with hs' | hs'
      · rw [hr', hs']
        nlinarith only [ha2]
      · exfalso
        apply hz
        change r c + s c = 0
        rw [hr', hs']
        ring
      · exfalso
        apply hz
        change r c + s c = 0
        rw [hr', hs']
        ring
      · rw [hr', hs']
        nlinarith only [ha2]
  simp_rw [hsq] at hsum
  rw [← sum_filter, sum_const, nsmul_eq_mul] at hsum
  exact_mod_cast (show (((univ.filter fun c ↦ (r + s) c ≠ 0).card : ℕ) : ℝ) = 4 by
    linarith)

/-- Steps `s6einR`, `s6enotK` and `s6eN`: the third root is new and the first root
has inner product one with it, as used in the star-count injection of `lem:6-E7`. -/
theorem add_mem_componentStarClosure_sdiff (K : H.hadamardGraph.ConnectedComponent)
    {r s : EuclideanSpace ℝ (Fin n)}
    (hr : r ∈ (hH.componentLineSystem hn hn16 ha K).Φ)
    (hs : s ∈ (hH.componentLineSystem hn hn16 ha K).Φ) (hrs : ⟪r, s⟫ = -1) :
    r + s ∈ (hH.componentStarClosure hn hn16 ha K).Φ \
      (hH.componentLineSystem hn hn16 ha K).Φ ∧ ⟪r, r + s⟫ = 1 := by
  obtain ⟨_, _, hsc, hsub, _⟩ := hH.componentStarClosure_properties hn hn16 ha K
  refine ⟨⟨hsc r (hsub hr) s (hsub hs) hrs, ?_⟩, ?_⟩
  · intro hadd
    exact hH.add_not_mem_lineSystem hn hn16 ha
      (hH.componentLineSystem_subset hn hn16 ha K hr)
      (hH.componentLineSystem_subset hn hn16 ha K hs)
      (hH.componentLineSystem_subset hn hn16 ha K hadd)
  · rw [inner_add_right, (hH.componentLineSystem hn hn16 ha K).inner_self r hr, hrs]
    norm_num

end Matrix.IsHadamard
