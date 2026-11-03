/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Models
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Orthogonal lines in the classical models

Blueprint Lemma `lem:6-orthogonal`, Section 6 of [CGSS]. The proof uses the two-coordinate
supports in Definition 3.1, without classification. Families are indexed by an arbitrary
finite type; pairwise orthogonality and nonzero norms already imply injectivity.
-/

open scoped BigOperators RealInnerProductSpace
open Finset

namespace LineSystem

/-- Step `s6oAdisj`: orthogonal roots in `A_ℓ` have disjoint supports. -/
theorem An.disjoint_supports_of_integerInner_eq_zero {n : ℕ} (p q : An.Index n)
    (h : integerInner (An.root p) (An.root q) = 0) :
    Disjoint ({p.1.1, p.1.2} : Finset (Fin (n + 1))) {q.1.1, q.1.2} := by
  have hp := p.property
  have hq := q.property
  rw [An.root, anRoot, integerInner_pairVector] at h
  simp only [anRoot, pairVector, Pi.add_apply, Pi.single_apply] at h
  simp only [disjoint_left, mem_insert, mem_singleton]
  intro i hi hj
  split_ifs at h <;> rcases hi with hi | hi <;> rcases hj with hj | hj <;> grind

-- Lemma (orthogonal lines in A and D), Section 6
/-- Step `s6oA` of blueprint `lem:6-orthogonal`, Section 6 of [CGSS]: `A_ℓ` has no
orthogonal family of `ℓ` roots when `2 ≤ ℓ`. This is independent of Theorem 3.5. -/
theorem An.not_card_pairwise_orthogonal {n : ℕ} (hn : 2 ≤ n) {I : Type*} [Fintype I]
    (v : I → EuclideanSpace ℝ (Fin (n + 1))) (hv : ∀ i, v i ∈ (An n).Φ)
    (ho : Pairwise fun i j ↦ ⟪v i, v j⟫ = 0) : Fintype.card I ≠ n := by
  classical
  have hindex : ∀ i, ∃ p : An.Index n, integerVector 1 (An.root p) = v i := hv
  choose p hp using hindex
  have hd : (↑(univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ ({(p i).1.1, (p i).1.2} :
      Finset (Fin (n + 1)))) := by
    intro i _ j _ hij
    apply An.disjoint_supports_of_integerInner_eq_zero
    have he : ⟪v i, v j⟫ = 0 := ho hij
    rw [← hp i, ← hp j, inner_integerVector] at he
    norm_num at he
    exact he
  have hc : (univ.biUnion fun i ↦ ({(p i).1.1, (p i).1.2} :
      Finset (Fin (n + 1)))).card = Fintype.card I * 2 := by
    rw [card_biUnion hd]
    simp only [card_pair (p _).property, sum_const, card_univ, smul_eq_mul]
  have hb := card_le_univ (univ.biUnion fun i ↦ ({(p i).1.1, (p i).1.2} :
    Finset (Fin (n + 1))))
  rw [hc, Fintype.card_fin] at hb
  omega

/-- Step `s6oDsupp`: orthogonal D roots have equal or disjoint two-coordinate supports. -/
theorem Dn.disjoint_or_eq_supports_of_integerInner_eq_zero {n : ℕ} (p q : Dn.Index n)
    (h : integerInner (Dn.root p) (Dn.root q) = 0) :
    Disjoint ({p.1.1.1, p.1.1.2} : Finset (Fin n)) {q.1.1.1, q.1.1.2} ∨ p.1 = q.1 := by
  rcases p with ⟨⟨⟨a, b⟩, hab⟩, u, v⟩
  rcases q with ⟨⟨⟨c, d⟩, hcd⟩, w, z⟩
  dsimp at hab hcd ⊢
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d
      exact Or.inr rfl
    · exfalso
      rw [Dn.root, dnRoot, integerInner_pairVector] at h
      simp only [dnRoot, pairVector, Pi.add_apply, Pi.single_apply, rootSign] at h
      split_ifs at h <;> grind
  · left
    rw [disjoint_left]
    intro i hi hj
    simp only [mem_insert, mem_singleton] at hi hj
    rw [Dn.root, dnRoot, integerInner_pairVector] at h
    simp only [dnRoot, pairVector, Pi.add_apply, Pi.single_apply, rootSign] at h
    split_ifs at h <;> rcases hi with hi | hi <;> rcases hj with hj | hj <;> grind

/-- The same-support inner-product calculation in step `s6oDperp`. -/
theorem Dn.integerInner_same_support {n : ℕ} (p : {p : Fin n × Fin n // p.1 < p.2})
    (a b : Bool × Bool) : integerInner (Dn.root (p, a)) (Dn.root (p, b)) =
      rootSign a.1 * rootSign b.1 + rootSign a.2 * rootSign b.2 := by
  rw [Dn.root, dnRoot, integerInner_pairVector]
  simp [dnRoot, pairVector, p.property.ne, p.property.ne.symm]

/-- Step `s6oDtwo`: at most two orthogonal D roots can have one prescribed support.
Their restrictions to those two coordinates are independent in `ℝ²`. -/
theorem Dn.card_le_two_of_same_support {n : ℕ} {I : Type*} [Fintype I]
    (p : I → Dn.Index n) (s : {s : Fin n × Fin n // s.1 < s.2})
    (hs : ∀ i, (p i).1 = s)
    (ho : Pairwise fun i j ↦ integerInner (Dn.root (p i)) (Dn.root (p j)) = 0) :
    Fintype.card I ≤ 2 := by
  let v : I → EuclideanSpace ℝ (Fin 2) := fun i ↦
    WithLp.toLp 2 ![(rootSign (p i).2.1 : ℝ), (rootSign (p i).2.2 : ℝ)]
  have hp (i : I) : p i = (s, (p i).2) := Prod.ext (hs i) rfl
  have hv (i : I) : ⟪v i, v i⟫ = 2 := by
    simp only [v, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    cases (p i).2.1 <;> cases (p i).2.2 <;> norm_num [rootSign]
  have hvne (i : I) : v i ≠ 0 := by
    intro hi
    have hi' := hv i
    rw [hi, inner_zero_left] at hi'
    norm_num at hi'
  have hvo : Pairwise fun i j ↦ ⟪v i, v j⟫ = 0 := by
    intro i j hij
    have he : integerInner (Dn.root (p i)) (Dn.root (p j)) = 0 := ho hij
    rw [hp i, hp j, Dn.integerInner_same_support] at he
    have he' : (rootSign (p i).2.1 : ℝ) * rootSign (p j).2.1 +
        (rootSign (p i).2.2 : ℝ) * rootSign (p j).2.2 = 0 := by exact_mod_cast he
    simpa [v, PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using he'
  have hi := linearIndependent_of_ne_zero_of_inner_eq_zero hvne hvo
  simpa using hi.fintype_card_le_finrank

-- Lemma (orthogonal lines in A and D), Section 6
/-- Steps `s6oDk` and `s6oD` of blueprint `lem:6-orthogonal`, Section 6 of [CGSS]: an
orthogonal family of `ℓ` roots in `D_ℓ` forces `ℓ` to be even. The result also holds at
ranks zero and one, so no lower bound on `ℓ` is needed. -/
theorem Dn.even_of_card_pairwise_orthogonal {n : ℕ} {I : Type*} [Fintype I]
    (v : I → EuclideanSpace ℝ (Fin n)) (hv : ∀ i, v i ∈ (Dn n).Φ)
    (ho : Pairwise fun i j ↦ ⟪v i, v j⟫ = 0) (hc : Fintype.card I = n) : Even n := by
  classical
  have hindex : ∀ i, ∃ p : Dn.Index n, integerVector 1 (Dn.root p) = v i := hv
  choose p hp using hindex
  have hi : Pairwise fun i j ↦ integerInner (Dn.root (p i)) (Dn.root (p j)) = 0 := by
    intro i j hij
    have he : ⟪v i, v j⟫ = 0 := ho hij
    rw [← hp i, ← hp j, inner_integerVector] at he
    norm_num at he
    exact he
  let S := univ.image (fun i ↦ (p i).1)
  have hd : (S : Set {s : Fin n × Fin n // s.1 < s.2}).PairwiseDisjoint
      (fun s ↦ ({s.1.1, s.1.2} : Finset (Fin n))) := by
    intro s hs t ht hst
    obtain ⟨i, _, rfl⟩ := mem_image.mp hs
    obtain ⟨j, _, rfl⟩ := mem_image.mp ht
    have hij : i ≠ j := fun he ↦ hst (congrArg (fun i ↦ (p i).1) he)
    exact (Dn.disjoint_or_eq_supports_of_integerInner_eq_zero _ _
      (hi hij)).resolve_right hst
  have hle : 2 * S.card ≤ n := by
    have hb := card_le_univ (S.biUnion fun s ↦ ({s.1.1, s.1.2} : Finset (Fin n)))
    rw [card_biUnion hd] at hb
    have hsCard (s : {s : Fin n × Fin n // s.1 < s.2}) :
        ({s.1.1, s.1.2} : Finset (Fin n)).card = 2 := card_pair s.property.ne
    simpa only [hsCard, sum_const, smul_eq_mul,
      Fintype.card_fin, mul_comm] using hb
  have hge : n ≤ 2 * S.card := by
    have hb (s : {s : Fin n × Fin n // s.1 < s.2}) :
        (univ.filter fun i ↦ (p i).1 = s).card ≤ 2 := by
      have hb := Dn.card_le_two_of_same_support
        (fun i : {i : I // (p i).1 = s} ↦ p i) s (fun i ↦ i.property)
        (fun i j hij ↦ hi (fun he ↦ hij (Subtype.ext he)))
      simpa only [Fintype.card_subtype] using hb
    have he := card_eq_sum_card_image (fun i ↦ (p i).1) (univ : Finset I)
    have hh := sum_le_sum (s := S) (fun s _ ↦ hb s)
    rw [← he, card_univ, hc] at hh
    simpa only [sum_const, smul_eq_mul, mul_comm] using hh
  exact ⟨S.card, by omega⟩

end LineSystem
