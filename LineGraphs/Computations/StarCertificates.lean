/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ModelCertificates
import LineGraphs.Computations.GraphCertificates
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Marked stars and their finite certificates

The finite labels are identified with the actual sets `H.Γa` and `H.Δ`.
-/

open scoped RealInnerProductSpace
open Computations

namespace LineSystem.IntegerModel

variable {d : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin d))} (M : IntegerModel S)

theorem inner_eq_zero_iff (a b : M.ι) :
    ⟪integerVector M.c (M.v a), integerVector M.c (M.v b)⟫ = 0 ↔
      integerInner (M.v a) (M.v b) = 0 := by
  rw [inner_integerVector, mul_eq_zero]
  simp [M.c_ne_zero]

theorem inner_eq_one_iff (a b : M.ι) :
    ⟪integerVector M.c (M.v a), integerVector M.c (M.v b)⟫ = 1 ↔
      integerInner (M.v a) (M.v b) = M.q := by
  rw [inner_integerVector, ← M.hc, mul_right_inj' (mul_ne_zero M.c_ne_zero M.c_ne_zero)]
  exact Int.cast_inj

/-- Construct Hypothesis 2.4 with the specified integer roots as the ordered star. -/
noncomputable def hyp24 (hi : S.IsIndecomposable) (hs : S.IsStarClosed)
    (a b : M.ι) (hab : integerInner (M.v a) (M.v b) = -M.q) :
    Hyp24 (EuclideanSpace ℝ (Fin d)) where
  S := S
  isIndecomposable := hi
  isStarClosed := hs
  a := integerVector M.c (M.v a)
  b := integerVector M.c (M.v b)
  a_mem := M.root_mem a
  b_mem := M.root_mem b
  inner_a_b := (M.inner_eq_neg_one_iff a b).mpr hab

variable (hi : S.IsIndecomposable) (hs : S.IsStarClosed)
  (a b : M.ι) (hab : integerInner (M.v a) (M.v b) = -M.q)

theorem mem_Γa_iff (i : M.ι) :
    integerVector M.c (M.v i) ∈ (M.hyp24 hi hs a b hab).Γa ↔
      integerInner (M.v i) (M.v a) = 0 ∧ integerInner (M.v i) (M.v b) = M.q := by
  simp only [Hyp24.Γa, Set.mem_ofPred_eq, M.root_mem, true_and, hyp24]
  constructor
  · intro h
    exact ⟨(M.inner_eq_zero_iff i a).mp h.1, (M.inner_eq_one_iff i b).mp h.2.1⟩
  · rintro ⟨h₁, h₂⟩
    have h₁' := (M.inner_eq_zero_iff i a).mpr h₁
    have h₂' := (M.inner_eq_one_iff i b).mpr h₂
    exact ⟨h₁', h₂', by simp [Hyp24.c, inner_sub_right, h₁', h₂']⟩

theorem mem_Δ_iff (i : M.ι) :
    integerVector M.c (M.v i) ∈ (M.hyp24 hi hs a b hab).Δ ↔
      integerInner (M.v i) (M.v a) = 0 ∧ integerInner (M.v i) (M.v b) = 0 := by
  simp only [Hyp24.Δ, Set.mem_ofPred_eq, M.root_mem, true_and, hyp24]
  constructor
  · intro h
    exact ⟨(M.inner_eq_zero_iff i a).mp h.1, (M.inner_eq_zero_iff i b).mp h.2.1⟩
  · rintro ⟨h₁, h₂⟩
    have h₁' := (M.inner_eq_zero_iff i a).mpr h₁
    have h₂' := (M.inner_eq_zero_iff i b).mpr h₂
    refine ⟨h₁', h₂', ?_⟩
    simp [Hyp24.c, inner_sub_right, h₁', h₂']

/-- A checked enumeration labels a subset of the real roots, without multiplicities. -/
noncomputable def subsetEquiv {κ : Type*} (T : Set (EuclideanSpace ℝ (Fin d)))
    (hT : T ⊆ S.Φ) (label : κ → M.ι) (inj : Function.Injective label)
    (cover : ∀ i, integerVector M.c (M.v i) ∈ T ↔ ∃ j, label j = i) : κ ≃ T :=
  Equiv.ofBijective (fun j => ⟨integerVector M.c (M.v (label j)),
    (cover _).mpr ⟨j, rfl⟩⟩) ⟨by
      intro i j h
      exact inj (M.inj (integerVector_injective M.c_ne_zero (congrArg Subtype.val h))), by
      rintro ⟨x, hx⟩
      obtain ⟨i, he⟩ := M.equiv.surjective ⟨x, hT hx⟩
      have hv : integerVector M.c (M.v i) = x := congrArg Subtype.val he
      obtain ⟨j, rfl⟩ := (cover i).mp (hv ▸ hx)
      exact ⟨j, Subtype.ext hv⟩⟩

end LineSystem.IntegerModel

namespace SimpleGraph.Iso

variable {V W : Type*} [Fintype V] [Fintype W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Strongly regular parameters are preserved under graph isomorphism. -/
theorem isSRGWith (e : G ≃g H) {n k l m : ℕ} (h : G.IsSRGWith n k l m) :
    H.IsSRGWith n k l m := by
  classical
  have common (i j : V) : Fintype.card (H.commonNeighbors (e i) (e j)) =
      Fintype.card (G.commonNeighbors i j) := by
    apply Fintype.card_congr
    exact (e.toEquiv.subtypeEquiv (fun x => by
      change (G.Adj i x ∧ G.Adj j x) ↔ (H.Adj (e i) (e x) ∧ H.Adj (e j) (e x))
      rw [e.map_rel_iff, e.map_rel_iff])).symm
  refine ⟨(Fintype.card_congr e.toEquiv).symm.trans h.card, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [e.degree_eq]
    exact h.regular v
  · intro v w hvw
    obtain ⟨i, rfl⟩ := e.surjective v
    obtain ⟨j, rfl⟩ := e.surjective w
    rw [common]
    exact h.of_adj i j (e.map_rel_iff.mp hvw)
  · intro v w hne hvw
    obtain ⟨i, rfl⟩ := e.surjective v
    obtain ⟨j, rfl⟩ := e.surjective w
    rw [common]
    exact h.of_not_adj (fun he => hne (congrArg e he))
      (fun he => hvw (e.map_rel_iff.mpr he))

end SimpleGraph.Iso

namespace Computations

/-- Count a predicate by filtering a complete list, rather than evaluating sets of real roots. -/
theorem card_subtype_fin_eq {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Fintype.card {i // p i} = ((List.finRange n).filter (fun i => decide (p i))).length := by
  rw [Fintype.card_subtype, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange n).filter (fun i => decide (p i)))]
  simp

/-- Degree and common-neighbor checks for a finite adjacency table. -/
def checkSRG (n k l m : ℕ) (A : IntMatrix) : Bool :=
  (List.finRange n).all fun (i : Fin n) =>
    (((List.finRange n).filter (fun (j : Fin n) => decide (entry A i j = 1))).length == k) &&
    (List.finRange n).all fun (j : Fin n) =>
      i == j ||
      (((List.finRange n).filter (fun (z : Fin n) =>
        decide (entry A i z = 1 ∧ entry A j z = 1))).length ==
        if entry A i j == 1 then l else m)

/-- The list checker certifies Mathlib's strongly regular graph predicate. -/
theorem checkSRG_sound {n k l m : ℕ} {A : IntMatrix}
    (hA : checkAdjacency n A = true) (h : checkSRG n k l m A = true) :
    (graphOfMatrix hA).IsSRGWith n k l m := by
  have rows (i : Fin n) := List.all_eq_true.mp h i (List.mem_finRange i)
  have deg (i : Fin n) : (graphOfMatrix hA).degree i = k := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, card_subtype_fin_eq]
    simpa [graphOfMatrix] using (Bool.and_eq_true_iff.mp (rows i)).1
  have common (i j : Fin n) (hne : i ≠ j) :
      Fintype.card ((graphOfMatrix hA).commonNeighbors i j) =
        if entry A i j = 1 then l else m := by
    have hij := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (rows i)).2 j
      (List.mem_finRange j)
    rw [card_subtype_fin_eq]
    simpa [SimpleGraph.mem_commonNeighbors, graphOfMatrix, hne] using hij
  refine ⟨Fintype.card_fin n, deg, ?_, ?_⟩
  · intro i j hij
    simpa [show entry A i j = 1 from hij] using common i j (SimpleGraph.Adj.ne hij)
  · intro i j hne hij
    simpa [show entry A i j ≠ 1 from hij] using common i j hne

end Computations
