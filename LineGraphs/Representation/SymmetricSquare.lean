/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.LineSystem.Models

/-!
# The symmetric square and the order bound

Lemma `lem:4-symsq` and the order bound of Theorem 4.3 of [CGSS].
-/

open scoped RealInnerProductSpace
open Finset

namespace EuclideanSpace

/-- Lemma `lem:4-symsq`, Section 4 of [CGSS]: diagonal and strict upper-triangle
coordinates of the symmetric square. -/
abbrev SymSqIndex (n : ℕ) := Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2}

/-- Lemma `lem:4-symsq`, Section 4 of [CGSS]: the symmetric square, with
off-diagonal coordinates scaled by `√2`. -/
noncomputable def symSq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (SymSqIndex n) :=
  WithLp.toLp 2 fun p ↦ match p with
    | .inl i => v i ^ 2
    | .inr p => Real.sqrt 2 * v p.val.1 * v p.val.2

/-- Lemma `lem:4-symsq`, Section 4 of [CGSS]: the inner product of symmetric
squares is the square of the original inner product. -/
theorem inner_symSq {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) :
    ⟪symSq v, symSq w⟫ = ⟪v, w⟫ ^ 2 := by
  let f := fun i j : Fin n ↦ (w i * v i) * (w j * v j)
  have hs : ∑ i, ∑ j, (if j < i then f i j else 0) =
      ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    simp only [f, mul_comm]
  have he (i j : Fin n) : f i j = (if i = j then f i i else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, h.asymm]
    · simp
    · simp [h, h.ne.symm, h.asymm]
  have htotal : (∑ i, w i * v i) ^ 2 =
      (∑ i, f i i) + 2 * ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [sq, sum_mul_sum]
    change (∑ i, ∑ j, f i j) = _
    calc
      _ = ∑ i, ∑ j, ((if i = j then f i i else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        apply sum_congr rfl
        intro i _
        exact sum_congr rfl (fun j _ ↦ he i j)
      _ = _ := by
        simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
        rw [hs]
        ring
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [htotal]
  simp only [symSq, Fintype.sum_sum_type]
  rw [← Finset.sum_subtype (univ.filter (fun p : Fin n × Fin n ↦ p.1 < p.2))
    (by intro p; simp) (fun p ↦ Real.sqrt 2 * w p.1 * w p.2 *
      (Real.sqrt 2 * v p.1 * v p.2)), sum_filter]
  simp only [Fintype.sum_prod_type]
  congr 1
  · apply sum_congr rfl
    intro i _
    dsimp [f]
    ring
  · rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, ite_true]
      dsimp [f]
      calc
        _ = (Real.sqrt 2) ^ 2 * (w i * v i * (w j * v j)) := by ring
        _ = _ := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · simp [h]

end EuclideanSpace

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {X : SimpleGraph V}
  [DecidableRel X.Adj]

omit [Fintype V] in
/-- Theorem 4.3, steps `s43pd`--`s43one`, of [CGSS]: the symmetric squares
of a representation are linearly independent because their Gram matrix is
`2I` plus the original positive semidefinite Gram matrix. -/
theorem IsRepresentation.linearIndependent_symSq [Finite V] {n : ℕ}
    {x : V → EuclideanSpace ℝ (Fin n)} (hx : X.IsRepresentation x) :
    LinearIndependent ℝ (fun u ↦ EuclideanSpace.symSq (x u)) := by
  let : Fintype V := Fintype.ofFinite V
  have hgram : Matrix.gram ℝ (fun u ↦ EuclideanSpace.symSq (x u)) =
      (2 : ℝ) • (1 : Matrix V V ℝ) + Matrix.gram ℝ x := by
    ext u v
    simp only [Matrix.gram_apply, EuclideanSpace.inner_symSq, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, isRepresentation_iff.mp hx u v]
    split_ifs <;> norm_num
  apply Matrix.linearIndependent_of_posDef_gram
  rw [hgram]
  exact (Matrix.PosDef.one.smul (show (0 : ℝ) < 2 by norm_num)).add_posSemidef
    (Matrix.posSemidef_gram ℝ x)

/-- Theorem 4.3, assertion 1, of [CGSS]: a graph represented in the default
eight-dimensional model of `E₈` has at most 36 vertices. -/
theorem IsRepresentedIn.card_le_36 (hX : X.IsRepresentedIn LineSystem.E₈) :
    Fintype.card V ≤ 36 := by
  obtain ⟨x, hx, _⟩ := hX
  have h := hx.linearIndependent_symSq.fintype_card_le_finrank
  have hc : Fintype.card (EuclideanSpace.SymSqIndex 8) = 36 := by decide +kernel
  simpa only [finrank_euclideanSpace, hc] using h

end SimpleGraph
