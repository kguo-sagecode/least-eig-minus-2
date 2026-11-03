/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Remark512

/-!
# Resolutions and their disjointness graphs

Example 5.13 (`ex:5.13`) of [CGSS], steps `s5exclass`–`s5exgram`.
We retain the shared Hall–Connor `Design`; every real incidence matrix below is
`Design.realIncMatrix`, the explicit entrywise cast from its integral matrix.
-/

open Matrix
open scoped BigOperators

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam c : ℕ}

/-- A resolution into labelled parallel classes, assumption 2 of `ex:5.13`,
Example 5.13 of [CGSS]. Each class partitions the point set. -/
structure Resolution (D : Design P B v k b r lam) (c : ℕ) where
  classOf : B → Fin c
  unique_block : ∀ i p, ∃! label, classOf label = i ∧ p ∈ D.block label

attribute [local instance] Classical.propDecidable

/-- The block Gram entries in step `s5exadjd`, Example 5.13 of [CGSS]. -/
theorem transpose_realIncMatrix_mul_apply (D : Design P B v k b r lam) (a d : B) :
    (D.realIncMatrixᵀ * D.realIncMatrix) a d = ((D.block a ∩ D.block d).card : ℝ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, D.realIncMatrix_apply]
  have he (p : P) :
      (if p ∈ D.block a then (1 : ℝ) else 0) * (if p ∈ D.block d then 1 else 0) =
        if p ∈ D.block a ∩ D.block d then 1 else 0 := by
    simp only [Finset.mem_inter]
    split_ifs <;> simp_all
  simp_rw [he]
  have hf : Finset.univ.filter (fun p ↦ p ∈ D.block a ∩ D.block d) =
      D.block a ∩ D.block d := by ext p; simp only [Finset.mem_filter,
        Finset.mem_univ, true_and]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one, hf]

/-- Distinct blocks meet in at most one point (`s5exadj01`, Example 5.13 of [CGSS]). -/
theorem inter_card_le_one_of_lam_eq_one (D : Design P B v k b r 1)
    {a d : B} (had : a ≠ d) : (D.block a ∩ D.block d).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  have he := D.card_blocksThroughPair p q hpq
  have hle := Finset.card_le_one.mp (le_of_eq he)
  exact had (hle a (by simp [(Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hq).1])
    d (by simp [(Finset.mem_inter.mp hp).2, (Finset.mem_inter.mp hq).2]))

namespace Resolution

variable {D : Design P B v k b r lam} (R : D.Resolution c)

/-- The class-indicator matrix (`s5exclass`, Example 5.13 of [CGSS]); its rows are `cᵢᵀ`. -/
noncomputable def classMatrix : Matrix (Fin c) B ℝ :=
  fun i label ↦ if R.classOf label = i then 1 else 0

/-- The graph `H` in assumption 3 of `ex:5.13`, Example 5.13 of [CGSS]. -/
def graph : SimpleGraph B where
  Adj a d := a ≠ d ∧ Disjoint (D.block a) (D.block d) ∧ R.classOf a ≠ R.classOf d
  symm.symm := by rintro a d ⟨hne, hd, hc⟩; exact ⟨hne.symm, hd.symm, hc.symm⟩
  loopless.irrefl := by rintro a ⟨hne, _⟩; exact hne rfl

/-- Distinct blocks in one class are disjoint (`s5exadjc`, Example 5.13 of [CGSS]). -/
theorem disjoint_of_classOf_eq {a d : B} (had : a ≠ d) (he : R.classOf a = R.classOf d) :
    Disjoint (D.block a) (D.block d) := by
  apply Finset.disjoint_left.mpr
  intro p hpa hpd
  obtain ⟨label, _, hu⟩ := R.unique_block (R.classOf a) p
  exact had ((hu a ⟨rfl, hpa⟩).trans (hu d ⟨he.symm, hpd⟩).symm)

/-- A point occurs once in each class (`s5exclass`, Example 5.13 of [CGSS]). -/
theorem card_blocksThrough_class (i : Fin c) (p : P) :
    (Finset.univ.filter (fun a ↦ R.classOf a = i ∧ p ∈ D.block a)).card = 1 := by
  obtain ⟨a, ha, hu⟩ := R.unique_block i p
  apply Finset.card_eq_one.mpr
  refine ⟨a, Finset.ext fun d ↦ ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hd ↦ hu d hd, fun hd ↦ hd ▸ ha⟩

/-- Counting the partition of points (`s5exclass`, Example 5.13 of [CGSS]). -/
theorem card_class_mul (i : Fin c) :
    (Finset.univ.filter (fun a ↦ R.classOf a = i)).card * k = v := by
  have he := Finset.card_mul_eq_card_mul (fun p a ↦ p ∈ D.block a)
    (s := Finset.univ) (t := Finset.univ.filter (fun a ↦ R.classOf a = i))
    (m := 1) (n := k) (fun p _ ↦ ?_) (fun a _ ↦ ?_)
  · simpa only [Finset.card_univ, D.card_points, mul_one] using he.symm
  · simpa [Finset.bipartiteAbove, Finset.filter_filter] using R.card_blocksThrough_class i p
  · simpa [Finset.bipartiteBelow] using D.card_block a

/-- The identities `N'cᵢ = j` (`s5exclass`, Example 5.13 of [CGSS]). -/
theorem realIncMatrix_mul_classMatrix_transpose :
    D.realIncMatrix * R.classMatrixᵀ = Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  ext p i
  have he := R.card_blocksThrough_class i p
  have heR : ((Finset.univ.filter
      (fun a ↦ R.classOf a = i ∧ p ∈ D.block a)).card : ℝ) = 1 := by exact_mod_cast he
  simp only [Matrix.mul_apply, Matrix.transpose_apply, classMatrix,
    D.realIncMatrix_apply, Matrix.of_apply]
  have hentry (a : B) :
      (if p ∈ D.block a then (1 : ℝ) else 0) * (if R.classOf a = i then 1 else 0) =
        if R.classOf a = i ∧ p ∈ D.block a then 1 else 0 := by
    split_ifs <;> simp_all
  simp_rw [hentry]
  simpa using heR

/-- Every block belongs to exactly one class (`s5exclass`, Example 5.13 of [CGSS]). -/
theorem sum_classMatrix (a : B) : ∑ i, R.classMatrix i a = 1 := by
  simp [classMatrix]

/-- The class Gram matrix including its diagonal (`s5exclass`, Example 5.13 of [CGSS]). -/
theorem transpose_classMatrix_mul_apply (a d : B) :
    (R.classMatrixᵀ * R.classMatrix) a d = if R.classOf a = R.classOf d then 1 else 0 := by
  simp [Matrix.mul_apply, classMatrix, eq_comm]

end Resolution

namespace Resolution

variable {D : Design P B v k b r 1} (R : D.Resolution c)

/-- The adjacency identity in `s5exadj`, Example 5.13 of [CGSS]. The matrix
`classMatrixᵀ * classMatrix` is `I + R` in the blueprint's notation. -/
theorem adjMatrix_graph :
    R.graph.adjMatrix ℝ = Matrix.of (fun _ _ ↦ (1 : ℝ)) -
      R.classMatrixᵀ * R.classMatrix - D.realIncMatrixᵀ * D.realIncMatrix +
        (k : ℝ) • (1 : Matrix B B ℝ) := by
  ext a d
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.sub_apply,
    R.transpose_classMatrix_mul_apply, D.transpose_realIncMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix, graph, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases had : a = d
  · subst d
    simp [D.card_block]
  · by_cases hc : R.classOf a = R.classOf d
    · have hd := R.disjoint_of_classOf_eq had hc
      simp [had, hc, Finset.disjoint_iff_inter_eq_empty.mp hd]
    · by_cases hd : Disjoint (D.block a) (D.block d)
      · simp [had, hc, hd, Finset.disjoint_iff_inter_eq_empty.mp hd]
      · have hn : (D.block a ∩ D.block d).card ≠ 0 := by
          simpa [Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty] using hd
        have he : (D.block a ∩ D.block d).card = 1 := by
          have := D.inter_card_le_one_of_lam_eq_one had
          omega
        simp [had, hc, hd, he]

end Resolution

namespace Resolution

variable {k : ℕ}
  {D : Design P B (k * (2 * k - 1)) k (4 * k ^ 2 - 1) (2 * k + 1) 1}
  (R : D.Resolution (2 * k + 1))

/-- The class size in `s5exclass`, Example 5.13 of [CGSS]. -/
theorem card_class (i : Fin (2 * k + 1)) :
    (Finset.univ.filter (fun a ↦ R.classOf a = i)).card = 2 * k - 1 := by
  have he := R.card_class_mul i
  have hk := D.one_lt_k
  nlinarith

/-- Orthogonality and norms of class indicators (`s5exclass` and `s5exd12`,
Example 5.13 of [CGSS]). -/
theorem classMatrix_mul_transpose :
    R.classMatrix * R.classMatrixᵀ = ((2 * k - 1 : ℕ) : ℝ) • 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, classMatrix,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    have he (a : B) :
        (if R.classOf a = i then (1 : ℝ) else 0) *
          (if R.classOf a = i then 1 else 0) = if R.classOf a = i then 1 else 0 := by
      split_ifs <;> norm_num
    simp_rw [he]
    simpa using congrArg (fun n : ℕ ↦ (n : ℝ)) (R.card_class i)
  · have he (a : B) :
        (if R.classOf a = i then (1 : ℝ) else 0) *
          (if R.classOf a = j then 1 else 0) = 0 := by
      split_ifs <;> simp_all
    simp [he, hij]

/-- The point Gram identity in `s5exgram`, Example 5.13 of [CGSS]. -/
theorem realIncMatrix_mul_transpose :
    D.realIncMatrix * D.realIncMatrixᵀ = (2 * k : ℝ) • 1 +
      Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
  rw [D.incMatrix_mul_transpose]
  simp

/-- Full row rank in `s5exgram` and `s5exd3k`, Example 5.13 of [CGSS]. -/
theorem rank_realIncMatrix : D.realIncMatrix.rank = k * (2 * k - 1) :=
  D.rank_realIncMatrix_of_lam_lt_r (by have := D.one_lt_k; omega)

end Resolution
end Design
