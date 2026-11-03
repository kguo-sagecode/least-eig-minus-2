/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.MatrixCertificates
import LineGraphs.Computations.RootTables
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# GraphCertificates

Decoding a checked zero-one adjacency matrix into a `SimpleGraph`. -/

namespace Computations

/-- Shape, symmetry, zero diagonal, and zero-one entries. -/
def checkAdjacency (n : ℕ) (A : IntMatrix) : Bool :=
  checkSymmetric n A && (List.range n).all (fun i =>
    entry A i i == 0 && (List.range n).all (fun j =>
      entry A i j == 0 || entry A i j == 1))

theorem checkAdjacency_symmetric {n : ℕ} {A : IntMatrix}
    (h : checkAdjacency n A = true) (i j : Fin n) : entry A i j = entry A j i := by
  have he := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  simpa using List.all_eq_true.mp (List.all_eq_true.mp he i.val
    (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt)

theorem checkAdjacency_diagonal {n : ℕ} {A : IntMatrix}
    (h : checkAdjacency n A = true) (i : Fin n) : entry A i i = 0 := by
  have he := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 i.val
    (List.mem_range.mpr i.isLt)
  simpa using (Bool.and_eq_true_iff.mp he).1

theorem checkAdjacency_entries {n : ℕ} {A : IntMatrix}
    (h : checkAdjacency n A = true) (i j : Fin n) : entry A i j = 0 ∨ entry A i j = 1 := by
  have he := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp h).2 i.val (List.mem_range.mpr i.isLt))).2
  simpa using List.all_eq_true.mp he j.val (List.mem_range.mpr j.isLt)

/-- A graph whose adjacency relation is the checked integer matrix. -/
def graphOfMatrix {n : ℕ} {A : IntMatrix} (h : checkAdjacency n A = true) :
    SimpleGraph (Fin n) where
  Adj i j := entry A i j = 1
  symm.symm i j hij := (checkAdjacency_symmetric h i j) ▸ hij
  loopless.irrefl i hii := by simp [checkAdjacency_diagonal h i] at hii

instance {n : ℕ} {A : IntMatrix} (h : checkAdjacency n A = true) :
    DecidableRel (graphOfMatrix h).Adj :=
  fun i j => inferInstanceAs (Decidable (entry A i j = 1))

/-- The decoded graph has exactly the checked adjacency matrix over any ring. -/
theorem adjMatrix_graphOfMatrix {R : Type*} [Ring R] {n : ℕ} {A : IntMatrix}
    (h : checkAdjacency n A = true) : (graphOfMatrix h).adjMatrix R = toMatrix n A := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  change (if entry A i j = 1 then 1 else 0 : R) = (entry A i j : R)
  rcases checkAdjacency_entries h i j with he | he <;> simp [he]

/-- A labelled adjacency table identifies its decoded graph with the original graph. -/
def graphOfMatrixIso {n : ℕ} {A : IntMatrix} (h : checkAdjacency n A = true)
    {V : Type*} (G : SimpleGraph V) (label : Fin n ≃ V)
    (hG : ∀ i j, G.Adj (label i) (label j) ↔ entry A i j = 1) : graphOfMatrix h ≃g G where
  toEquiv := label
  map_rel_iff' := by
    intro i j
    exact hG i j

/-- Isomorphism certificates transfer to any supplied labellings of the vertex types. -/
theorem nonempty_iso_of_checkGraphIso' {n : ℕ} {A B : IntMatrix} {p : List ℕ}
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (v : Fin n ≃ V) (w : Fin n ≃ W)
    (hG : ∀ i j, G.Adj (v i) (v j) ↔ entry A i j = 1)
    (hH : ∀ i j, H.Adj (w i) (w j) ↔ entry B i j = 1)
    (h : checkGraphIso n A B p = true) : Nonempty (G ≃g H) := by
  obtain ⟨e, _, he⟩ := checkGraphIso_sound h
  refine ⟨{ toEquiv := v.symm.trans (e.trans w), map_rel_iff' := ?_ }⟩
  intro x y
  obtain ⟨i, rfl⟩ := v.surjective x
  obtain ⟨j, rfl⟩ := v.surjective y
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, hG, hH, toMatrix, Int.cast_id] using
    (congrArg (· = 1) (he i j)).symm |> Iff.of_eq

/-- An integer-dot adjacency table, with diagonal entries explicitly zero. -/
def dotAdjacency (n : ℕ) (target : ℤ) (vs : List IntVector) : IntMatrix :=
  tabulate n fun i j =>
    if i = j then 0 else if dot (vs[i.val]?.getD []) (vs[j.val]?.getD []) = target then 1 else 0

/-- The list permutation really is an isomorphism of the decoded graphs. -/
theorem nonempty_graphOfMatrix_iso {n : ℕ} {A B : IntMatrix} {p : List ℕ}
    (hA : checkAdjacency n A = true) (hB : checkAdjacency n B = true)
    (h : checkGraphIso n A B p = true) : Nonempty (graphOfMatrix hA ≃g graphOfMatrix hB) :=
  nonempty_iso_of_checkGraphIso _ _ (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) h

end Computations

namespace LineSystem.IntegerModel

open Computations
open scoped RealInnerProductSpace

/-- Graphs on roots use the integer model's normalization and the same list dot product. -/
theorem adjMatrix_eq_dotAdjacency {d n : ℕ}
    {S : LineSystem (EuclideanSpace ℝ (Fin d))} (M : IntegerModel S)
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : Fin n ≃ V) (a : Fin n → M.ι)
    (hG : ∀ i j, G.Adj (label i) (label j) ↔ i ≠ j ∧
      ⟪integerVector M.c (M.v (a i)), integerVector M.c (M.v (a j))⟫ = 1) :
    (G.adjMatrix ℝ).submatrix label label =
      toMatrix n (dotAdjacency n M.q (List.ofFn fun i => List.ofFn (M.v (a i)))) := by
  have hi (i j : Fin n) :
      ⟪integerVector M.c (M.v (a i)), integerVector M.c (M.v (a j))⟫ = 1 ↔
        M.v (a i) ⬝ᵥ M.v (a j) = M.q := by
    rw [inner_integerVector]
    constructor
    · intro h
      apply Int.cast_injective (α := ℝ)
      apply mul_left_cancel₀ (mul_ne_zero M.c_ne_zero M.c_ne_zero)
      exact h.trans M.hc.symm
    · intro h
      simpa only [integerInner, h] using M.hc
  ext i j
  simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, dotAdjacency,
    toMatrix_tabulate, List.getElem?_ofFn, Fin.isLt, dite_true, Option.getD_some,
    Fin.eta, dot_ofFn, hG, hi]
  by_cases h : i = j <;> simp [h]

end LineSystem.IntegerModel
