/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.GraphCertificates
import LineGraphs.Spectral.PositiveVector

/-!
# Positive integer eigenvector certificates

The checker includes nonemptiness, symmetry, nonnegativity, dimensions and strict positivity.
-/

namespace Computations

open Matrix

/-- Matrix-vector multiplication with the same zero-padded lookup as `toMatrix`. -/
def matrixVecMul (n : ℕ) (A : IntMatrix) (x : IntVector) : IntVector :=
  List.ofFn fun i : Fin n =>
    dot (List.ofFn fun j : Fin n => entry A i j) (List.ofFn fun j : Fin n => x[j.val]?.getD 0)

/-- Exact checks sufficient to identify the largest eigenvalue. -/
def checkPositiveEigenvector (n : ℕ) (A : IntMatrix) (x : IntVector) (b : ℤ) : Bool :=
  decide (0 < n) && checkSymmetric n A && A.all (fun r => r.all (fun z => decide (0 ≤ z))) &&
  (x.length == n) && x.all (fun z => decide (0 < z)) && (matrixVecMul n A x == x.map (b * ·))

theorem checkPositiveEigenvector_pos {n : ℕ} {A : IntMatrix} {x : IntVector} {b : ℤ}
    (h : checkPositiveEigenvector n A x b = true) : 0 < n := by
  simp only [checkPositiveEigenvector, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact h.1.1.1.1.1

theorem checkPositiveEigenvector_hermitian {n : ℕ} {A : IntMatrix} {x : IntVector} {b : ℤ}
    (h : checkPositiveEigenvector n A x b = true) : (toMatrix (R := ℝ) n A).IsHermitian := by
  simp only [checkPositiveEigenvector, Bool.and_eq_true_iff] at h
  exact checkSymmetric_sound h.1.1.1.1.2

/-- All the real hypotheses follow from the integer checks, without real-number evaluation. -/
theorem checkPositiveEigenvector_spec {n : ℕ} {A : IntMatrix} {x : IntVector} {b : ℤ}
    (h : checkPositiveEigenvector n A x b = true) :
    let y : Fin n → ℝ := fun i => (x[i.val]?.getD 0 : ℝ)
    (∀ i j, 0 ≤ toMatrix (R := ℝ) n A i j) ∧ (∀ i, 0 < y i) ∧
      toMatrix n A *ᵥ y = (b : ℝ) • y := by
  obtain ⟨⟨⟨⟨⟨_, _⟩, hA⟩, hl⟩, hx⟩, he⟩ := by
    simpa only [checkPositiveEigenvector, Bool.and_eq_true_iff, List.all_eq_true,
      decide_eq_true_eq, beq_iff_eq] using h
  have hn (i : Fin n) : i.val < x.length := hl ▸ i.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    change (0 : ℝ) ≤ (entry A i j : ℝ)
    suffices 0 ≤ entry A i j by exact_mod_cast this
    unfold entry
    cases hr : A[i.val]? with
    | none => simp
    | some r =>
      cases hz : r[j.val]? with
      | none => simp [hz]
      | some z => simpa [hz] using hA r (List.mem_of_getElem? hr) z (List.mem_of_getElem? hz)
  · intro i
    have hi := hx x[i.val] (List.getElem_mem (hn i))
    dsimp
    simpa only [List.getElem?_eq_getElem (hn i), Option.getD_some, Int.cast_pos] using hi
  · funext i
    have hi := congrArg (fun v : IntVector => v[i.val]?.getD 0) he
    simp only [matrixVecMul, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some,
      dot_ofFn, List.getElem?_map, List.getElem?_eq_getElem (hn i),
      Option.map_some] at hi
    change ∑ j : Fin n, (entry A i j : ℝ) * (x[j.val]?.getD 0 : ℝ) =
      (b : ℝ) * (x[i.val]?.getD 0 : ℝ)
    rw [List.getElem?_eq_getElem (hn i), Option.getD_some]
    exact_mod_cast hi

/-- The proposed integer is the largest real eigenvalue, with nonemptiness supplied by the check. -/
theorem checkPositiveEigenvector_sound {n : ℕ} {A : IntMatrix} {x : IntVector} {b : ℤ}
    (h : checkPositiveEigenvector n A x b = true) :
    let : Nonempty (Fin n) := ⟨⟨0, checkPositiveEigenvector_pos h⟩⟩
    (checkPositiveEigenvector_hermitian h).largestEigenvalue = (b : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, checkPositiveEigenvector_pos h⟩⟩
  obtain ⟨hA, hx, he⟩ := checkPositiveEigenvector_spec h
  exact (checkPositiveEigenvector_hermitian h).largestEigenvalue_eq_of_pos_eigenvector hA hx he

/-- The adjacency guard turns the matrix conclusion into a largest eigenvalue of a graph. -/
theorem largestEigenvalue_graphOfMatrix_of_checkPositiveEigenvector
    {n : ℕ} {A : IntMatrix} {x : IntVector} {b : ℤ}
    (hA : checkAdjacency n A = true) (h : checkPositiveEigenvector n A x b = true) :
    letI : Nonempty (Fin n) := ⟨⟨0, checkPositiveEigenvector_pos h⟩⟩
    (graphOfMatrix hA).largestEigenvalue = (b : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, checkPositiveEigenvector_pos h⟩⟩
  simpa only [SimpleGraph.largestEigenvalue, adjMatrix_graphOfMatrix] using
    checkPositiveEigenvector_sound h

end Computations

/-- Compatibility name from the spectral toolkit. -/
alias Matrix.positiveEigenvectorCertificate_sound := Computations.checkPositiveEigenvector_sound
