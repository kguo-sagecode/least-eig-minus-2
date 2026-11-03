/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.GraphCertificates
import LineGraphs.Computations.SpectrumChecker
import LineGraphs.Computations.SwitchingChecker
import LineGraphs.Computations.SimilarityChecker
import LineGraphs.Computations.PositiveEigenvector
import LineGraphs.Computations.CliqueCertificates
import LineGraphs.Computations.BoundedSearch
import LineGraphs.Computations.E8Data
import LineGraphs.LineSystem.Models

/-!
# Examples

Small end-to-end examples and rejection checks for malformed or incorrect certificates.
These supplement the full E₈ demonstration in `E8.lean`. -/

namespace Computations.Examples

/-- The triangle adjacency matrix. -/
def triangle : IntMatrix := [[0, 1, 1], [1, 0, 1], [1, 1, 0]]

/-- The triangle has eigenvalues two once and minus one twice. -/
def triangleSpectrum : List (ℤ × ℕ) := [(2, 1), (-1, 2)]

theorem triangle_checked : checkSpectrum 3 triangle triangleSpectrum = true := by decide +kernel

theorem triangle_spectrum : (toMatrix (R := ℝ) 3 triangle).spectrumMultiset =
    (triangleSpectrum.map fun x => Multiset.replicate x.2 (x.1 : ℝ)).sum :=
  checkSpectrum_sound triangle_checked

/-- The same identity in Horner coefficient form: `A² - A - 2I = 0`. -/
theorem triangle_polynomial_checked : checkPolynomial 3 triangle [-2, -1, 1] = true := by
  decide +kernel

theorem triangle_polynomial : Polynomial.aeval (toMatrix (R := ℝ) 3 triangle)
    (polynomialOfCoeffs [-2, -1, 1]) = 0 := checkPolynomial_sound_real triangle_polynomial_checked

example : checkSpectrum 3 triangle [(2, 2), (-1, 1)] = false := by decide +kernel
example : checkSpectrum 3 triangle [(2, 1), (-1, 1), (-1, 1)] = false := by decide +kernel
example : checkSpectrum 3 triangle [] = false := by decide +kernel
example : checkSpectrum 0 [] [] = true := by decide +kernel
example : checkSpectrum 2 [[0, 1], [1]] [(1, 1), (-1, 1)] = false := by decide +kernel
example : checkPolynomial 3 triangle [-1, -1, 1] = false := by decide +kernel
example : checkTraces 3 triangle [(0, 3), (1, 0), (2, 6), (3, 6)] = true := by decide +kernel
example : checkTraces 3 triangle [(0, 2)] = false := by decide +kernel

/-- A nontrivial permutation certificate for the three-vertex path. -/
def path : IntMatrix := [[0, 1, 0], [1, 0, 1], [0, 1, 0]]
/-- The three-vertex path after a cyclic relabelling. -/
def relabelledPath : IntMatrix := [[0, 0, 1], [0, 0, 1], [1, 1, 0]]

theorem path_adjacency : checkAdjacency 3 path = true := by decide +kernel
theorem relabelledPath_adjacency : checkAdjacency 3 relabelledPath = true := by decide +kernel
theorem path_iso_checked : checkGraphIso 3 path relabelledPath [1, 2, 0] = true := by decide +kernel

theorem path_iso :
    Nonempty (graphOfMatrix path_adjacency ≃g graphOfMatrix relabelledPath_adjacency) :=
  nonempty_graphOfMatrix_iso path_adjacency relabelledPath_adjacency path_iso_checked

example : checkGraphIso 3 path relabelledPath [1, 1, 0] = false := by decide +kernel
example : checkGraphIso 3 path relabelledPath [1, 3, 0] = false := by decide +kernel
example : checkGraphIso 3 path relabelledPath [0, 1, 2] = false := by decide +kernel
example : checkAdjacency 2 [[1, 1], [1, 0]] = false := by decide +kernel
example : checkAdjacency 2 [[0, 1], [0, 0]] = false := by decide +kernel
example : checkAdjacency 2 [[0, 2], [2, 0]] = false := by decide +kernel

/-- Rectangular vector data, but a square prescribed Gram matrix. -/
theorem gram_checked : checkGram 3 [[2, 0, -2], [0, 2, -2]] [[8, 4], [4, 8]] = true := by
  decide +kernel

/-- Two roots of A₂, using its common integer presentation. -/
def gramIndices (i : Fin 2) : LineSystem.AnIndex 2 :=
  if i = 0 then ⟨(0, 2), by decide⟩ else ⟨(1, 2), by decide⟩

open scoped RealInnerProductSpace in
theorem gram_inner :
    ⟪LineSystem.integerVector 1 (LineSystem.anRoot (gramIndices 0)),
      LineSystem.integerVector 1 (LineSystem.anRoot (gramIndices 1))⟫ = 1 := by
  have hc : checkGram 3
      (List.ofFn fun i : Fin 2 => List.ofFn (LineSystem.anRoot (gramIndices i)))
      [[2, 1], [1, 2]] = true := by decide +kernel
  have h := (LineSystem.An.integerModel 2).inner_eq_of_checkGram gramIndices hc 0 1
  norm_num [toMatrix, entry] at h
  change ⟪LineSystem.integerVector 1 (LineSystem.anRoot (gramIndices 0)),
    LineSystem.integerVector 1 (LineSystem.anRoot (gramIndices 1))⟫ = (1 : ℝ) * 1 at h
  simpa only [one_mul] using h

example : checkGram 3 [[2, 0], [0, 2, -2]] [[8, 4], [4, 8]] = false := by decide +kernel
example : checkGram 3 [[2, 0, -2], [0, 2, -2]] [[8, 5], [4, 8]] = false := by decide +kernel
example : checkStar 2 (-4) (fun _ => false) [[2, 0], [-2, 2]] = false := by decide +kernel

/-- The domain-completeness bridge is necessary to rule out mathematical solutions. -/
theorem bounded_checked : allBox [3, 4] (fun xs => !decide (xs.sum = 10)) = true := by
  decide +kernel

theorem no_bounded_solution :
    ¬ ∃ xs, List.Forall₂ (· < ·) xs [3, 4] ∧ xs.sum = 10 :=
  no_bounded_solution_of_check bounded_checked (fun _ _ h => by simp [h])

example : allBox [3, 4] (fun xs => !decide (xs.sum = 5)) = false := by decide +kernel

/-- Only one chunk demonstrates the dot checker; the model already proves the general bound. -/
theorem e₈_dots_demo :
    (E₈Data.e₈Chunk 0).all (checkDotsRow E₈Data.e₈Allowed E₈Data.e₈Roots) = true := by
  decide +kernel

theorem triangle_adjacency : checkAdjacency 3 triangle = true := by decide +kernel

theorem triangle_graph_spectrum : (graphOfMatrix triangle_adjacency).spectrumMultiset =
    {2} + {-1, -1} := by
  simpa [triangleSpectrum] using spectrum_graphOfMatrix_of_checkSpectrum
    triangle_adjacency triangle_checked

/-- Switching at one vertex of the triangle leaves an isolated vertex and an edge. -/
def switchedTriangle : IntMatrix := [[0, 0, 0], [0, 0, 1], [0, 1, 0]]

theorem switchedTriangle_adjacency : checkAdjacency 3 switchedTriangle = true := by decide +kernel

theorem triangle_switch_checked :
    checkSeidelSwitching 3 triangle switchedTriangle [-1, 1, 1] [0, 1, 2] = true := by
  decide +kernel

theorem triangle_switch : (graphOfMatrix triangle_adjacency).IsSwitchingEquivalent
    (graphOfMatrix switchedTriangle_adjacency) :=
  checkSeidelSwitching_sound triangle_adjacency switchedTriangle_adjacency triangle_switch_checked

example : checkSwitching 1 [[0]] [[0]] [0] [0] = false := by decide +kernel
example : checkSwitching 1 [[0]] [[0]] [] [0] = false := by decide +kernel
example : checkSwitching 2 [[0, 1], [1, 0]] [[0, 1], [1, 0]] [1, 1] [0, 0] = false := by
  decide +kernel

/-- An intertwiner with denominator two exercises scaled inverses. -/
theorem path_similarity_checked : checkSimilarity 3 path relabelledPath
    [[0, 0, 2], [2, 0, 0], [0, 2, 0]] [[0, 1, 0], [0, 0, 1], [1, 0, 0]] 2 = true := by
  decide +kernel

theorem path_cospectral : (graphOfMatrix path_adjacency).Cospectral
    (graphOfMatrix relabelledPath_adjacency) :=
  cospectral_graphOfMatrix_of_checkSimilarity path_adjacency relabelledPath_adjacency
    path_similarity_checked

example : checkSimilarity 1 [[0]] [[1]] [[0]] [[0]] 0 = false := by decide +kernel
example : checkSimilarity 1 [[0]] [[1]] [[1]] [[1]] 1 = false := by decide +kernel
example : checkSimilarity 1 [[0]] [[0]] [[1]] [[2]] 1 = false := by decide +kernel
example : checkSimilarity 1 [[0, 0]] [[0]] [[1]] [[1]] 1 = false := by decide +kernel

theorem triangle_positive_checked : checkPositiveEigenvector 3 triangle [1, 1, 1] 2 = true := by
  decide +kernel

theorem triangle_largestEigenvalue :
    (checkPositiveEigenvector_hermitian triangle_positive_checked).largestEigenvalue = 2 :=
  checkPositiveEigenvector_sound triangle_positive_checked

example : checkPositiveEigenvector 0 [] [] 0 = false := by decide +kernel
example : checkPositiveEigenvector 1 [[-1]] [1] (-1) = false := by decide +kernel
example : checkPositiveEigenvector 3 triangle [0, 0, 0] 2 = false := by decide +kernel
example : checkPositiveEigenvector 3 triangle [1, 1] 2 = false := by decide +kernel
example : checkPositiveEigenvector 3 triangle [1, 1, 1] 3 = false := by decide +kernel
example : checkPositiveEigenvector 2 [[0, 1], [0, 0]] [1, 1] 0 = false := by decide +kernel

theorem triangle_path_nonisomorphic :
    ¬ Nonempty (graphOfMatrix triangle_adjacency ≃g graphOfMatrix path_adjacency) :=
  checkNonisomorphic_sound triangle_adjacency path_adjacency (by decide +kernel :
    checkNonisomorphic 3 3 triangle path = true)

example : checkNonisomorphic 3 2 path relabelledPath = false := by decide +kernel
example : checkDots 3 [0] [[0, 0]] = false := by decide +kernel
example : checkStar 3 (-4) (fun _ => true) [[0, 0]] = false := by decide +kernel
example : allBox [] (fun _ => true) = true := by decide +kernel
example : allBox [0, 37] (fun _ => false) = true := by decide +kernel

end Computations.Examples
