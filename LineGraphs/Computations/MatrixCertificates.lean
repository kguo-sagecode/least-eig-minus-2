/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.Checkers
import LineGraphs.Spectral.Basic

/-!
# MatrixCertificates

Factored annihilators and the bridge from integer certificates to the spectral lemmas. -/

namespace Computations

/-- Product of `(A - θ I)` in the order given by the list. -/
def matrixFactors (n : ℕ) (A : IntMatrix) : List ℤ → IntMatrix
  | [] => scalarMatrix n 1
  | θ :: roots => matrixMul n (matrixAdd n A (scalarMatrix n (-θ))) (matrixFactors n A roots)

/-- Check the matrix shape and the vanishing of the factored annihilator. -/
def checkAnnihilator (n : ℕ) (A : IntMatrix) (roots : List ℤ) : Bool :=
  checkShape n A && checkZero (matrixFactors n A roots)

/-- Check the matrix shape and equality with its transpose. -/
def checkSymmetric (n : ℕ) (A : IntMatrix) : Bool :=
  checkShape n A && (List.range n).all (fun i => (List.range n).all (fun j =>
    entry A i j == entry A j i))

theorem checkZero_sound_cast {R : Type*} [Ring R] {A : IntMatrix}
    (h : checkZero A = true) (n : ℕ) : toMatrix (R := R) n A = 0 := by
  have hz := checkZero_sound h n
  ext i j
  have he := congrFun (congrFun hz i) j
  change entry A i j = 0 at he
  change (entry A i j : R) = 0
  simp [he]

private theorem intCast_smul_one {R : Type*} [Ring R] (n : ℕ) (c : ℤ) :
    (c : R) • (1 : Matrix (Fin n) (Fin n) R) = (c : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.intCast_apply, h]

theorem toMatrix_factors {R : Type*} [CommRing R] (n : ℕ) (A : IntMatrix) (roots : List ℤ) :
    toMatrix (R := R) n (matrixFactors n A roots) =
      Polynomial.aeval (toMatrix (R := R) n A)
        ((roots.map fun θ : ℤ => Polynomial.X - Polynomial.C (θ : R)).prod) := by
  induction roots with
  | nil => simp [matrixFactors]
  | cons θ roots ih =>
    simp [matrixFactors, ih, intCast_smul_one, sub_eq_add_neg]

theorem checkAnnihilator_sound {R : Type*} [CommRing R] {n : ℕ} {A : IntMatrix}
    {roots : List ℤ} (h : checkAnnihilator n A roots = true) :
    Polynomial.aeval (toMatrix (R := R) n A)
      ((roots.map fun θ : ℤ => Polynomial.X - Polynomial.C (θ : R)).prod) = 0 := by
  rw [← toMatrix_factors]
  exact checkZero_sound_cast (Bool.and_eq_true_iff.mp h).2 n

theorem checkAnnihilator_sound_ofFn {R : Type*} [CommRing R] {n m : ℕ} {A : IntMatrix}
    (θ : Fin m → ℤ) (h : checkAnnihilator n A (List.ofFn θ) = true) :
    Polynomial.aeval (toMatrix (R := R) n A)
      (∏ i, (Polynomial.X - Polynomial.C (θ i : R))) = 0 := by
  simpa [List.map_ofFn, Function.comp_def, List.prod_ofFn] using
    (checkAnnihilator_sound (R := R) h)

theorem checkSymmetric_sound {n : ℕ} {A : IntMatrix}
    (h : checkSymmetric n A = true) : (toMatrix (R := ℝ) n A).IsHermitian := by
  ext i j
  have he := (Bool.and_eq_true_iff.mp h).2
  have hij : entry A i j = entry A j i := by
    simpa using List.all_eq_true.mp (List.all_eq_true.mp he i.val
      (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt)
  simpa [toMatrix, Matrix.conjTranspose_apply] using congrArg (Int.cast (R := ℝ)) hij.symm

/-- The advertised spectrum follows by checking integer annihilation and integer moments.
The scalar Vandermonde equations are proved separately (usually `norm_num`). -/
theorem multiplicities_eq_of_checks {n m : ℕ} {A : IntMatrix}
    (θ : Fin m → ℤ) (μ : Fin m → ℕ) (moments : Fin m → ℤ)
    (hθ : Function.Injective θ)
    (hs : checkSymmetric n A = true)
    (hp : checkAnnihilator n A (List.ofFn θ) = true)
    (ht : checkTraces n A (List.ofFn fun j => (j.val, moments j)) = true)
    (hm : ∀ j : Fin m, moments j = ∑ i, (μ i : ℤ) * θ i ^ j.val) :
    ∀ i, (toMatrix (R := ℝ) n A).eigenvalueMultiplicity (θ i : ℝ) = μ i := by
  have hi : Function.Injective (fun i => (θ i : ℝ)) := by
    intro i j hij
    exact hθ (Int.cast_injective hij)
  have he := (checkSymmetric_sound hs).multiplicities_eq_of_certificate
    (fun i => (θ i : ℝ)) hi (checkAnnihilator_sound_ofFn θ hp)
    (fun i => (μ i : ℝ)) (fun j => ?_)
  · intro i
    exact_mod_cast he i
  · rw [checkTraces_sound ht (List.mem_ofFn.mpr ⟨j, rfl⟩), hm]
    simp

/-- End-to-end cospectrality from list certificates, with no real arithmetic evaluated. -/
theorem charpoly_eq_of_checks {n n' m : ℕ} {A B : IntMatrix}
    (θ : Fin m → ℤ) (moments : Fin m → ℤ) (hθ : Function.Injective θ)
    (hAs : checkSymmetric n A = true) (hBs : checkSymmetric n' B = true)
    (hAp : checkAnnihilator n A (List.ofFn θ) = true)
    (hBp : checkAnnihilator n' B (List.ofFn θ) = true)
    (hAt : checkTraces n A (List.ofFn fun j => (j.val, moments j)) = true)
    (hBt : checkTraces n' B (List.ofFn fun j => (j.val, moments j)) = true) :
    (toMatrix (R := ℝ) n A).charpoly = (toMatrix (R := ℝ) n' B).charpoly := by
  apply Matrix.IsHermitian.charpoly_eq_of_annihilatingPolynomial_trace (checkSymmetric_sound hAs)
    (checkSymmetric_sound hBs) (fun i => (θ i : ℝ))
    (fun _ _ h => hθ (Int.cast_injective h))
    (checkAnnihilator_sound_ofFn θ hAp) (checkAnnihilator_sound_ofFn θ hBp)
  intro j
  rw [checkTraces_sound hAt (List.mem_ofFn.mpr ⟨j, rfl⟩),
    checkTraces_sound hBt (List.mem_ofFn.mpr ⟨j, rfl⟩)]

end Computations
