/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Pairs
import LineGraphs.Computations.Checkers

/-!
# C16: a Boolean checker for Hypothesis 6.1

All executable operations use integer row lists. Checking only increasing pairs saves a factor
of four; the soundness proof uses the symmetry of agreement to cover every ordered quadruple.
-/

open scoped BigOperators

namespace Computations.C16

/-- An executable agreement count, with the same zero-padded lookup as `toMatrix`. -/
def agreementCount (n : ℕ) (A : IntMatrix) (i j k l : ℕ) : ℕ :=
  (List.ofFn fun c : Fin n ↦
    if entry A i c = entry A j c ∧ entry A j c = entry A k c ∧
      entry A k c = entry A l c then 1 else 0).sum

/-- The integer test for `8 agr ∈ {n,n-x,n+x}`. -/
def checkAgreementAt (n x : ℕ) (A : IntMatrix) (i j k l : ℕ) : Bool :=
  let a : ℤ := 8 * agreementCount n A i j k l
  a == (n : ℤ) || a == (n : ℤ) - x || a == (n : ℤ) + x

/-- A row of the agreement checker; the first row index can be chunked independently. -/
def checkAgreementRow (n x : ℕ) (A : IntMatrix) (i : ℕ) : Bool :=
  (List.range n).all fun j ↦ if i < j then
    (List.range n).all fun k ↦ if i != k && j != k then
      (List.range n).all fun l ↦ if k < l ∧ i ≠ l ∧ j ≠ l then
        checkAgreementAt n x A i j k l else true
    else true
  else true

/-- Check the exact square shape and all four-row agreements. -/
def checkFourRowAgreement (n x : ℕ) (A : IntMatrix) : Bool :=
  checkShape n A && (List.range n).all (checkAgreementRow n x A)

/-- The executable count agrees with blueprint Definition `def:6-pairs`. -/
theorem agreementCount_eq (n : ℕ) (A : IntMatrix) (i j k l : Fin n) :
    agreementCount n A i j k l =
      (toMatrix (R := ℤ) n A).fourRowAgreeCount i j k l := by
  simp [agreementCount, List.sum_ofFn, Matrix.fourRowAgreeCount, toMatrix,
    Finset.sum_boole]
  rfl

/-- Agreement is invariant under swapping the first two rows. -/
theorem agreement_swap_first {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j k l : Fin n) :
    H.fourRowAgreeCount i j k l = H.fourRowAgreeCount j i k l := by
  unfold Matrix.fourRowAgreeCount
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩
  · exact ⟨h₁.symm, h₁.trans h₂, h₃⟩
  · exact ⟨h₁.symm, h₁.trans h₂, h₃⟩

/-- Agreement is invariant under swapping the last two rows. -/
theorem agreement_swap_last {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j k l : Fin n) :
    H.fourRowAgreeCount i j k l = H.fourRowAgreeCount i j l k := by
  unfold Matrix.fourRowAgreeCount
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩
  · exact ⟨h₁, h₂.trans h₃, h₃.symm⟩
  · exact ⟨h₁, h₂.trans h₃, h₃.symm⟩

/-- Soundness for increasing pairs, directly from the Boolean loops. -/
theorem checkAgreementRow_sound {n x : ℕ} {A : IntMatrix} {i : Fin n}
    (h : checkAgreementRow n x A i = true) (j k l : Fin n)
    (hij : i < j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k < l) :
    (8 * ((toMatrix (R := ℤ) n A).fourRowAgreeCount i j k l : ℤ)) ∈
      ({(n : ℤ), (n : ℤ) - x, (n : ℤ) + x} : Set ℤ) := by
  have hj := List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt)
  have hj' : ((List.range n).all fun k ↦ if i.val != k && j.val != k then
      (List.range n).all fun l ↦ if k < l ∧ i.val ≠ l ∧ j.val ≠ l then
        checkAgreementAt n x A i j k l else true else true) = true := by
    simpa [show i.val < j.val from hij] using hj
  have hk := List.all_eq_true.mp hj' k.val (List.mem_range.mpr k.isLt)
  have hik' : i.val ≠ k.val := fun he ↦ hik (Fin.ext he)
  have hjk' : j.val ≠ k.val := fun he ↦ hjk (Fin.ext he)
  have hk' : ((List.range n).all fun l ↦ if k.val < l ∧ i.val ≠ l ∧ j.val ≠ l then
      checkAgreementAt n x A i j k l else true) = true := by
    simpa [hik', hjk'] using hk
  have hl := List.all_eq_true.mp hk' l.val (List.mem_range.mpr l.isLt)
  have hil' : i.val ≠ l.val := fun he ↦ hil (Fin.ext he)
  have hjl' : j.val ≠ l.val := fun he ↦ hjl (Fin.ext he)
  have hl' : checkAgreementAt n x A i j k l = true := by
    simpa [show k.val < l.val from hkl, hil', hjl'] using hl
  simpa [checkAgreementAt, agreementCount_eq, or_assoc] using hl'

/-- Soundness of the C16 list checker for Hypothesis 6.1 of [CGSS]. -/
theorem checkFourRowAgreement_sound {n x : ℕ} {A : IntMatrix}
    (hH : (toMatrix (R := ℤ) n A).IsHadamard) (h : checkFourRowAgreement n x A = true) :
    hH.FourRowAgreement x := by
  have hr := (Bool.and_eq_true_iff.mp h).2
  have hs (i j k l : Fin n) (hij : i < j) (hik : i ≠ k) (hil : i ≠ l)
      (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k < l) :=
    checkAgreementRow_sound (List.all_eq_true.mp hr i.val (List.mem_range.mpr i.isLt))
      j k l hij hik hil hjk hjl hkl
  intro i j k l hij hik hil hjk hjl hkl
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · rcases lt_or_gt_of_ne hkl with hkl' | hkl'
    · exact hs i j k l hij' hik hil hjk hjl hkl'
    · rw [agreement_swap_last]
      exact hs i j l k hij' hil hik hjl hjk hkl'
  · rw [agreement_swap_first]
    rcases lt_or_gt_of_ne hkl with hkl' | hkl'
    · exact hs j i k l hij' hjk hjl hik hil hkl'
    · rw [agreement_swap_last]
      exact hs j i l k hij' hjl hjk hil hik hkl'

end Computations.C16
