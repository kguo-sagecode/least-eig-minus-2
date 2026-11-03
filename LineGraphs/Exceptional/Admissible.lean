/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Extension

/-! # Admissible vectors and neighbour sets

Lemma `lem:admissible` (Lemma 3.5) of [Exc].
-/

open Matrix

namespace Matrix

variable {V : Type*} [DecidableEq V]

-- Lemma 3.5 [Exc]
/-- The basis columns satisfy `C(·,b)=D e_b`, in the proof of `lem:admissible`
(Lemma 3.5) of [Exc]. -/
theorem certificateCoordinates_apply_basis (M : Matrix V V ℤ) (B : Finset V) (b c : B) :
    M.certificateCoordinates B b c = M.certificateDet B * (if b = c then 1 else 0) := by
  change ((M.certificateMatrix B).adjugate * M.certificateMatrix B) b c = _
  rw [adjugate_mul]
  simp only [certificateDet, smul_apply, smul_eq_mul, one_apply]

-- Lemma 3.5 [Exc]
/-- The basis entries of `sᵀ C` recover `D s`, in `lem:admissible`
(Lemma 3.5) of [Exc]. -/
theorem vecMul_certificateCoordinates_basis (M : Matrix V V ℤ) (B : Finset V)
    (s : B → ℤ) (b : B) :
    (s ᵥ* M.certificateCoordinates B) b = M.certificateDet B * s b := by
  simp [vecMul, dotProduct, certificateCoordinates_apply_basis, mul_ite, mul_comm]

-- Lemma 3.5 [Exc]
/-- A basis vertex belongs to `N_s` exactly when its coordinate is one, as used in
`lem:admissible` (Lemma 3.5) of [Exc]. -/
theorem mem_admissibleNeighbors_basis_iff (M : Matrix V V ℤ) (B : Finset V)
    (hD : M.certificateDet B ≠ 0) (s : B → ℤ) (b : B) :
    (b : V) ∈ M.admissibleNeighbors B s ↔ s b = 1 := by
  change (s ᵥ* M.certificateCoordinates B) b = M.certificateDet B ↔ _
  rw [vecMul_certificateCoordinates_basis]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (by simpa only [mul_one] using h)
  · rintro h
    simp [h]

-- Lemma 3.5 [Exc]
/-- The zero vector has empty neighbour set in `lem:admissible` (Lemma 3.5) of [Exc]. -/
theorem admissibleNeighbors_zero (M : Matrix V V ℤ) (B : Finset V)
    (hD : M.certificateDet B ≠ 0) : M.admissibleNeighbors B 0 = ∅ := by
  ext u
  simp [admissibleNeighbors, hD.symm]

-- Lemma 3.5 [Exc]
/-- Nonzero admissible vectors give nonempty sets in `lem:admissible`
(Lemma 3.5) of [Exc]. -/
theorem IsAdmissible.neighbors_nonempty {M : Matrix V V ℤ} {B : Finset V} {s : B → ℤ}
    (hs : M.IsAdmissible B s) (hD : M.certificateDet B ≠ 0) (hne : s ≠ 0) :
    (M.admissibleNeighbors B s).Nonempty := by
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hne
  refine ⟨b, (mem_admissibleNeighbors_basis_iff M B hD s b).mpr ?_⟩
  exact (hs.1 b).resolve_left hb

-- Lemma 3.5 [Exc]
/-- The indicator of `N_s ∩ B` is `s`, in `lem:admissible` (Lemma 3.5) of [Exc].
Only the zero-or-one condition is needed for this recovery. -/
theorem certificateIndicator_admissibleNeighbors (M : Matrix V V ℤ) (B : Finset V)
    (hD : M.certificateDet B ≠ 0) (s : B → ℤ) (hs : ∀ b, s b = 0 ∨ s b = 1) :
    SimpleGraph.certificateIndicator (M.admissibleNeighbors B s) B = s := by
  classical
  funext b
  rcases hs b with hb | hb <;>
    simp [SimpleGraph.certificateIndicator, mem_admissibleNeighbors_basis_iff M B hD, hb]

-- Lemma 3.5 [Exc]
/-- Distinct zero-or-one vectors give distinct neighbour sets, in `lem:admissible`
(Lemma 3.5) of [Exc]. In particular, this holds for admissible vectors. -/
theorem admissibleNeighbors_inj (M : Matrix V V ℤ) (B : Finset V)
    (hD : M.certificateDet B ≠ 0) {s t : B → ℤ}
    (hs : ∀ b, s b = 0 ∨ s b = 1) (ht : ∀ b, t b = 0 ∨ t b = 1) :
    M.admissibleNeighbors B s = M.admissibleNeighbors B t ↔ s = t := by
  constructor
  · intro h
    rw [← certificateIndicator_admissibleNeighbors M B hD s hs, h,
      certificateIndicator_admissibleNeighbors M B hD t ht]
  · rintro rfl
    rfl

end Matrix

namespace SimpleGraph

variable {V : Type*} [Finite V] [DecidableEq V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {B : Finset V}

-- Lemma 3.5 [Exc]
/-- The forward construction in `lem:admissible` (Lemma 3.5) of [Exc]: each nonzero
admissible vector gives an extension represented in `E₈`. -/
theorem isRepresentedIn_adjoinVertex_admissibleNeighbors (hX : X.Connected)
    (hB : X.integralGramMatrix.IsGramCertificate B) (hr : B.card ≤ 8) {s : B → ℤ}
    (hs : X.integralGramMatrix.IsAdmissible B s) (hne : s ≠ 0) :
    (X.adjoinVertex (X.integralGramMatrix.admissibleNeighbors B s)).IsRepresentedIn
      LineSystem.E₈ := by
  classical
  have hD := (hB.det_pos X.integralGramMatrix_isSymm).ne'
  have hN := hs.neighbors_nonempty hD hne
  apply (isRepresentedIn_adjoinVertex_iff hX hB hr hN).mpr
  rw [certificateIndicator_admissibleNeighbors _ _ hD s hs.1]
  refine ⟨?_, hs.2.2⟩
  intro u
  rcases hs.2.1 u with hu | hu
  · simp [admissibleNeighbors, hu, hD.symm]
  · simp [admissibleNeighbors, hu]

-- Lemma 3.5 [Exc]
/-- The recovery assertion in `lem:admissible` (Lemma 3.5) of [Exc]: an extension
represented in `E₈` yields a nonzero admissible indicator and recovers its neighbour set. -/
theorem admissible_certificateIndicator_of_isRepresentedIn_adjoinVertex (hX : X.Connected)
    (hB : X.integralGramMatrix.IsGramCertificate B) (hr : B.card ≤ 8) {N : Set V}
    (hN : N.Nonempty) (hY : (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈) :
    certificateIndicator N B ≠ 0 ∧ X.integralGramMatrix.IsAdmissible B (certificateIndicator N B) ∧
      X.integralGramMatrix.admissibleNeighbors B (certificateIndicator N B) = N := by
  classical
  let s := certificateIndicator N B
  have hD := (hB.det_pos X.integralGramMatrix_isSymm).ne'
  obtain ⟨hc, hq⟩ := (isRepresentedIn_adjoinVertex_iff hX hB hr hN).mp hY
  have hs : X.integralGramMatrix.IsAdmissible B s := by
    refine ⟨?_, ?_, hq⟩
    · intro b
      simp only [s, certificateIndicator]
      split_ifs <;> simp
    · intro u
      rw [hc u]
      split_ifs <;> simp
  have heq : X.integralGramMatrix.admissibleNeighbors B s = N := by
    ext u
    change (s ᵥ* X.integralGramMatrix.certificateCoordinates B) u =
      X.integralGramMatrix.certificateDet B ↔ u ∈ N
    rw [hc u]
    by_cases hu : u ∈ N <;> simp [hu, hD.symm]
  refine ⟨?_, hs, heq⟩
  intro hz
  change s = 0 at hz
  rw [hz, admissibleNeighbors_zero _ _ hD] at heq
  exact hN.ne_empty heq.symm

-- Lemma 3.5 [Exc]
/-- Lemma `lem:admissible` (Lemma 3.5) of [Exc]: the nonempty admissible neighbour
sets are exactly the extensions represented in `E₈`. -/
theorem isRepresentedIn_adjoinVertex_iff_exists_admissible (hX : X.Connected)
    (hB : X.integralGramMatrix.IsGramCertificate B) (hr : B.card ≤ 8) {N : Set V}
    (hN : N.Nonempty) :
    (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈ ↔
      ∃ s : B → ℤ, s ≠ 0 ∧ X.integralGramMatrix.IsAdmissible B s ∧
        X.integralGramMatrix.admissibleNeighbors B s = N := by
  constructor
  · intro hY
    exact ⟨certificateIndicator N B,
      admissible_certificateIndicator_of_isRepresentedIn_adjoinVertex hX hB hr hN hY⟩
  · rintro ⟨s, hne, hs, rfl⟩
    exact isRepresentedIn_adjoinVertex_admissibleNeighbors hX hB hr hs hne

-- Lemma 3.5 [Exc]
/-- The uniqueness assertion of `lem:admissible` (Lemma 3.5) of [Exc], with the
unique vector explicitly identified as the indicator of `N ∩ B`. -/
theorem existsUnique_admissible_of_isRepresentedIn_adjoinVertex (hX : X.Connected)
    (hB : X.integralGramMatrix.IsGramCertificate B) (hr : B.card ≤ 8) {N : Set V}
    (hN : N.Nonempty) (hY : (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈) :
    ∃! s : B → ℤ, s ≠ 0 ∧ X.integralGramMatrix.IsAdmissible B s ∧
      X.integralGramMatrix.admissibleNeighbors B s = N := by
  have hs := admissible_certificateIndicator_of_isRepresentedIn_adjoinVertex hX hB hr hN hY
  refine ⟨certificateIndicator N B, hs, ?_⟩
  rintro t ⟨_, ht, hNt⟩
  exact (admissibleNeighbors_inj _ _ (hB.det_pos X.integralGramMatrix_isSymm).ne'
    ht.1 hs.2.1.1).mp (hNt.trans hs.2.2.symm)

end SimpleGraph
