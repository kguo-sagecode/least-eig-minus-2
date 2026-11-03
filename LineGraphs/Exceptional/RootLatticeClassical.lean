/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.RootLatticeBasis
import LineGraphs.RootSetClassification.LeadingDeterminants

/-! # Simple roots of the classical root lattices

Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: integral simple-root bases and
their Gram determinants for `A` and `D`.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace LineSystem.An

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: consecutive coordinate
differences form the simple roots of `Aₙ`. -/
noncomputable def simpleRoot (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.single i.succ 1 - EuclideanSpace.single i.castSucc 1

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the simple roots belong to the model. -/
theorem simpleRoot_mem (n : ℕ) (i : Fin n) : simpleRoot n i ∈ (An n).Φ :=
  sub_single_mem_An _ _ (by simp [Fin.ext_iff])

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the simple-root Gram matrix is
the `Aₙ` Cartan matrix. -/
theorem gram_simpleRoot (n : ℕ) :
    Matrix.gram ℝ (simpleRoot n) = (CartanMatrix.A n).map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [Matrix.gram_apply, simpleRoot, inner_sub_left, inner_sub_right,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul, PiLp.single_apply,
    Matrix.map_apply, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
    Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> norm_num <;> omega

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the determinant of the `Aₙ`
simple-root Gram matrix is `n + 1`, including rank zero. -/
theorem det_gram_simpleRoot (n : ℕ) : (Matrix.gram ℝ (simpleRoot n)).det = n + 1 := by
  rw [gram_simpleRoot, ← Int.cast_det, CartanMatrix.det_A]
  norm_cast

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: every coordinate difference
is an integral combination of consecutive differences. -/
theorem sub_single_mem_span_simpleRoot (n : ℕ) (i j : Fin (n + 1)) :
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈
      span ℤ (Set.range (simpleRoot n)) := by
  have h (k : Fin (n + 1)) :
      EuclideanSpace.single k (1 : ℝ) - EuclideanSpace.single 0 1 ∈
        span ℤ (Set.range (simpleRoot n)) := by
    induction k using Fin.induction with
    | zero => simp
    | succ k hk =>
      have hm := add_mem (subset_span (Set.mem_range_self k) :
        simpleRoot n k ∈ span ℤ (Set.range (simpleRoot n))) hk
      convert hm using 1
      simp only [simpleRoot]
      abel
  convert sub_mem (h i) (h j) using 1
  abel

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the simple roots generate the
full `Aₙ` root lattice. -/
theorem span_int_simpleRoot (n : ℕ) :
    span ℤ (Set.range (simpleRoot n)) = span ℤ (An n).Φ := by
  apply le_antisymm
  · exact span_mono (Set.range_subset_iff.mpr (simpleRoot_mem n))
  · apply span_le.mpr
    rintro r ⟨a, rfl⟩
    have he : integerVector 1 (anRoot a) =
        EuclideanSpace.single a.val.1 (1 : ℝ) - EuclideanSpace.single a.val.2 1 := by
      ext k
      simp [integerVector, anRoot, pairVector, Pi.single_apply, PiLp.single_apply]
      split_ifs <;> norm_num
    change integerVector 1 (anRoot a) ∈ span ℤ (Set.range (simpleRoot n))
    rw [he]
    exact sub_single_mem_span_simpleRoot n _ _

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: an integral simple-root basis of `Aₙ`. -/
noncomputable def simpleIntBasis (n : ℕ) : Basis (Fin n) ℤ (span ℤ (An n).Φ) :=
  (An n).intBasisOfSimpleRoots (simpleRoot n)
    (Matrix.linearIndependent_of_det_gram_ne_zero (by rw [det_gram_simpleRoot]; positivity))
    (span_int_simpleRoot n)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the basis vectors are the consecutive roots. -/
@[simp] theorem simpleIntBasis_apply (n : ℕ) (i : Fin n) :
    (simpleIntBasis n i : EuclideanSpace ℝ (Fin (n + 1))) = simpleRoot n i := by
  simp [simpleIntBasis]

end LineSystem.An

namespace LineSystem.Dn

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: simple roots of `Dₙ₊₂`.
The fork comes first: `e₀ + e₁`, followed by the consecutive differences of `Aₙ₊₁`.
The shift permits all dimensions at least two without proof arguments in the definition. -/
noncomputable def simpleRoot (n : ℕ) : Fin (n + 2) → EuclideanSpace ℝ (Fin (n + 2)) :=
  Fin.cases (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1) (An.simpleRoot (n + 1))

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: each specified simple root is a `D` root. -/
theorem simpleRoot_mem (n : ℕ) (i : Fin (n + 2)) : simpleRoot n i ∈ (Dn (n + 2)).Φ := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact add_single_mem_Dn _ _ (by simp)
  · exact An_Φ_subset_Dn (n + 1) (An.simpleRoot_mem _ j)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: reversing the order gives the
standard `D` Cartan matrix. -/
theorem gram_simpleRoot (n : ℕ) :
    Matrix.gram ℝ (simpleRoot n) =
      ((CartanMatrix.D (n + 2)).submatrix Fin.rev Fin.rev).map (Int.cast : ℤ → ℝ) := by
  have h0 (j : Fin (n + 1)) :
      CartanMatrix.D (n + 2) (Fin.rev 0) (Fin.rev j.succ) =
        if j.val = 1 then -1 else 0 := by
    have hj := j.isLt
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_rev,
      Fin.val_zero, Fin.val_succ]
    split_ifs <;> omega
  have hss (i j : Fin (n + 1)) :
      CartanMatrix.D (n + 2) (Fin.rev i.succ) (Fin.rev j.succ) =
        CartanMatrix.A (n + 1) i j := by
    have hi := i.isLt
    have hj := j.isLt
    simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff,
      Fin.val_rev, Fin.val_succ]
    split_ifs <;> omega
  have hg0 (j : Fin (n + 1)) :
      ⟪simpleRoot n 0, simpleRoot n j.succ⟫ = if j.val = 1 then -1 else 0 := by
    simp only [simpleRoot, Fin.cases_zero, Fin.cases_succ, An.simpleRoot,
      inner_add_left, inner_sub_right, EuclideanSpace.inner_single_left,
      conj_trivial, one_mul, PiLp.single_apply, Fin.ext_iff, Fin.val_zero,
      Fin.val_one, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> norm_num <;> omega
  ext i j
  refine Fin.cases (Fin.cases ?_ (fun j ↦ ?_) j)
    (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) j) i
  · rw [Matrix.gram_apply, (Dn (n + 2)).inner_self _ (simpleRoot_mem n 0)]
    simp [CartanMatrix.D]
  · simp only [Matrix.gram_apply, hg0, Matrix.map_apply, Matrix.submatrix_apply, h0]
    split_ifs <;> norm_num
  · rw [Matrix.gram_apply, real_inner_comm, hg0]
    rw [Matrix.map_apply, Matrix.submatrix_apply, (CartanMatrix.D_isSymm _).apply, h0]
    split_ifs <;> norm_num
  · change Matrix.gram ℝ (An.simpleRoot (n + 1)) i j = _
    rw [An.gram_simpleRoot]
    simp only [Matrix.map_apply, Matrix.submatrix_apply, hss]

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the determinant of the `D`
simple-root Gram matrix is four. -/
theorem det_gram_simpleRoot (n : ℕ) : (Matrix.gram ℝ (simpleRoot n)).det = 4 := by
  rw [gram_simpleRoot, ← Int.cast_det]
  change ((((CartanMatrix.D (n + 2)).submatrix Fin.revPerm Fin.revPerm).det : ℤ) : ℝ) = 4
  rw [Matrix.det_submatrix_equiv_self]
  rcases n with _ | _ | n
  · have h : (CartanMatrix.D 2).det = 4 := by decide
    exact_mod_cast h
  · have h : (CartanMatrix.D 3).det = 4 := by decide
    exact_mod_cast h
  · rw [CartanMatrix.det_D]
    norm_num

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the simple roots generate
the full `Dₙ₊₂` root lattice, including both signs of every coordinate pair. -/
theorem span_int_simpleRoot (n : ℕ) :
    span ℤ (Set.range (simpleRoot n)) = span ℤ (Dn (n + 2)).Φ := by
  apply le_antisymm
  · exact span_mono (Set.range_subset_iff.mpr (simpleRoot_mem n))
  · have hdiff (i j : Fin (n + 2)) :
        EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈
          span ℤ (Set.range (simpleRoot n)) := by
      apply span_mono (s := Set.range (An.simpleRoot (n + 1))) ?_
        (An.sub_single_mem_span_simpleRoot (n + 1) i j)
      rintro _ ⟨k, rfl⟩
      exact ⟨k.succ, rfl⟩
    have hplus (i j : Fin (n + 2)) :
        EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 ∈
          span ℤ (Set.range (simpleRoot n)) := by
      have hm := add_mem (add_mem (hdiff i 0) (hdiff j 1))
        (subset_span (Set.mem_range_self (0 : Fin (n + 2))) :
          simpleRoot n 0 ∈ span ℤ (Set.range (simpleRoot n)))
      convert hm using 1
      simp only [simpleRoot, Fin.cases_zero]
      abel
    apply span_le.mpr
    rintro r ⟨⟨⟨⟨i, j⟩, hij⟩, a, b⟩, rfl⟩
    change integerVector 1 (dnRoot (⟨(i, j), hij⟩, a, b)) ∈
      span ℤ (Set.range (simpleRoot n))
    cases a <;> cases b
    · convert hplus i j using 1
      ext k
      simp [integerVector, dnRoot, pairVector, rootSign, Pi.single_apply, PiLp.single_apply]
    · convert hdiff i j using 1
      ext k
      simp [integerVector, dnRoot, pairVector, rootSign, Pi.single_apply, PiLp.single_apply]
      split_ifs <;> norm_num
    · convert hdiff j i using 1
      ext k
      simp [integerVector, dnRoot, pairVector, rootSign, Pi.single_apply, PiLp.single_apply]
      split_ifs <;> norm_num
    · convert Submodule.neg_mem _ (hplus i j) using 1
      ext k
      simp [integerVector, dnRoot, pairVector, rootSign, Pi.single_apply, PiLp.single_apply]
      split_ifs <;> norm_num

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: an integral simple-root basis of `Dₙ₊₂`. -/
noncomputable def simpleIntBasis (n : ℕ) : Basis (Fin (n + 2)) ℤ (span ℤ (Dn (n + 2)).Φ) :=
  (Dn (n + 2)).intBasisOfSimpleRoots (simpleRoot n)
    (Matrix.linearIndependent_of_det_gram_ne_zero (by rw [det_gram_simpleRoot]; norm_num))
    (span_int_simpleRoot n)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the basis vectors are the specified roots. -/
@[simp] theorem simpleIntBasis_apply (n : ℕ) (i : Fin (n + 2)) :
    (simpleIntBasis n i : EuclideanSpace ℝ (Fin (n + 2))) = simpleRoot n i := by
  simp [simpleIntBasis]

end LineSystem.Dn
