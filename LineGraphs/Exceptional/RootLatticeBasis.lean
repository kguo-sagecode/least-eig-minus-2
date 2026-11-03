/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Lattice
import LineGraphs.Computations.C21E6
import LineGraphs.Computations.C21E7
import LineGraphs.Computations.C21E8

/-! # Integral bases of root lattices

The integral-basis part of Lemma `lem:rootlattice` (Lemma 2.2) of [Exc].
The exceptional models use the integral coordinates certified by C21.
-/

open Module Submodule
open scoped RealInnerProductSpace

namespace LineSystem

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: roots with integral coordinates
in a given family generate exactly its integer span. -/
theorem span_int_eq_of_integral_coordinates (S : LineSystem E) (v : ι → E)
    (hm : ∀ i, v i ∈ S.Φ)
    (hc : ∀ r ∈ S.Φ, ∃ z : ι → ℤ, r = ∑ i, (z i : ℝ) • v i) :
    span ℤ (Set.range v) = span ℤ S.Φ := by
  apply le_antisymm
  · exact span_mono (Set.range_subset_iff.mpr hm)
  · apply span_le.mpr
    intro r hr
    obtain ⟨z, rfl⟩ := hc r hr
    apply sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul]
    exact smul_mem _ _ (subset_span (Set.mem_range_self i))

-- Lemma 2.2 [Exc]
omit [Fintype ι] in
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: independent simple roots that
generate the root lattice form an integral basis. -/
noncomputable def intBasisOfSimpleRoots (S : LineSystem E) (v : ι → E)
    (hli : LinearIndependent ℝ v) (hs : span ℤ (Set.range v) = span ℤ S.Φ) :
    Basis ι ℤ (span ℤ S.Φ) :=
  (Basis.span (hli.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hs)

-- Lemma 2.2 [Exc]
omit [Fintype ι] in
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the integral basis retains the
specified simple-root vectors. -/
@[simp] theorem intBasisOfSimpleRoots_apply (S : LineSystem E) (v : ι → E)
    (hli : LinearIndependent ℝ v) (hs : span ℤ (Set.range v) = span ℤ S.Φ) (i : ι) :
    (S.intBasisOfSimpleRoots v hli hs i : E) = v i := by
  simp [intBasisOfSimpleRoots]

end LineSystem

namespace LineSystem.E₆

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the C21 simple roots generate
the entire `E₆` root lattice over the integers. -/
theorem span_int_simpleRoot : span ℤ (Set.range simpleRoot) = span ℤ E₆.Φ :=
  E₆.span_int_eq_of_integral_coordinates simpleRoot simpleRoot_mem
    (fun _ hr ↦ let ⟨z, _, hz⟩ := exists_simpleRoot_coordinates hr; ⟨z, hz⟩)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: an integral simple-root basis of `E₆`. -/
noncomputable def simpleIntBasis : Basis (Fin 6) ℤ (span ℤ E₆.Φ) :=
  E₆.intBasisOfSimpleRoots simpleRoot
    (Matrix.linearIndependent_of_det_gram_ne_zero (by rw [det_gram_simpleRoot]; norm_num))
    span_int_simpleRoot

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the basis vectors are the C21 simple roots. -/
@[simp] theorem simpleIntBasis_apply (i : Fin 6) :
    (simpleIntBasis i : EuclideanSpace ℝ (Fin 8)) = simpleRoot i := by
  simp [simpleIntBasis]

end LineSystem.E₆

namespace LineSystem.E₇

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the C21 simple roots generate
the entire `E₇` root lattice over the integers. -/
theorem span_int_simpleRoot : span ℤ (Set.range simpleRoot) = span ℤ E₇.Φ :=
  E₇.span_int_eq_of_integral_coordinates simpleRoot simpleRoot_mem
    (fun _ hr ↦ let ⟨z, _, hz⟩ := exists_simpleRoot_coordinates hr; ⟨z, hz⟩)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: an integral simple-root basis of `E₇`. -/
noncomputable def simpleIntBasis : Basis (Fin 7) ℤ (span ℤ E₇.Φ) :=
  E₇.intBasisOfSimpleRoots simpleRoot
    (Matrix.linearIndependent_of_det_gram_ne_zero (by rw [det_gram_simpleRoot]; norm_num))
    span_int_simpleRoot

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the basis vectors are the C21 simple roots. -/
@[simp] theorem simpleIntBasis_apply (i : Fin 7) :
    (simpleIntBasis i : EuclideanSpace ℝ (Fin 8)) = simpleRoot i := by
  simp [simpleIntBasis]

end LineSystem.E₇

namespace LineSystem.E₈

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the C21 simple roots generate
the entire `E₈` root lattice over the integers. -/
theorem span_int_simpleRoot : span ℤ (Set.range simpleRoot) = span ℤ E₈.Φ :=
  E₈.span_int_eq_of_integral_coordinates simpleRoot simpleRoot_mem
    (fun _ hr ↦ let ⟨z, _, hz⟩ := exists_simpleRoot_coordinates hr; ⟨z, hz⟩)

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: an integral simple-root basis of `E₈`. -/
noncomputable def simpleIntBasis : Basis (Fin 8) ℤ (span ℤ E₈.Φ) :=
  E₈.intBasisOfSimpleRoots simpleRoot
    (Matrix.linearIndependent_of_det_gram_ne_zero (by rw [det_gram_simpleRoot]; norm_num))
    span_int_simpleRoot

-- Lemma 2.2 [Exc]
/-- Lemma `lem:rootlattice` (Lemma 2.2) of [Exc]: the basis vectors are the C21 simple roots. -/
@[simp] theorem simpleIntBasis_apply (i : Fin 8) :
    (simpleIntBasis i : EuclideanSpace ℝ (Fin 8)) = simpleRoot i := by
  simp [simpleIntBasis]

end LineSystem.E₈
