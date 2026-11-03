/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Rayleigh
import LineGraphs.Spectral.Regular

/-!
# Symmetric Perron–Frobenius

Theorem 4.5 of the spectral toolkit: taking absolute values of a top eigenvector,
propagating zero coordinates along support edges, and subtracting a minimum ratio.
-/

open Module Module.End

namespace Matrix

variable {n : Type*}

/-- The positive off-diagonal support of a real symmetric matrix. -/
def positiveSupportGraph (A : Matrix n n ℝ) (hA : A.IsHermitian) : SimpleGraph n where
  Adj u v := u ≠ v ∧ 0 < A u v
  symm.symm u v huv := ⟨huv.1.symm, by
    have heq : A v u = A u v := by simpa using hA.apply u v
    simpa only [heq] using huv.2⟩
  loopless.irrefl u hu := hu.1 rfl

variable [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [DecidableEq n] in
/-- Taking coordinatewise absolute values can only increase the absolute quadratic form
of an entrywise nonnegative matrix. -/
theorem abs_dotProduct_mulVec_le (hA₀ : ∀ u v, 0 ≤ A u v) (x : n → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ (fun u => |x u|) ⬝ᵥ (A *ᵥ fun u => |x u|) := by
  -- Step `pf-triangle`: apply the finite-sum triangle inequality twice.
  have hrow (u : n) : |∑ v, A u v * x v| ≤ ∑ v, A u v * |x v| := by
    calc
      _ ≤ ∑ v, |A u v * x v| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_of_nonneg (hA₀ u _)]
  calc
    _ ≤ ∑ u, |x u * ∑ v, A u v * x v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, |x u| * ∑ v, A u v * |x v| := by
      apply Finset.sum_le_sum
      intro u _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hrow u) (abs_nonneg _)
    _ = _ := rfl

namespace IsHermitian

variable (hA : A.IsHermitian) [Nonempty n]

/-- Theorem 4.5 of the spectral toolkit, step `pf-nonnegative`: a nonnegative nonzero top
eigenvector exists. -/
theorem exists_nonneg_eigenvector_largest (hA₀ : ∀ u v, 0 ≤ A u v) :
    ∃ x : n → ℝ, x ≠ 0 ∧ (∀ u, 0 ≤ x u) ∧ A *ᵥ x = hA.largestEigenvalue • x := by
  -- Step `pf-choose`: take a top eigenvector and its coordinatewise absolute value.
  obtain ⟨y, hy0, hy⟩ := hA.mem_spectrumMultiset_iff.mp
    hA.largestEigenvalue_mem_spectrumMultiset
  let x : n → ℝ := fun u => |y u|
  have hx0 : x ≠ 0 := by
    intro hx
    apply hy0
    ext u
    exact abs_eq_zero.mp (congrFun hx u)
  have hnorm : x ⬝ᵥ x = y ⬝ᵥ y := by
    simp only [dotProduct, x, ← sq, sq_abs]
  -- Step `pf-absform`: the absolute vector has no smaller quadratic form.
  have hlower : hA.largestEigenvalue * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    calc
      _ = y ⬝ᵥ (A *ᵥ y) := by rw [hy, dotProduct_smul, hnorm]; rfl
      _ ≤ |y ⬝ᵥ (A *ᵥ y)| := le_abs_self _
      _ ≤ _ := abs_dotProduct_mulVec_le hA₀ y
  have hupper := hA.dotProduct_mulVec_le_largestEigenvalue_mul x
  -- Step `pf-equality`: equality in the Rayleigh bound is an eigenvector equation.
  have heigen : A *ᵥ x = hA.largestEigenvalue • x := by
    apply (hA.rayleigh_eq_largestEigenvalue_iff hx0).mp
    have hpos : 0 < x ⬝ᵥ x := by
      simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx0
    exact (div_eq_iff hpos.ne').mpr (le_antisymm hupper hlower)
  exact ⟨x, hx0, fun u => abs_nonneg _, heigen⟩

/-- The largest eigenvalue of a nonnegative symmetric matrix is nonnegative. -/
theorem largestEigenvalue_nonneg (hA₀ : ∀ u v, 0 ≤ A u v) : 0 ≤ hA.largestEigenvalue := by
  -- Step `pf-diagonal`: equivalently, test the nonnegative top eigenvector's form.
  obtain ⟨x, hx0, hx, heigen⟩ := hA.exists_nonneg_eigenvector_largest hA₀
  have hform : 0 ≤ x ⬝ᵥ (A *ᵥ x) := Finset.sum_nonneg fun u _ =>
    mul_nonneg (hx u) (Finset.sum_nonneg fun v _ => mul_nonneg (hA₀ u v) (hx v))
  rw [heigen, dotProduct_smul] at hform
  have hpos : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx0
  exact nonneg_of_mul_nonneg_left hform hpos

/-- Theorem 4.5 of the spectral toolkit, step `pf-absolute`: every eigenvalue is bounded in
absolute value
by the largest eigenvalue. -/
theorem abs_eigenvalue_le_largest (hA₀ : ∀ u v, 0 ≤ A u v) {μ : ℝ}
    (hμ : μ ∈ A.spectrumMultiset) : |μ| ≤ hA.largestEigenvalue := by
  obtain ⟨x, hx0, heigen⟩ := hA.mem_spectrumMultiset_iff.mp hμ
  -- Step `pf-mu`: the eigenvector form is μ times its positive squared norm.
  have hpos : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx0
  have hnorm : (fun u => |x u|) ⬝ᵥ (fun u => |x u|) = x ⬝ᵥ x := by
    simp only [dotProduct, ← sq, sq_abs]
  -- Step `pf-triangle`: bound the absolute form by the form of the absolute vector.
  have hbound := (abs_dotProduct_mulVec_le hA₀ x).trans
    (hA.dotProduct_mulVec_le_largestEigenvalue_mul (fun u => |x u|))
  rw [heigen, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hpos, hnorm] at hbound
  -- Step `pf-divide`: cancel the squared norm.
  exact (mul_le_mul_iff_left₀ hpos).mp hbound

omit [Nonempty n] [DecidableEq n] in
/-- Theorem 4.5 of the spectral toolkit, step `pf-propagate`: a zero coordinate of a nonnegative
eigenvector
propagates along the positive support, so connected support forces the vector to vanish. -/
theorem eq_zero_of_nonneg_eigenvector_of_eq_zero (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) {x : n → ℝ} {b : ℝ}
    (hx : ∀ u, 0 ≤ x u) (heigen : A *ᵥ x = b • x) {u : n} (hu : x u = 0) : x = 0 := by
  -- Steps `pf-zero-sum`, `pf-edgezero`: a zero row sum of nonnegative terms
  -- forces zero at every positive-support neighbour.
  have hedge {v w : n} (hvw : (A.positiveSupportGraph hA).Adj v w)
      (hv : x v = 0) : x w = 0 := by
    have hsum : ∑ z, A v z * x z = 0 := by
      have he := congrFun heigen v
      simpa [mulVec, dotProduct, hv] using he
    have hw := (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
      mul_nonneg (hA₀ v z) (hx z)).mp hsum w (Finset.mem_univ _)
    exact (mul_eq_zero.mp hw).resolve_left (ne_of_gt hvw.2)
  -- Step `pf-path`: propagate along each path from the zero coordinate.
  have hpath {v w : n} (p : (A.positiveSupportGraph hA).Walk v w) : x v = 0 → x w = 0 := by
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hv => ih (hedge hadj hv)
  -- Step `pf-allzero`: connectedness supplies all the paths.
  have hall (v : n) : x v = 0 := hpath (hc.preconnected u v).some hu
  exact funext hall

omit [Nonempty n] [DecidableEq n] in
/-- Theorem 4.5 of the spectral toolkit, step `pf-positive`: every nonzero nonnegative eigenvector
is positive
when the support is connected, regardless of its eigenvalue. -/
theorem pos_of_nonneg_eigenvector (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) {x : n → ℝ} {b : ℝ}
    (hx0 : x ≠ 0) (hx : ∀ u, 0 ≤ x u) (heigen : A *ᵥ x = b • x) : ∀ u, 0 < x u := by
  have hne (u : n) : x u ≠ 0 := fun hu => hx0
    (hA.eq_zero_of_nonneg_eigenvector_of_eq_zero hA₀ hc hx heigen hu)
  exact fun u => lt_of_le_of_ne (hx u) (hne u).symm

/-- Theorem 4.5 of the spectral toolkit: connected positive support gives a strictly positive top
eigenvector. -/
theorem exists_pos_eigenvector_largest (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) :
    ∃ x : n → ℝ, (∀ u, 0 < x u) ∧ A *ᵥ x = hA.largestEigenvalue • x := by
  have hex := hA.exists_nonneg_eigenvector_largest hA₀
  obtain ⟨x, hx0, hx, heigen⟩ := hex
  exact ⟨x, hA.pos_of_nonneg_eigenvector hA₀ hc hx0 hx heigen, heigen⟩

omit [DecidableEq n] in
/-- Theorem 4.5 of the spectral toolkit, step `pf-line`: with connected support, a positive
eigenvector
spans its whole eigenspace. The other eigenvector need not be nonnegative. -/
theorem eq_smul_of_pos_eigenvector (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) {x y : n → ℝ} {b : ℝ}
    (hx : ∀ u, 0 < x u) (hxe : A *ᵥ x = b • x) (hye : A *ᵥ y = b • y) :
    ∃ c : ℝ, y = c • x := by
  classical
  -- Step `pf-minratio`: choose a minimum of the finitely many real ratios.
  obtain ⟨u, _, hu⟩ := Finset.exists_min_image Finset.univ (fun u => y u / x u)
    Finset.univ_nonempty
  let c := y u / x u
  let z := y - c • x
  -- Step `pf-difference-eigen`: the difference is still an eigenvector.
  have hze : A *ᵥ z = b • z := by
    dsimp [z]
    rw [mulVec_sub, mulVec_smul, hxe, hye, smul_sub, smul_comm c b]
  -- Step `pf-difference-nonneg`: minimality makes every coordinate nonnegative.
  have hz (v : n) : 0 ≤ z v := by
    have hmin := (le_div_iff₀ (hx v)).mp (hu v (Finset.mem_univ _))
    exact sub_nonneg.mpr hmin
  -- Step `pf-difference-zero`: the minimizing coordinate vanishes.
  have hzu : z u = 0 := by
    dsimp [z, c]
    rw [div_mul_cancel₀ _ (hx u).ne', sub_self]
  -- Step `pf-line`: propagation makes the entire difference zero.
  have hz0 := hA.eq_zero_of_nonneg_eigenvector_of_eq_zero hA₀ hc hz hze hzu
  exact ⟨c, sub_eq_zero.mp hz0⟩

/-- Theorem 4.5 of the spectral toolkit, step `pf-dimension`: the top eigenvalue is simple when the
positive support is connected. -/
theorem multiplicity_largest_eq_one (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) :
    A.eigenvalueMultiplicity hA.largestEigenvalue = 1 := by
  obtain ⟨x, hx, hxe⟩ := hA.exists_pos_eigenvector_largest hA₀ hc
  have hx0 : x ≠ 0 := by
    intro h
    have hh := hx (Classical.arbitrary n)
    simp [h] at hh
  let W := eigenspace (toLin' A) hA.largestEigenvalue
  have hxW : x ∈ W := mem_eigenspace_iff.mpr hxe
  -- Step `pf-line`: every vector in the eigenspace is a multiple of x.
  have hspan : W = Submodule.span ℝ {x} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := hA.eq_smul_of_pos_eigenvector hA₀ hc hx hxe
        (show A *ᵥ y = hA.largestEigenvalue • y from mem_eigenspace_iff.mp hy)
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton x))
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxW)
  -- Step `pf-dimension`: Theorem 2.2 identifies multiplicity with eigenspace dimension.
  have hdim : finrank ℝ W = 1 := by rw [hspan]; exact finrank_span_singleton hx0
  rw [hA.eigenvalueMultiplicity_eq_finrank]
  exact hdim

omit [Nonempty n] [DecidableEq n] in
include hA in
/-- Edge constancy: if `x` is a positive eigenvector of a symmetric nonnegative
matrix and `y` has the same eigenvalue, then `y u / x u` is constant across every
positive-support edge. Connectedness is not required. This is the weighted
Laplacian form of the equality argument in `pf-line`. -/
theorem eigenvector_ratio_eq_of_pos_entry (hA₀ : ∀ u v, 0 ≤ A u v)
    {x y : n → ℝ} {b : ℝ} (hx : ∀ u, 0 < x u)
    (hxe : A *ᵥ x = b • x) (hye : A *ᵥ y = b • y)
    {u v : n} (huv : 0 < A u v) : y u / x u = y v / x v := by
  -- Step `lap-diagonal` (weighted): the two diagonal sums use the x-eigenvector equation.
  have hdiag : (∑ u, ∑ v, (y u ^ 2 / x u) * (A u v * x v)) =
      b * (y ⬝ᵥ y) := by
    simp_rw [← Finset.mul_sum]
    change (∑ u, (y u ^ 2 / x u) * (A *ᵥ x) u) = _
    rw [hxe]
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    field_simp [(hx u).ne']
  have hswap : (∑ u, ∑ v, (y v ^ 2 / x v) * (A v u * x u)) =
      ∑ u, ∑ v, (y u ^ 2 / x u) * (A u v * x v) := Finset.sum_comm
  -- Step `lap-cross` (weighted): the cross sum uses the y-eigenvector equation.
  have hcross : (∑ u, ∑ v, y u * (A u v * y v)) = b * (y ⬝ᵥ y) := by
    simp_rw [← Finset.mul_sum]
    change y ⬝ᵥ (A *ᵥ y) = _
    rw [hye, dotProduct_smul]; rfl
  -- Step `lap-minus` (weighted): expand the squared ratio differences.
  have hexpand (u v : n) :
      A u v * x u * x v * (y u / x u - y v / x v) ^ 2 =
        (y u ^ 2 / x u) * (A u v * x v) +
        (y v ^ 2 / x v) * (A v u * x u) - 2 * (y u * (A u v * y v)) := by
    have hsym : A v u = A u v := by simpa using hA.apply u v
    rw [hsym]
    field_simp [(hx u).ne', (hx v).ne']
    ring
  have hsum : (∑ u, ∑ v, A u v * x u * x v * (y u / x u - y v / x v) ^ 2) = 0 := by
    have htwo : (∑ u, ∑ v, 2 * (y u * (A u v * y v))) =
        2 * (∑ u, ∑ v, y u * (A u v * y v)) := by simp only [Finset.mul_sum]
    simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hswap, hdiag, htwo, hcross]
    ring
  -- Step `lap-edges` (weighted): every summand is nonnegative; a positive edge has
  -- zero squared ratio difference.
  have hnn (u v : n) : 0 ≤ A u v * x u * x v * (y u / x u - y v / x v) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hA₀ u v) (hx u).le) (hx v).le) (sq_nonneg _)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => hnn u v).mp hsum u (Finset.mem_univ _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hnn u v).mp
    hrow v (Finset.mem_univ _)
  have hweight : 0 < A u v * x u * x v := mul_pos (mul_pos huv (hx u)) (hx v)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left hweight.ne'))

end IsHermitian
end Matrix
