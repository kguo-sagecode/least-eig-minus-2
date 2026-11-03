/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Rayleigh
import LineGraphs.Cartan.WeightedGraph

/-!
# Rayleigh maxima for weighted graphs

The Rayleigh and propagation lemmas used in the Remark 3.11 classification.
`Matrix.maxRayleigh` uses the largest eigenvalue from the project's spectral toolkit;
the lemmas below show that it is the attained maximum on the unit sphere.
-/

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {B : Matrix ι ι ℝ}

/-- The maximum Rayleigh value of a real symmetric matrix. The spectral toolkit proves
that this largest eigenvalue is the maximum on the unit sphere. -/
noncomputable abbrev maxRayleigh (hB : B.IsHermitian) : ℝ := hB.largestEigenvalue

namespace IsHermitian

/-- The quadratic bound in `lem:rayleigh`, Remark 3.11 of [CGSS]. -/
theorem quadratic_le_maxRayleigh (hB : B.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ (B *ᵥ x) ≤ maxRayleigh hB * (x ⬝ᵥ x) :=
  hB.dotProduct_mulVec_le_largestEigenvalue_mul x

/-- Step `ryattain` of `lem:rayleigh`, Remark 3.11 of [CGSS]: equality in the maximum
Rayleigh quotient is precisely the top eigenvector equation. -/
theorem rayleigh_eq_iff (hB : B.IsHermitian) {x : ι → ℝ} (hx : x ≠ 0) :
    x ⬝ᵥ (B *ᵥ x) / (x ⬝ᵥ x) = maxRayleigh hB ↔ B *ᵥ x = maxRayleigh hB • x :=
  hB.rayleigh_eq_largestEigenvalue_iff hx

/-- Step `ryeigen` of `lem:rayleigh`, Remark 3.11 of [CGSS]: the maximum Rayleigh value
has a unit eigenvector and bounds every real eigenvalue. -/
theorem maxRayleigh_eigenvalue (hB : B.IsHermitian) :
    (∃ x : ι → ℝ, x ⬝ᵥ x = 1 ∧ B *ᵥ x = maxRayleigh hB • x) ∧
    ∀ (t : ℝ) (x : ι → ℝ), x ≠ 0 → B *ᵥ x = t • x → t ≤ maxRayleigh hB := by
  constructor
  · let w := hB.sortedEigenvectorBasis ⟨0, Fintype.card_pos⟩
    refine ⟨⇑w, ?_, hB.mulVec_sortedEigenvectorBasis_zero⟩
    have hn := hB.sortedEigenvectorBasis.norm_eq_one ⟨0, Fintype.card_pos⟩
    have hsq := EuclideanSpace.real_norm_sq_eq w
    simpa only [w, hn, one_pow, dotProduct, pow_two, mul_one] using hsq.symm
  · intro t x hx heig
    exact hB.le_largestEigenvalue_of_mem ((hB.mem_spectrumMultiset_iff).mpr ⟨x, hx, heig⟩)

/-- Step `ryabs` of `lem:rayleigh`, Remark 3.11 of [CGSS]: for a nonnegative symmetric
matrix, absolute values of a unit maximizer give a nonnegative unit maximizing eigenvector. -/
theorem exists_nonneg_max_eigenvector (hB : B.IsHermitian) (hpos : ∀ i j, 0 ≤ B i j) :
    ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ x ⬝ᵥ x = 1 ∧ B *ᵥ x = maxRayleigh hB • x := by
  obtain ⟨x, hxnorm, heig⟩ := hB.maxRayleigh_eigenvalue.1
  let y : ι → ℝ := fun i ↦ |x i|
  have hynorm : y ⬝ᵥ y = 1 := by
    simpa only [y, dotProduct, ← sq, sq_abs] using hxnorm
  have hy0 : y ≠ 0 := by intro h; simp [h] at hynorm
  have hxform : x ⬝ᵥ (B *ᵥ x) = maxRayleigh hB := by
    rw [heig, dotProduct_smul, smul_eq_mul, hxnorm, mul_one]
  have habs : x ⬝ᵥ (B *ᵥ x) ≤ y ⬝ᵥ (B *ᵥ y) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    calc
      x i * (B i j * x j) = B i j * (x i * x j) := by ring
      _ ≤ B i j * |x i * x j| := mul_le_mul_of_nonneg_left (le_abs_self _) (hpos i j)
      _ = y i * (B i j * y j) := by rw [abs_mul]; ring
  have hmax : y ⬝ᵥ (B *ᵥ y) = maxRayleigh hB := by
    apply le_antisymm
    · simpa only [hynorm, mul_one] using hB.quadratic_le_maxRayleigh y
    · rwa [hxform] at habs
  refine ⟨y, fun i ↦ abs_nonneg _, hynorm, (hB.rayleigh_eq_iff hy0).mp ?_⟩
  rw [hynorm, div_one, hmax]

/-! The remaining statements allow nonzero diagonal entries. -/

/-- The off-diagonal support of a real Hermitian matrix. -/
def supportGraph (hB : B.IsHermitian) : SimpleGraph ι :=
  B.supportGraph (fun i j ↦ by rw [(isHermitian_iff_isSymm.mp hB).apply i j])

omit [DecidableEq ι] [Nonempty ι] in
/-- `lem:rem-propagation`, Remark 3.11 of [CGSS]: zero propagation for a nonnegative
symmetric matrix, allowing nonzero diagonal entries. -/
theorem eq_zero_of_nonneg_eigenvector_zero (hB : B.IsHermitian)
    (hpos : ∀ i j, 0 ≤ B i j) (hconn : hB.supportGraph.Connected)
    {x : ι → ℝ} {t : ℝ} (hx : ∀ i, 0 ≤ x i) (heig : B *ᵥ x = t • x)
    {i₀ : ι} (hzero : x i₀ = 0) : x = 0 := by
  have hstep {i j : ι} (hij : hB.supportGraph.Adj i j) (hi : x i = 0) : x j = 0 := by
    have hsum : ∑ k, B i k * x k = 0 := by
      have h := congr_fun heig i
      simpa only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hi, mul_zero] using h
    have hterm : B i j * x j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ mul_nonneg (hpos i k) (hx k))).mp
        hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hterm).resolve_left hij.2
  have heq : ∀ ⦃i j⦄, hB.supportGraph.Adj i j → (x i = 0) = (x j = 0) := by
    intro i j hij
    exact propext ⟨hstep hij, hstep hij.symm⟩
  funext j
  exact (hconn.constant_of_edge_eq heq i₀ j) ▸ hzero

/-- Step `rypositive` of `lem:rayleigh`, Remark 3.11 of [CGSS]: a connected nonnegative
symmetric matrix has a strictly positive unit top eigenvector. -/
theorem exists_pos_max_eigenvector (hB : B.IsHermitian)
    (hpos : ∀ i j, 0 ≤ B i j) (hconn : hB.supportGraph.Connected) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x ⬝ᵥ x = 1 ∧ B *ᵥ x = maxRayleigh hB • x := by
  obtain ⟨x, hx, hnorm, heig⟩ := hB.exists_nonneg_max_eigenvector hpos
  refine ⟨x, fun i ↦ lt_of_le_of_ne (hx i) ?_, hnorm, heig⟩
  intro hi
  have hz := hB.eq_zero_of_nonneg_eigenvector_zero hpos hconn hx heig hi.symm
  simp [hz] at hnorm

omit [DecidableEq ι] in
/-- Step `rysimple` of `lem:rayleigh`, Remark 3.11 of [CGSS]: every eigenvector at the
eigenvalue of a positive eigenvector is its scalar multiple, for connected nonnegative support. -/
theorem eigenvector_eq_smul_of_pos (hB : B.IsHermitian)
    (hpos : ∀ i j, 0 ≤ B i j) (hconn : hB.supportGraph.Connected)
    {w v : ι → ℝ} {t : ℝ} (hw : ∀ i, 0 < w i)
    (hew : B *ᵥ w = t • w) (hev : B *ᵥ v = t • v) : ∃ c : ℝ, v = c • w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ v i / w i)
  let c := v i / w i
  have hmax (j : ι) : v j / w j ≤ c :=
    (Finset.le_sup' (fun i ↦ v i / w i) (Finset.mem_univ j)).trans_eq hi
  have hnonneg (j : ι) : 0 ≤ (c • w - v) j :=
    sub_nonneg.mpr ((div_le_iff₀ (hw j)).mp (hmax j))
  have hzero : (c • w - v) i = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c, div_mul_cancel₀ _ (hw i).ne',
      sub_self]
  have heig : B *ᵥ (c • w - v) = t • (c • w - v) := by
    rw [mulVec_sub, mulVec_smul, hew, hev, smul_sub, smul_comm c t w]
  have hz := hB.eq_zero_of_nonneg_eigenvector_zero hpos hconn hnonneg heig hzero
  exact ⟨c, (sub_eq_zero.mp hz).symm⟩

/-- Step `rysimple` of `lem:rayleigh`, Remark 3.11 of [CGSS]: the largest eigenspace of a
connected nonnegative symmetric matrix has dimension one. -/
theorem max_eigenspace_simple (hB : B.IsHermitian)
    (hpos : ∀ i j, 0 ≤ B i j) (hconn : hB.supportGraph.Connected) :
    Module.finrank ℝ (Module.End.eigenspace (toLin' B) (maxRayleigh hB)) = 1 := by
  obtain ⟨w, hw, hnorm, hew⟩ := hB.exists_pos_max_eigenvector hpos hconn
  have hwmem : w ∈ Module.End.eigenspace (toLin' B) (maxRayleigh hB) := by
    exact Module.End.mem_eigenspace_iff.mpr hew
  apply finrank_eq_one (⟨w, hwmem⟩ : Module.End.eigenspace (toLin' B) (maxRayleigh hB))
  · intro h
    have hwzero : w = 0 := congrArg Subtype.val h
    simp [hwzero] at hnorm
  · intro v
    obtain ⟨c, hc⟩ := hB.eigenvector_eq_smul_of_pos hpos hconn hw hew
      (Module.End.mem_eigenspace_iff.mp v.property)
    exact ⟨c, Subtype.ext hc.symm⟩

/-- `lem:rayleigh`, Remark 3.11 of [CGSS]: a positive eigenvector of a connected
nonnegative symmetric matrix has eigenvalue equal to the maximum Rayleigh value. -/
theorem eigenvalue_eq_maxRayleigh_of_pos (hB : B.IsHermitian)
    (hpos : ∀ i j, 0 ≤ B i j) (hconn : hB.supportGraph.Connected)
    {x : ι → ℝ} {t : ℝ} (hx : ∀ i, 0 < x i) (heig : B *ᵥ x = t • x) :
    t = maxRayleigh hB := by
  obtain ⟨w, hw, _, hew⟩ := hB.exists_pos_max_eigenvector hpos hconn
  by_contra hne
  have hz := hB.dotProduct_eq_zero_of_eigenvalue_ne heig hew hne
  have hp : 0 < x ⬝ᵥ w := Finset.sum_pos (fun i _ ↦ mul_pos (hx i) (hw i))
    Finset.univ_nonempty
  linarith

private theorem maxRayleigh_reindex_le {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hB : B.IsHermitian) (e : ι ≃ κ) :
    maxRayleigh (hB.reindex e) ≤ maxRayleigh hB := by
  obtain ⟨x, hnorm, heig⟩ := (maxRayleigh_eigenvalue (hB.reindex e)).1
  have hx : x ∘ e ≠ 0 := by
    intro hz
    have hxz : x = 0 := by
      funext j
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using
        congr_fun hz (e.symm j)
    simp [hxz] at hnorm
  apply hB.maxRayleigh_eigenvalue.2 _ (x ∘ e) hx
  have he := congrArg (fun v ↦ v ∘ e) heig
  simpa only [reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Pi.smul_comp] using he

/-- `lem:rem-rayleigh-reindex`, Remark 3.11 of [CGSS]: reindexing preserves the maximum
Rayleigh value. -/
theorem maxRayleigh_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hB : B.IsHermitian) (e : ι ≃ κ) :
    maxRayleigh (hB.reindex e) = maxRayleigh hB := by
  apply le_antisymm (maxRayleigh_reindex_le hB e)
  simpa only [reindex_apply, Equiv.symm_symm, submatrix_submatrix, Equiv.symm_comp_self,
    submatrix_id_id] using
    maxRayleigh_reindex_le (hB.reindex e) e.symm

end IsHermitian

end Matrix

namespace WeightedGraph

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The positive-weight support agrees with the Hermitian matrix's nonzero support. -/
theorem support_eq_supportGraph (X : WeightedGraph ι) :
    X.support = X.isHermitian.supportGraph := by
  ext i j
  change 0 < X.weights i j ↔ i ≠ j ∧ X.weights i j ≠ 0
  constructor
  · intro h
    refine ⟨?_, h.ne'⟩
    intro hij
    subst j
    simp [X.diag] at h
  · rintro ⟨_, h⟩
    exact lt_of_le_of_ne (X.nonneg i j) h.symm

/-- A positive eigenvector on a connected weighted graph has the maximum eigenvalue. -/
theorem eigenvalue_eq_maxRayleigh_of_pos (X : WeightedGraph ι) (hX : X.support.Connected)
    {x : ι → ℝ} {t : ℝ} (hx : ∀ i, 0 < x i) (heig : X.weights *ᵥ x = t • x) :
    t = maxRayleigh X.isHermitian := by
  apply X.isHermitian.eigenvalue_eq_maxRayleigh_of_pos X.nonneg _ hx heig
  rwa [← X.support_eq_supportGraph]

/-- On a connected weighted graph the nonnegative maximizing eigenvector is strictly positive. -/
theorem exists_pos_max_eigenvector (X : WeightedGraph ι) (hX : X.support.Connected) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ x ⬝ᵥ x = 1 ∧
      X.weights *ᵥ x = maxRayleigh X.isHermitian • x := by
  obtain ⟨x, hx, hnorm, heig⟩ := X.isHermitian.exists_nonneg_max_eigenvector X.nonneg
  refine ⟨x, fun i ↦ lt_of_le_of_ne (hx i) ?_, hnorm, heig⟩
  intro hi
  have hz := X.eq_zero_of_nonneg_eigenvector_zero hX hx heig hi.symm
  simp [hz] at hnorm

end WeightedGraph
