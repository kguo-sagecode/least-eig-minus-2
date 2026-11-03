/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.PerronFrobenius
import LineGraphs.Spectral.Interlacing

/-!
# Strict monotonicity of the largest eigenvalue

Theorem 4.8 of the spectral toolkit. A nonempty proper subgraph of a connected
graph has a strictly smaller largest eigenvalue; vertices or edges may be omitted.
-/

open Matrix

namespace Matrix.IsHermitian

variable {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype m] [DecidableEq m] [Nonempty m]
  {A : Matrix n n ℝ} {B : Matrix m m ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)

private theorem comparison_and_equality (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) (hB₀ : ∀ u v, 0 ≤ B u v)
    (f : m ↪ n) (hBA : ∀ u v, B u v ≤ A (f u) (f v)) :
    hB.largestEigenvalue ≤ hA.largestEigenvalue ∧
      (hB.largestEigenvalue = hA.largestEigenvalue →
        Function.Surjective f ∧ B = A.submatrix f f) := by
  classical
  -- Step `strict-choose`: take a nonnegative top eigenvector of B and extend by zero.
  obtain ⟨y, hy0, hy, hye⟩ := hB.exists_nonneg_eigenvector_largest hB₀
  obtain ⟨E, _, hnorm, hform, hvalue, hout⟩ :=
    Matrix.exists_principal_submatrix_extension f A
  let z := (E (WithLp.toLp 2 y)).ofLp
  have hzvalue (u : m) : z (f u) = y u := hvalue (WithLp.toLp 2 y) u
  have hzout (v : n) (hv : ∀ u, f u ≠ v) : z v = 0 := hout (WithLp.toLp 2 y) v hv
  have hz0 : z ≠ 0 := by
    intro hz
    apply hy0
    ext u
    have hh := congrFun hz (f u)
    simpa only [hzvalue, Pi.zero_apply] using hh
  -- Step `strict-vector`: extension preserves nonnegativity and squared norm.
  have hz (v : n) : 0 ≤ z v := by
    by_cases hv : ∃ u, f u = v
    · obtain ⟨u, rfl⟩ := hv
      rw [hzvalue]
      exact hy u
    · rw [hzout v (by simpa only [not_exists] using hv)]
  have hznorm : z ⬝ᵥ z = y ⬝ᵥ y := hnorm (WithLp.toLp 2 y)
  have hzform : z ⬝ᵥ (A *ᵥ z) = y ⬝ᵥ (A.submatrix f f *ᵥ y) := hform (WithLp.toLp 2 y)
  have hpos : 0 < y ⬝ᵥ y := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hy0
  -- Step `strict-forms`: entrywise inequalities give the first form comparison.
  have hterm (u v : m) : y u * (B u v * y v) ≤ y u * (A (f u) (f v) * y v) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hBA u v) (hy v)) (hy u)
  have hleform : y ⬝ᵥ (B *ᵥ y) ≤ z ⬝ᵥ (A *ᵥ z) := by
    rw [hzform]
    simp only [dotProduct, mulVec, Finset.mul_sum, submatrix_apply]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v
  have hyeq : y ⬝ᵥ (B *ᵥ y) = hB.largestEigenvalue * (y ⬝ᵥ y) := by
    rw [hye, dotProduct_smul]; rfl
  have hupper := hA.dotProduct_mulVec_le_largestEigenvalue_mul z
  have hweak : hB.largestEigenvalue ≤ hA.largestEigenvalue := by
    have hh := hleform.trans hupper
    rw [hyeq, hznorm] at hh
    exact (mul_le_mul_iff_left₀ hpos).mp hh
  refine ⟨hweak, ?_⟩
  intro heq
  -- Step `strict-eigen`: equality at the ends forces Rayleigh equality for z.
  have hformeq : z ⬝ᵥ (A *ᵥ z) = hA.largestEigenvalue * (z ⬝ᵥ z) := by
    rw [hyeq, heq, ← hznorm] at hleform
    exact le_antisymm hupper hleform
  have hze : A *ᵥ z = hA.largestEigenvalue • z := by
    apply (hA.rayleigh_eq_largestEigenvalue_iff hz0).mp
    rw [hformeq]
    exact mul_div_cancel_right₀ _ (by rw [hznorm]; exact hpos.ne')
  -- Step `strict-positive`: connected support makes z positive, so no coordinate was omitted.
  have hzpos := hA.pos_of_nonneg_eigenvector hA₀ hc hz0 hz hze
  have hsurj : Function.Surjective f := by
    intro v
    by_contra hv
    have hzero := hzout v (by simpa only [not_exists] using hv)
    have hh := hzpos v
    rw [hzero] at hh
    exact (lt_irrefl 0) hh
  have hypos (u : m) : 0 < y u := hzvalue u ▸ hzpos (f u)
  -- Step `strict-difference`: the two entrywise ordered quadratic sums are equal.
  have hsums : (∑ u, ∑ v, y u * (B u v * y v)) =
      ∑ u, ∑ v, y u * (A (f u) (f v) * y v) := by
    have hh : y ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (A.submatrix f f *ᵥ y) := by
      rw [← hzform, hformeq, hznorm, hyeq, heq]
    simpa only [dotProduct, mulVec, Finset.mul_sum, submatrix_apply] using hh
  -- Step `strict-entries`: each nonnegative difference vanishes, and the weights are positive.
  have hentries : B = A.submatrix f f := by
    ext u v
    have hrow := (Finset.sum_eq_sum_iff_of_le fun u _ =>
      Finset.sum_le_sum fun v _ => hterm u v).mp hsums u (Finset.mem_univ _)
    have huv := (Finset.sum_eq_sum_iff_of_le fun v _ => hterm u v).mp
      hrow v (Finset.mem_univ _)
    exact mul_right_cancel₀ (hypos v).ne' (mul_left_cancel₀ (hypos u).ne' huv)
  exact ⟨hsurj, hentries⟩

/-- The weak comparison accompanying Theorem 4.8: a nonnegative symmetric matrix
bounded by a principal submatrix has no larger top eigenvalue. -/
theorem largestEigenvalue_le_of_le_submatrix (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) (hB₀ : ∀ u v, 0 ≤ B u v)
    (f : m ↪ n) (hBA : ∀ u v, B u v ≤ A (f u) (f v)) :
    hB.largestEigenvalue ≤ hA.largestEigenvalue :=
  (comparison_and_equality hA hB hA₀ hc hB₀ f hBA).1

/-- Theorem 4.8 of the spectral toolkit: the comparison is strict if a vertex is omitted or an entry
inequality is strict. No connectedness assumption on the smaller matrix is needed. -/
theorem largestEigenvalue_lt_of_lt_submatrix (hA₀ : ∀ u v, 0 ≤ A u v)
    (hc : (A.positiveSupportGraph hA).Connected) (hB₀ : ∀ u v, 0 ≤ B u v)
    (f : m ↪ n) (hBA : ∀ u v, B u v ≤ A (f u) (f v))
    (hproper : ¬ Function.Surjective f ∨ ∃ u v, B u v < A (f u) (f v)) :
    hB.largestEigenvalue < hA.largestEigenvalue := by
  have hh := comparison_and_equality hA hB hA₀ hc hB₀ f hBA
  -- Step `strict-contrapositive`: either kind of omission excludes equality.
  have hne : hB.largestEigenvalue ≠ hA.largestEigenvalue := by
    intro heq
    obtain ⟨hsurj, hentries⟩ := hh.2 heq
    rcases hproper with hnot | ⟨u, v, huv⟩
    · exact hnot hsurj
    · rw [hentries] at huv
      exact (lt_irrefl _) huv
  exact lt_of_le_of_ne hh.1 hne

end Matrix.IsHermitian

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype W] [DecidableEq W] [Nonempty W]
  {X : SimpleGraph V} [DecidableRel X.Adj] {Y : SimpleGraph W} [DecidableRel Y.Adj]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
/-- The positive support of an adjacency matrix is the original graph. -/
theorem positiveSupportGraph_adjMatrix :
    (X.adjMatrix ℝ).positiveSupportGraph (X.isHermitian_adjMatrix ℝ) = X := by
  ext u v
  change (u ≠ v ∧ 0 < X.adjMatrix ℝ u v) ↔ X.Adj u v
  by_cases huv : X.Adj u v
  · simp [adjMatrix_apply, huv, huv.ne]
  · simp [adjMatrix_apply, huv]

/-- Theorem 4.8 of the spectral toolkit: every nonempty proper subgraph of a connected finite
graph has
strictly smaller largest eigenvalue. The edge-preserving injection can omit vertices
or edges; the smaller graph need not be induced or connected. -/
theorem largestEigenvalue_lt_of_proper_subgraph (hc : X.Connected) (f : W ↪ V)
    (hf : ∀ u v, Y.Adj u v → X.Adj (f u) (f v))
    (hproper : ¬ Function.Surjective f ∨
      ∃ u v, X.Adj (f u) (f v) ∧ ¬ Y.Adj u v) :
    Y.largestEigenvalue < X.largestEigenvalue := by
  -- Step `strict-graph-hyp`: the support and nonnegativity hypotheses are automatic.
  have hsupport : ((X.adjMatrix ℝ).positiveSupportGraph (X.isHermitian_adjMatrix ℝ)).Connected := by
    rwa [positiveSupportGraph_adjMatrix]
  have hX₀ (u v : V) : 0 ≤ X.adjMatrix ℝ u v := by
    simp only [adjMatrix_apply]
    split_ifs <;> norm_num
  have hY₀ (u v : W) : 0 ≤ Y.adjMatrix ℝ u v := by
    simp only [adjMatrix_apply]
    split_ifs <;> norm_num
  have hle (u v : W) : Y.adjMatrix ℝ u v ≤ X.adjMatrix ℝ (f u) (f v) := by
    by_cases huv : Y.Adj u v
    · simp [adjMatrix_apply, huv, hf u v huv]
    · simpa [adjMatrix_apply, huv] using hX₀ (f u) (f v)
  -- Steps `strict-missingvertex`, `strict-missingedge`: graph properness gives matrix strictness.
  have hstrict : ¬ Function.Surjective f ∨
      ∃ u v, Y.adjMatrix ℝ u v < X.adjMatrix ℝ (f u) (f v) := by
    rcases hproper with hv | ⟨u, v, hX, hY⟩
    · exact Or.inl hv
    · exact Or.inr ⟨u, v, by simp [adjMatrix_apply, hX, hY]⟩
  exact (X.isHermitian_adjMatrix ℝ).largestEigenvalue_lt_of_lt_submatrix
    (Y.isHermitian_adjMatrix ℝ) hX₀ hsupport hY₀ f hle hstrict

end SimpleGraph
