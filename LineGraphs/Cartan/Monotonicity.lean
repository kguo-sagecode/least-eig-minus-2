/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.Rayleigh

/-!
# Rayleigh monotonicity under weighted containment

We extend a nonnegative unit maximizer by zero along the specified embedding.
Equality forces this extension to be positive on the connected larger graph, so the
embedding is onto and every entry inequality is an equality.
-/

namespace Matrix

variable {ι κ : Type*}

/-- Extension of coordinates by zero along a vertex embedding. -/
noncomputable def extendByZero (e : κ ↪ ι) (x : κ → ℝ) : ι → ℝ :=
  Function.extend e x 0

/-- `lem:monotonicity`, Remark 3.11 of [CGSS]: extending by zero preserves the
coordinate at each embedded vertex. -/
@[simp]
theorem extendByZero_apply (e : κ ↪ ι) (x : κ → ℝ) (i : κ) :
    extendByZero e x (e i) = x i := e.injective.extend_apply _ _ _

/-- Coordinates outside the image of the embedding vanish. -/
theorem extendByZero_eq_zero (e : κ ↪ ι) (x : κ → ℝ) {j : ι}
    (hj : j ∉ Set.range e) : extendByZero e x j = 0 :=
  Function.extend_apply' _ _ _ hj

/-- Extension by zero preserves coordinatewise nonnegativity. -/
theorem extendByZero_nonneg (e : κ ↪ ι) {x : κ → ℝ} (hx : ∀ i, 0 ≤ x i) (j : ι) :
    0 ≤ extendByZero e x j := by
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simpa only [extendByZero_apply] using hx i
  · rw [extendByZero_eq_zero e x hj]

variable [Fintype ι] [Fintype κ]

/-- Restricting the other factor computes the dot product against a zero extension. -/
theorem dotProduct_extendByZero (e : κ ↪ ι) (x : κ → ℝ) (y : ι → ℝ) :
    extendByZero e x ⬝ᵥ y = x ⬝ᵥ (y ∘ e) := by
  classical
  symm
  apply Finset.sum_of_injOn e e.injective.injOn (fun _ _ => Finset.mem_univ _)
  · intro j _ hj
    have hnot : j ∉ Set.range e := by simpa only [Finset.coe_univ, Set.image_univ] using hj
    rw [extendByZero_eq_zero e x hnot, zero_mul]
  · intro i _
    simp only [extendByZero_apply, Function.comp_apply]

/-- Extension by zero preserves the squared Euclidean norm. -/
theorem dotProduct_extendByZero_self (e : κ ↪ ι) (x : κ → ℝ) :
    extendByZero e x ⬝ᵥ extendByZero e x = x ⬝ᵥ x := by
  rw [dotProduct_extendByZero]
  congr 1
  funext i
  exact extendByZero_apply e x i

/-- The quadratic form of a zero extension is the principal-submatrix quadratic form. -/
theorem quadratic_extendByZero (e : κ ↪ ι) (x : κ → ℝ) (B : Matrix ι ι ℝ) :
    extendByZero e x ⬝ᵥ (B *ᵥ extendByZero e x) =
      x ⬝ᵥ (B.submatrix e e *ᵥ x) := by
  rw [dotProduct_extendByZero]
  congr 1
  funext i
  change B (e i) ⬝ᵥ extendByZero e x = _
  rw [dotProduct_comm, dotProduct_extendByZero, dotProduct_comm]
  rfl

/-- A quadratic form on a nonnegative vector is monotone in all matrix entries. -/
theorem quadratic_mono_of_nonneg {A B : Matrix ι ι ℝ} (hAB : ∀ i j, A i j ≤ B i j)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hx i)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hAB i j) (hx j)

end Matrix

namespace WeightedGraph

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty ι] [Nonempty κ] {X : WeightedGraph ι} {Y : WeightedGraph κ}

/-- Weighted containment cannot decrease the largest eigenvalue. Connectedness of the
larger graph is not needed for this non-strict statement. -/
theorem maxRayleigh_mono {e : κ ↪ ι} (he : X.Contains Y e) :
    maxRayleigh Y.isHermitian ≤ maxRayleigh X.isHermitian := by
  obtain ⟨x, hx, hnorm, heig⟩ := Y.isHermitian.exists_nonneg_max_eigenvector Y.nonneg
  have hform : x ⬝ᵥ (Y.weights *ᵥ x) = maxRayleigh Y.isHermitian := by
    rw [heig, dotProduct_smul, smul_eq_mul, hnorm, mul_one]
  calc
    maxRayleigh Y.isHermitian = x ⬝ᵥ (Y.weights *ᵥ x) := hform.symm
    _ ≤ x ⬝ᵥ (X.weights.submatrix e e *ᵥ x) := quadratic_mono_of_nonneg he hx
    _ = extendByZero e x ⬝ᵥ (X.weights *ᵥ extendByZero e x) :=
      (quadratic_extendByZero e x X.weights).symm
    _ ≤ maxRayleigh X.isHermitian * (extendByZero e x ⬝ᵥ extendByZero e x) :=
      X.isHermitian.quadratic_le_maxRayleigh _
    _ = maxRayleigh X.isHermitian := by rw [dotProduct_extendByZero_self, hnorm, mul_one]

/-- Equality in monotonicity, for a connected larger graph, forces the specified
containment to be onto and to preserve every weight. -/
theorem Contains.eq_of_maxRayleigh_eq {e : κ ↪ ι} (he : X.Contains Y e)
    (hX : X.support.Connected) (hmaxeq : maxRayleigh Y.isHermitian = maxRayleigh X.isHermitian) :
    Function.Surjective e ∧ ∀ i j, Y.weights i j = X.weights (e i) (e j) := by
  obtain ⟨v, hv, hvnorm, heig⟩ := Y.isHermitian.exists_nonneg_max_eigenvector Y.nonneg
  let x := extendByZero e v
  have hxnorm : x ⬝ᵥ x = 1 := (dotProduct_extendByZero_self e v).trans hvnorm
  have hxnonneg : ∀ i, 0 ≤ x i := extendByZero_nonneg e hv
  have hx0 : x ≠ 0 := by intro h; simp [h] at hxnorm
  have hvform : v ⬝ᵥ (Y.weights *ᵥ v) = maxRayleigh Y.isHermitian := by
    rw [heig, dotProduct_smul, smul_eq_mul, hvnorm, mul_one]
  have hcompare := quadratic_mono_of_nonneg (A := Y.weights)
    (B := X.weights.submatrix e e) he hv
  have hxform : x ⬝ᵥ (X.weights *ᵥ x) = maxRayleigh X.isHermitian := by
    apply le_antisymm
    · simpa only [hxnorm, mul_one] using X.isHermitian.quadratic_le_maxRayleigh x
    · rw [← hmaxeq, ← hvform]
      exact hcompare.trans_eq (quadratic_extendByZero e v X.weights).symm
  have hxeig : X.weights *ᵥ x = maxRayleigh X.isHermitian • x :=
    (X.isHermitian.rayleigh_eq_iff hx0).mp (by rw [hxnorm, div_one, hxform])
  have hxpos (i : ι) : 0 < x i := by
    apply lt_of_le_of_ne (hxnonneg i)
    intro hi
    exact hx0 (X.eq_zero_of_nonneg_eigenvector_zero hX hxnonneg hxeig hi.symm)
  have hvpos (i : κ) : 0 < v i := by
    simpa only [x, extendByZero_apply] using hxpos (e i)
  constructor
  · intro j
    by_contra hj
    have hz : x j = 0 := extendByZero_eq_zero e v hj
    exact (hxpos j).ne' hz
  · have heq : v ⬝ᵥ (Y.weights *ᵥ v) = v ⬝ᵥ (X.weights.submatrix e e *ᵥ v) := by
      rw [hvform, ← quadratic_extendByZero, show extendByZero e v = x from rfl, hxform, hmaxeq]
    have hrow (i : κ) : v i * (Y.weights *ᵥ v) i ≤
        v i * (X.weights.submatrix e e *ᵥ v) i := by
      apply mul_le_mul_of_nonneg_left _ (hv i)
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (he i j) (hv j))
    have hrows := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => hrow i)).mp heq
    intro i j
    have hinner : (Y.weights *ᵥ v) i = (X.weights.submatrix e e *ᵥ v) i :=
      mul_left_cancel₀ (hvpos i).ne' (hrows i (Finset.mem_univ i))
    have hterms := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (he i j) (hv j))).mp hinner
    exact mul_right_cancel₀ (hvpos j).ne' (hterms j (Finset.mem_univ j))

/-- Proper specified containment strictly increases the maximum Rayleigh value when
the larger weighted graph is connected. -/
theorem maxRayleigh_strictMono {e : κ ↪ ι} (he : X.Contains Y e)
    (hX : X.support.Connected)
    (hproper : ¬ Function.Surjective e ∨ ∃ i j, Y.weights i j < X.weights (e i) (e j)) :
    maxRayleigh Y.isHermitian < maxRayleigh X.isHermitian := by
  apply lt_of_le_of_ne (maxRayleigh_mono he)
  intro hmaxeq
  obtain ⟨hsurj, heq⟩ := he.eq_of_maxRayleigh_eq hX hmaxeq
  rcases hproper with h | ⟨i, j, hij⟩
  · exact h hsurj
  · exact (ne_of_lt hij) (heq i j)

end WeightedGraph
