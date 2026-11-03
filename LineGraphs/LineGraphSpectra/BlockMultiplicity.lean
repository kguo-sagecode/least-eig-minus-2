/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Blocks

/-!
# Multiplicities for scalar bipartite blocks

Toolkit Theorem 6.6, used in the blueprint's proof of [CGSS, Remark 5.7].
Projection onto the first part identifies an eigenspace of the block matrix
with the corresponding Gram eigenspace whenever the second scalar is avoided.
-/

open Module Module.End

namespace Matrix

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

omit [Fintype P] [Fintype Q] in
/-- The symmetric block matrix in blueprint step `s5rgspecC` for [CGSS, Remark 5.7]. -/
theorem isHermitian_fromBlocks_scalar (B : Matrix P Q ℝ) (s t : ℝ) :
    (fromBlocks (s • 1) B Bᵀ (t • 1)).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext (u | u) (v | v) <;> simp [transpose_apply, Matrix.one_apply, eq_comm]

/-- The two block eigenvector equations used by toolkit Theorem 6.6 and the
blueprint's `s5rgspecC` for [CGSS, Remark 5.7]. -/
theorem fromBlocks_scalar_mulVec_eq_iff (B : Matrix P Q ℝ) (s t θ : ℝ)
    (x : P ⊕ Q → ℝ) :
    fromBlocks (s • 1) B Bᵀ (t • 1) *ᵥ x = θ • x ↔
      B *ᵥ (x ∘ Sum.inr) = (θ - s) • (x ∘ Sum.inl) ∧
        Bᵀ *ᵥ (x ∘ Sum.inl) = (θ - t) • (x ∘ Sum.inr) := by
  rw [fromBlocks_mulVec, smul_mulVec, one_mulVec, smul_mulVec, one_mulVec]
  constructor
  · intro hx
    constructor
    · ext i
      have hi := congrFun hx (Sum.inl i)
      simp only [Sum.elim_inl, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        smul_eq_mul] at hi ⊢
      linarith
    · ext i
      have hi := congrFun hx (Sum.inr i)
      simp only [Sum.elim_inr, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        smul_eq_mul] at hi ⊢
      linarith
  · rintro ⟨hl, hr⟩
    ext (i | i)
    · have hi := congrFun hl i
      simp only [Sum.elim_inl, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        smul_eq_mul] at hi ⊢
      linarith
    · have hi := congrFun hr i
      simp only [Sum.elim_inr, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        smul_eq_mul] at hi ⊢
      linarith

/-- Toolkit Theorem 6.6, the eigenspace correspondence underlying blueprint
step `s5rgspecC` for [CGSS, Remark 5.7]. This includes the first scalar's zero modes. -/
theorem eigenvalueMultiplicity_fromBlocks_scalar_of_ne (B : Matrix P Q ℝ)
    (s t θ : ℝ) (hθ : θ ≠ t) :
    (fromBlocks (s • 1) B Bᵀ (t • 1)).eigenvalueMultiplicity θ =
      (B * Bᵀ).eigenvalueMultiplicity ((θ - s) * (θ - t)) := by
  let C := fromBlocks (s • 1) B Bᵀ (t • 1)
  let μ := (θ - s) * (θ - t)
  have hne : θ - t ≠ 0 := sub_ne_zero.mpr hθ
  let F : eigenspace C.toLin' θ →ₗ[ℝ] eigenspace (B * Bᵀ).toLin' μ :=
    { toFun := fun x ↦ ⟨(x : P ⊕ Q → ℝ) ∘ Sum.inl, by
        have hx : C *ᵥ (x : P ⊕ Q → ℝ) = θ • (x : P ⊕ Q → ℝ) :=
          mem_eigenspace_iff.mp x.property
        have he := (fromBlocks_scalar_mulVec_eq_iff B s t θ x).mp hx
        apply mem_eigenspace_iff.mpr
        change (B * Bᵀ) *ᵥ _ = _
        rw [← mulVec_mulVec, he.2, mulVec_smul, he.1, smul_smul]
        congr 1
        exact mul_comm _ _⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hl : (x : P ⊕ Q → ℝ) ∘ Sum.inl = 0 := congrArg Subtype.val hx
    have he := (fromBlocks_scalar_mulVec_eq_iff B s t θ x).mp
      (mem_eigenspace_iff.mp x.property)
    have hr : (x : P ⊕ Q → ℝ) ∘ Sum.inr = 0 := by
      rw [hl, mulVec_zero] at he
      exact (smul_eq_zero.mp he.2.symm).resolve_left hne
    apply Subtype.ext
    ext (i | i)
    · exact congrFun hl i
    · exact congrFun hr i
  have hsurj : Function.Surjective F := by
    intro x
    let y : P ⊕ Q → ℝ := Sum.elim (x : P → ℝ) ((θ - t)⁻¹ • (Bᵀ *ᵥ (x : P → ℝ)))
    have hy : y ∈ eigenspace C.toLin' θ := by
      apply mem_eigenspace_iff.mpr
      apply (fromBlocks_scalar_mulVec_eq_iff B s t θ y).mpr
      have hl : y ∘ Sum.inl = (x : P → ℝ) := rfl
      have hr : y ∘ Sum.inr = (θ - t)⁻¹ • (Bᵀ *ᵥ (x : P → ℝ)) := rfl
      rw [hl, hr]
      constructor
      · have hx : (B * Bᵀ) *ᵥ (x : P → ℝ) = μ • (x : P → ℝ) :=
          mem_eigenspace_iff.mp x.property
        rw [mulVec_smul, mulVec_mulVec, hx, smul_smul]
        congr 1
        dsimp [μ]
        field_simp
      · rw [smul_inv_smul₀ hne]
    exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩
  rw [(isHermitian_fromBlocks_scalar B s t).eigenvalueMultiplicity_eq_finrank,
    (spectrumMultiset_gram_products B).1.isHermitian.eigenvalueMultiplicity_eq_finrank]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective F ⟨hinj, hsurj⟩)

/-- The second scalar's multiplicity in toolkit Theorem 6.6, used in blueprint
step `s5rgspecC` for [CGSS, Remark 5.7]. The scalar diagonal entries are distinct. -/
theorem eigenvalueMultiplicity_fromBlocks_scalar_right (B : Matrix P Q ℝ)
    (s t : ℝ) (hst : s ≠ t) :
    (fromBlocks (s • 1) B Bᵀ (t • 1)).eigenvalueMultiplicity t =
      Fintype.card Q - B.rank := by
  have hswap : (fromBlocks (s • 1) B Bᵀ (t • 1)).submatrix
      (Equiv.sumComm Q P) (Equiv.sumComm Q P) =
      fromBlocks (t • 1) Bᵀ (Bᵀ)ᵀ (s • 1) := by
    ext (u | u) (v | v) <;> rfl
  have hs := spectrumMultiset_submatrix_equiv
    (fromBlocks (s • 1) B Bᵀ (t • 1)) (Equiv.sumComm Q P)
  rw [hswap] at hs
  have he := congrArg (Multiset.count t) hs
  change (fromBlocks (t • 1) Bᵀ (Bᵀ)ᵀ (s • 1)).eigenvalueMultiplicity t =
    (fromBlocks (s • 1) B Bᵀ (t • 1)).eigenvalueMultiplicity t at he
  rw [← he, eigenvalueMultiplicity_fromBlocks_scalar_of_ne Bᵀ t s t hst.symm,
    sub_self, zero_mul, transpose_transpose]
  exact (spectrumMultiset_gram_products B).2.2.2.2

/-- Counting the two real quadratic roots, with repetitions, in toolkit Theorem 6.6;
this is the spectral accounting in blueprint step `s5rgspecC` for [CGSS, Remark 5.7]. -/
theorem count_map_quadratic_roots (s t θ : ℝ) (Λ : Multiset ℝ)
    (hpos : ∀ μ ∈ Λ, 0 < μ) :
    Multiset.count θ (Λ.map (fun μ ↦ (s + t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2)) +
        Multiset.count θ (Λ.map (fun μ ↦ (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2)) =
      Multiset.count ((θ - s) * (θ - t)) Λ := by
  classical
  induction Λ using Multiset.induction_on with
  | empty => simp
  | @cons μ Λ ih =>
    have hμ := hpos μ (Multiset.mem_cons_self _ _)
    have hrest : ∀ ν ∈ Λ, 0 < ν := fun ν hν ↦ hpos ν (Multiset.mem_cons_of_mem hν)
    have hD : 0 < (s - t) ^ 2 + 4 * μ := by nlinarith [sq_nonneg (s - t)]
    have hsq := Real.sq_sqrt hD.le
    have hsqrt := Real.sqrt_pos.mpr hD
    have hroots : (θ - s) * (θ - t) = μ ↔
        θ = (s + t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 ∨
          θ = (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 := by
      constructor
      · intro h
        have hz : (2 * θ - s - t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) *
            (2 * θ - s - t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) = 0 := by nlinarith
        rcases mul_eq_zero.mp hz with hz | hz
        · left; linarith
        · right; linarith
      · rintro (h | h) <;> rw [h] <;> nlinarith
    have hne : (s + t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 ≠
        (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 := by linarith
    have hi := ih hrest
    simp only [Multiset.map_cons, Multiset.count_cons]
    by_cases hp : θ = (s + t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2
    · have hm : θ ≠ (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 := by
        rw [hp]; exact hne
      rw [ite_eq_left hp, ite_eq_right hm, ite_eq_left (hroots.mpr (Or.inl hp))]
      omega
    · by_cases hm : θ = (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2
      · rw [ite_eq_right hp, ite_eq_left hm, ite_eq_left (hroots.mpr (Or.inr hm))]
        omega
      · have hf : (θ - s) * (θ - t) ≠ μ := fun hf ↦ (hroots.mp hf).elim hp hm
        simp only [hp, hm, hf, ite_false]
        exact hi

/-- Toolkit Theorem 6.6 for unequal scalar blocks, the form used by the blueprint's
proof of [CGSS, Remark 5.7]. The two kernel multiplicities are kept separately. -/
theorem spectrumMultiset_fromBlocks_scalar_of_ne (B : Matrix P Q ℝ) (s t : ℝ)
    (hst : s ≠ t) :
    let Λ := (B * Bᵀ).spectrumMultiset.filter (0 < ·)
    (fromBlocks (s • 1) B Bᵀ (t • 1)).spectrumMultiset =
      Λ.map (fun μ ↦ (s + t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2) +
        Λ.map (fun μ ↦ (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2) +
        Multiset.replicate (Fintype.card P - B.rank) s +
        Multiset.replicate (Fintype.card Q - B.rank) t := by
  classical
  let Λ := (B * Bᵀ).spectrumMultiset.filter (0 < ·)
  have hpos : ∀ μ ∈ Λ, 0 < μ := fun _ h ↦ (Multiset.mem_filter.mp h).2
  have hzero : Multiset.count 0 Λ = 0 := by simp [Λ]
  have hg := spectrumMultiset_gram_products B
  apply Multiset.ext.mpr
  intro θ
  simp only [Multiset.count_add, Multiset.count_replicate]
  rw [count_map_quadratic_roots s t θ _ hpos]
  change (fromBlocks (s • 1) B Bᵀ (t • 1)).eigenvalueMultiplicity θ = _
  by_cases ht : θ = t
  · subst θ
    rw [eigenvalueMultiplicity_fromBlocks_scalar_right B s t hst]
    simp [hst, hzero]
  · rw [eigenvalueMultiplicity_fromBlocks_scalar_of_ne B s t θ ht]
    have hc := congrArg (Multiset.count ((θ - s) * (θ - t)))
      hg.1.spectrumMultiset_eq_filter_pos_add_replicate_zero
    rw [hg.2.2.2.1] at hc
    change (B * Bᵀ).eigenvalueMultiplicity ((θ - s) * (θ - t)) = _ at hc
    rw [hc]
    simp only [Multiset.count_add, Multiset.count_replicate, mul_eq_zero,
      sub_eq_zero, ht, or_false, Ne.symm ht, ite_false, add_zero, eq_comm]
    rfl

/-- The centered form of toolkit Theorem 6.6, used in blueprint step `s557ii`
and [CGSS, Remark 5.7]. -/
theorem spectrumMultiset_sub_center_fromBlocks_scalar (B : Matrix P Q ℝ) (s t : ℝ)
    (hst : s ≠ t) :
    let Λ := (B * Bᵀ).spectrumMultiset.filter (0 < ·)
    (fromBlocks (s • 1) B Bᵀ (t • 1)).spectrumMultiset.map
        (fun θ ↦ θ - (s + t) / 2) =
      Λ.map (fun μ ↦ Real.sqrt (μ + (s - t) ^ 2 / 4)) +
        Λ.map (fun μ ↦ -Real.sqrt (μ + (s - t) ^ 2 / 4)) +
        Multiset.replicate (Fintype.card P - B.rank) ((s - t) / 2) +
        Multiset.replicate (Fintype.card Q - B.rank) (-(s - t) / 2) := by
  dsimp only
  rw [spectrumMultiset_fromBlocks_scalar_of_ne B s t hst]
  simp only [Multiset.map_add, Multiset.map_map, Multiset.map_replicate, Function.comp_def]
  have hsqrt (μ : ℝ) : Real.sqrt ((s - t) ^ 2 + 4 * μ) =
      2 * Real.sqrt (μ + (s - t) ^ 2 / 4) := by
    rw [show (s - t) ^ 2 + 4 * μ = 4 * (μ + (s - t) ^ 2 / 4) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hplus (μ : ℝ) : (s + t + Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 - (s + t) / 2 =
      Real.sqrt (μ + (s - t) ^ 2 / 4) := by rw [hsqrt]; ring
  have hminus (μ : ℝ) : (s + t - Real.sqrt ((s - t) ^ 2 + 4 * μ)) / 2 - (s + t) / 2 =
      -Real.sqrt (μ + (s - t) ^ 2 / 4) := by rw [hsqrt]; ring
  simp only [hplus, hminus, show s - (s + t) / 2 = (s - t) / 2 by ring,
    show t - (s + t) / 2 = -(s - t) / 2 by ring]

end Matrix
