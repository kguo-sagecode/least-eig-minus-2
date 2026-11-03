/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.FivePossibilities
import LineGraphs.LineSystem.Frame
import LineGraphs.LineSystem.TriangleProperty
import LineGraphs.RootSystems.Correspondence

/-!
# Claims of Sections 2 and 3 of [CGSS] made explicit

Four claims that [CGSS] makes in passing, and that the library used only implicitly. Page
references are to [CGSS], J. Algebra 43 (1976), 305–327.

## Main statements

* `LineSystem.ncard_Φ_eq_two_mul_numLines`, `LineSystem.Hyp24.ncard_Δ_eq_two_mul`: the vector
  sets `Φ` and `Δ` have even size, so `numLines = |Φ| / 2` and `|Δ| / 2` count lines exactly
  (Theorem 2.13, p. 310). `LineSystem.five_possibilities_ncard_Δ` restates the exceptional
  rows of Theorem 2.13 with `|Δ| = 72, 30, 12`.
* `LineSystem.signedAdj_apply_mem`, `LineSystem.exists_signedAdj_submatrix`,
  `LineSystem.exists_signedAdj_eq_switch`: the matrix `C` of the paragraph before Theorem 3.7
  (p. 312) has entries `0, 1, -1` off the diagonal, and is determined by the line system
  up to switching (and, for two indexings of the lines, a relabelling).
* `IsRootSet.smul_iff`, `LineSystem.isRootSet_tfae_of_inner_self_eq`: Definition 3.9 is
  invariant under scaling, so clause (i) of Theorem 3.10 (p. 314) holds at any fixed length, as
  the proof normalizes "without loss of generality" (p. 314).
* `LineSystem.Hyp24.exists_iso_friendship_apply_eq_none`: Lemma 2.9 (p. 308) with the
  isomorphism sending `x` to the common vertex of the triangles.
-/

open scoped RealInnerProductSpace Pointwise
open Submodule Module

/-! ### Theorem 2.13: the parity of the counts -/

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 2.13
/-- The counts of Theorem 2.13 of [CGSS] (p. 310) are line counts: `Φ` has exactly
`2 * numLines` vectors, so `numLines = |Φ| / 2` loses no remainder. The proof counts a signing
(`nonempty_signing`). -/
theorem ncard_Φ_eq_two_mul_numLines (S : LineSystem V) : S.Φ.ncard = 2 * S.numLines := by
  obtain ⟨σ⟩ := S.nonempty_signing
  have h := σ.bijOn.injOn.ncard_image
  rw [σ.bijOn.image_eq, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool] at h
  omega

-- Theorem 2.13
/-- For Theorem 2.13 of [CGSS] (p. 310): the vector set of a line system has even size. -/
theorem even_ncard_Φ (S : LineSystem V) : Even S.Φ.ncard :=
  ⟨S.numLines, by rw [S.ncard_Φ_eq_two_mul_numLines, two_mul]⟩

namespace Hyp24

-- Theorem 2.13
/-- For Theorem 2.13 of [CGSS] (p. 310): `Δ` is the vector set of the restriction of
the system to the orthogonal complement of the star `a, b, c`. -/
theorem Δ_eq_orthogonalTo (H : Hyp24 V) :
    H.Δ = (((H.S.orthogonalTo H.a).orthogonalTo H.b).orthogonalTo H.c).Φ := by
  ext x
  simp only [Δ, orthogonalTo, Set.mem_ofPred_eq, and_assoc]

-- Theorem 2.13
/-- For Theorem 2.13 of [CGSS] (p. 310): `Δ` has an even number of vectors, so the
line count `|Δ| / 2` of `five_possibilities` loses no remainder. -/
theorem ncard_Δ_eq_two_mul (H : Hyp24 V) : H.Δ.ncard = 2 * (H.Δ.ncard / 2) := by
  rw [H.Δ_eq_orthogonalTo]
  exact ncard_Φ_eq_two_mul_numLines _

-- Theorem 2.13
/-- For Theorem 2.13 of [CGSS] (p. 310): `Δ` has even size. -/
theorem even_ncard_Δ (H : Hyp24 V) : Even H.Δ.ncard :=
  ⟨H.Δ.ncard / 2, by rw [← two_mul, ← H.ncard_Δ_eq_two_mul]⟩

end Hyp24

local notation "ℓ" => finrank ℝ V

-- Theorem 2.13
/-- Theorem 2.13 of [CGSS] (p. 310), as `five_possibilities`, with the exceptional rows
stated by the size of the signed set `Δ`: `|Δ| = 72, 30, 12`, that is, 36, 15 and 6 lines. By
`ncard_Φ_eq_two_mul_numLines` the line counts 120, 63 and 36 are exact as well. -/
theorem five_possibilities_ncard_Δ (S : LineSystem V) (D : ModelInputs)
    (hNE : S.Φ.Nonempty) (hI : S.IsIndecomposable) (hSC : S.IsStarClosed)
    (hspan : span ℝ S.Φ = ⊤) :
    (Nonempty (S.Iso (An ℓ)) ∧ S.numLines = ℓ * (ℓ + 1) / 2 ∧
      ((ℓ = 1 ∧ S.numLines = 1) ∨
        (2 ≤ ℓ ∧ ∃ H : Hyp24 V, H.S = S ∧
          Nonempty (H.orthGraph ≃g (⊥ : SimpleGraph (Fin (ℓ - 2))))))) ∨
    (4 ≤ ℓ ∧ Nonempty (S.Iso (Dn ℓ)) ∧ S.numLines = ℓ * (ℓ - 1) ∧
      ∃ H : Hyp24 V, H.S = S ∧
        Nonempty (H.orthGraph ≃g SimpleGraph.friendship (ℓ - 3))) ∨
    (ℓ = 8 ∧ Nonempty (S.Iso E₈) ∧ S.numLines = 120 ∧
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 27 ∧ H.Δ.ncard = 72) ∨
    (ℓ = 7 ∧ Nonempty (S.Iso E₇) ∧ S.numLines = 63 ∧
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 15 ∧ H.Δ.ncard = 30) ∨
    (ℓ = 6 ∧ Nonempty (S.Iso E₆) ∧ S.numLines = 36 ∧
      ∃ H : Hyp24 V, H.S = S ∧ H.Γa.ncard = 9 ∧ H.Δ.ncard = 12) := by
  rcases S.five_possibilities D hNE hI hSC hspan with h | h | ⟨h₁, h₂, h₃, H, hH, hΓ, hΔ⟩ |
      ⟨h₁, h₂, h₃, H, hH, hΓ, hΔ⟩ | ⟨h₁, h₂, h₃, H, hH, hΓ, hΔ⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have := H.ncard_Δ_eq_two_mul
    exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, H, hH, hΓ, by omega⟩))
  · have := H.ncard_Δ_eq_two_mul
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃, H, hH, hΓ, by omega⟩)))
  · have := H.ncard_Δ_eq_two_mul
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h₁, h₂, h₃, H, hH, hΓ, by omega⟩)))

/-! ### The matrix `C` before Theorem 3.7 -/

namespace Signing

variable {S : LineSystem V} {I : Type*}

-- The matrix C before Theorem 3.7
/-- For the paragraph before Theorem 3.7 of [CGSS] (p. 312): every vector of `Φ` is
`± σ i` for some line `i`. -/
theorem exists_eq_or_eq_neg (σ : S.Signing I) {r : V} (hr : r ∈ S.Φ) :
    ∃ i, r = σ i ∨ r = -σ i := by
  obtain ⟨⟨i, b⟩, _, h⟩ := σ.bijOn.surjOn hr
  refine ⟨i, ?_⟩
  cases b
  · exact Or.inl (by simpa [signedVec] using h.symm)
  · exact Or.inr (by simpa [signedVec] using h.symm)

-- The matrix C before Theorem 3.7
/-- For the paragraph before Theorem 3.7 of [CGSS] (p. 312): two chosen vectors that
agree up to sign lie on the same line, so they have the same index. -/
theorem eq_of_eq_or_eq_neg (σ : S.Signing I) {i j : I} (h : σ i = σ j ∨ σ i = -σ j) :
    i = j := by
  rcases h with h | h
  · have := σ.bijOn.injOn (Set.mem_univ (i, false)) (Set.mem_univ (j, false))
      (by simpa [signedVec] using h)
    exact congrArg Prod.fst this
  · have := σ.bijOn.injOn (Set.mem_univ (i, false)) (Set.mem_univ (j, true))
      (by simpa [signedVec] using h)
    exact absurd (congrArg Prod.snd this) (by simp)

end Signing

-- The matrix C before Theorem 3.7
/-- The paragraph before Theorem 3.7 of [CGSS] (p. 312): off the diagonal, the matrix
`C` has entries `0, 1, -1`. The values `±2` would put two chosen vectors on one line. -/
theorem signedAdj_apply_mem {S : LineSystem V} {I : Type*} [DecidableEq I] (σ : S.Signing I)
    {i j : I} (hij : i ≠ j) : signedAdj σ i j ∈ ({-1, 0, 1} : Set ℝ) := by
  have he : signedAdj σ i j = ⟪σ i, σ j⟫ := by
    simp [signedAdj, Matrix.one_apply_ne hij]
  rw [he]
  rcases S.inner_mem _ (σ.mem i) _ (σ.mem j) with h | h | h | h | h
  · refine absurd (σ.eq_of_eq_or_eq_neg (Or.inr ?_)) hij
    refine (S.inner_eq_two_iff (σ.mem i) (S.neg_mem _ (σ.mem j))).1 ?_
    rw [inner_neg_right, h, neg_neg]
  · simp [h]
  · simp [h]
  · simp [h]
  · exact absurd (σ.eq_of_eq_or_eq_neg
      (Or.inl ((S.inner_eq_two_iff (σ.mem i) (σ.mem j)).1 h))) hij

-- The matrix C before Theorem 3.7
/-- For the paragraph before Theorem 3.7 of [CGSS] (p. 312): if the signing `τ` takes
on the line `e i` the vector `ε i • σ i`, with signs `ε i = ±1`, then its matrix is that of `σ`
switched by `ε` and relabelled by `e`. -/
theorem signedAdj_submatrix_of_eq_smul {S : LineSystem V} {I J : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq J] (σ : S.Signing I) (τ : S.Signing J) {e : I → J}
    (he : Function.Injective e) {ε : I → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hτ : ∀ i, τ (e i) = ε i • σ i) :
    (signedAdj τ).submatrix e e = Matrix.diagonal ε * signedAdj σ * Matrix.diagonal ε := by
  ext i j
  simp only [Matrix.submatrix_apply, signedAdj, Matrix.sub_apply, Matrix.gram_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, hτ,
    real_inner_smul_left, real_inner_smul_right, Matrix.one_apply, he.eq_iff]
  split_ifs with hij
  · subst hij
    have hsq : ε i * ε i = 1 := by rcases hε i with h | h <;> rw [h] <;> norm_num
    rw [S.inner_self _ (σ.mem i)]
    linear_combination 2 * hsq
  · ring

-- The matrix C before Theorem 3.7
/-- The paragraph before Theorem 3.7 of [CGSS] (p. 312): the matrix `C` is determined by
the line system up to switching. Two signings with the same indexing of the lines differ by the
signs `ε i = ±1`, and their matrices by conjugation with the diagonal matrix of `ε`. -/
theorem exists_signedAdj_eq_switch {S : LineSystem V} {I : Type*} [Fintype I] [DecidableEq I]
    (σ τ : S.Signing I) (h : ∀ i, τ i = σ i ∨ τ i = -σ i) :
    ∃ ε : I → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      signedAdj τ = Matrix.diagonal ε * signedAdj σ * Matrix.diagonal ε := by
  classical
  let ε : I → ℝ := fun i ↦ if τ i = σ i then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i ↦ by
    simp only [ε]
    split_ifs <;> simp
  have hτ : ∀ i, τ (id i) = ε i • σ i := fun i ↦ by
    simp only [ε, id]
    split_ifs with hi
    · rw [hi, one_smul]
    · rcases h i with h' | h'
      · exact absurd h' hi
      · rw [h', neg_smul, one_smul]
  have := signedAdj_submatrix_of_eq_smul σ τ Function.injective_id hε hτ
  rw [Matrix.submatrix_id_id] at this
  exact ⟨ε, hε, this⟩

-- The matrix C before Theorem 3.7
/-- The paragraph before Theorem 3.7 of [CGSS] (p. 312), for two arbitrary signings of
one line system: after relabelling the lines by a bijection `e`, the matrices differ by
switching with signs `ε i = ±1`. -/
theorem exists_signedAdj_submatrix {S : LineSystem V} {I J : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq J] (σ : S.Signing I) (τ : S.Signing J) :
    ∃ e : I ≃ J, ∃ ε : I → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (signedAdj τ).submatrix e e = Matrix.diagonal ε * signedAdj σ * Matrix.diagonal ε := by
  classical
  choose f hf using fun i ↦ τ.exists_eq_or_eq_neg (σ.mem i)
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply σ.eq_of_eq_or_eq_neg
    have h₁ := hf i
    have h₂ := hf i'
    rw [hii'] at h₁
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact Or.inl (by rw [h₁, h₂])
    · exact Or.inr (by rw [h₁, h₂, neg_neg])
    · exact Or.inr (by rw [h₁, h₂])
    · exact Or.inl (by rw [h₁, h₂])
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := σ.exists_eq_or_eq_neg (τ.mem j)
    refine ⟨i, τ.eq_of_eq_or_eq_neg ?_⟩
    rcases hf i with h₁ | h₁ <;> rcases hi with h₂ | h₂
    · exact Or.inl (by rw [h₂, h₁])
    · exact Or.inr (by rw [h₂, h₁, neg_neg])
    · exact Or.inr (by rw [h₂, h₁, neg_neg])
    · exact Or.inl (by rw [h₂, h₁, neg_neg])
  let ε : I → ℝ := fun i ↦ if σ i = τ (f i) then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i ↦ by
    simp only [ε]
    split_ifs <;> simp
  have hτ : ∀ i, τ (f i) = ε i • σ i := fun i ↦ by
    simp only [ε]
    split_ifs with hi
    · rw [hi, one_smul]
    · rcases hf i with h' | h'
      · exact absurd h' hi
      · rw [h', neg_smul, one_smul, neg_neg]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ε, hε,
    signedAdj_submatrix_of_eq_smul σ τ hinj hε hτ⟩

end LineSystem

/-! ### Theorem 3.10: the scaling of root sets -/

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.10
/-- For Theorem 3.10 of [CGSS] (p. 314): a nonzero multiple of a Root System of
Definition 3.9 is a Root System. -/
theorem smul {Φ : Set V} (hΦ : IsRootSet Φ) {c : ℝ} (hc : c ≠ 0) : IsRootSet (c • Φ) := by
  have hk (r s : V) : 2 * ⟪c • r, c • s⟫ / ⟪c • r, c • r⟫ = 2 * ⟪r, s⟫ / ⟪r, r⟫ := by
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [show 2 * (c * (c * ⟪r, s⟫)) = c * c * (2 * ⟪r, s⟫) by ring,
      show c * (c * ⟪r, r⟫) = c * c * ⟪r, r⟫ by ring, mul_div_mul_left _ _ (mul_ne_zero hc hc)]
  refine ⟨hΦ.finite.smul_set, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨r, hr, hr0⟩ := Set.mem_smul_set.mp h0
    exact hΦ.ne_zero hr ((smul_eq_zero.mp hr0).resolve_left hc)
  · rw [span_smul_eq_of_isUnit _ _ hc.isUnit, hΦ.span_eq_top]
  · intro r' hr' s' hs'
    obtain ⟨r, hr, rfl⟩ := Set.mem_smul_set.mp hr'
    obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.mp hs'
    rw [hk]
    exact hΦ.crystallographic r hr s hs
  · intro r' hr' t ht
    obtain ⟨r, hr, rfl⟩ := Set.mem_smul_set.mp hr'
    obtain ⟨s, hs, hts⟩ := Set.mem_smul_set.mp ht
    have h : s = t • r := smul_right_injective V hc (by
      change c • s = c • t • r
      rw [hts, smul_comm])
    exact hΦ.reduced r hr t (h ▸ hs)
  · intro r' hr' s' hs'
    obtain ⟨r, hr, rfl⟩ := Set.mem_smul_set.mp hr'
    obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.mp hs'
    rw [hk, ← smul_comm c, ← smul_sub]
    exact Set.smul_mem_smul_set (hΦ.reflection_mem r hr s hs)

-- Theorem 3.10
/-- For Theorem 3.10 of [CGSS] (p. 314): Definition 3.9 is invariant under nonzero
scaling, which is the "without loss of generality" of the proof (p. 314). -/
theorem smul_iff {Φ : Set V} {c : ℝ} (hc : c ≠ 0) : IsRootSet (c • Φ) ↔ IsRootSet Φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul hc⟩
  have := h.smul (inv_ne_zero hc)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end IsRootSet

namespace LineSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Theorem 3.10
/-- Theorem 3.10 of [CGSS] (p. 314) with clause (i) at any fixed length (p. 314): for a
spanning set `Φ` of vectors of squared norm `2 c²`, `c ≠ 0`, the following are equivalent: `Φ` is
a Root System of Definition 3.9; the rescaled vectors `c⁻¹ • Φ`, of squared norm 2, form a
star-closed line system; they form an orthogonal sum of the models `A_n, D_n, E₈, E₇, E₆`. -/
theorem isRootSet_tfae_of_inner_self_eq (Φ : Set V) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ r ∈ Φ, ⟪r, r⟫ = 2 * c ^ 2) (hspan : span ℝ Φ = ⊤) :
    List.TFAE [IsRootSet Φ,
      ∃ S : LineSystem V, S.Φ = c⁻¹ • Φ ∧ S.IsStarClosed,
      ∃ S : LineSystem V, S.Φ = c⁻¹ • Φ ∧ S.IsOrthogonalSumOfModels] := by
  have h₂ : ∀ r ∈ c⁻¹ • Φ, ⟪r, r⟫ = 2 := by
    intro r' hr'
    obtain ⟨r, hr, rfl⟩ := Set.mem_smul_set.mp hr'
    rw [real_inner_smul_left, real_inner_smul_right, h r hr]
    field_simp
  have hspan' : span ℝ (c⁻¹ • Φ) = ⊤ := by
    rw [span_smul_eq_of_isUnit _ _ (inv_ne_zero hc).isUnit, hspan]
  have H := isRootSet_tfae_of_inner_self_eq_two (c⁻¹ • Φ) h₂ hspan'
  tfae_have 1 ↔ 2 := (IsRootSet.smul_iff (inv_ne_zero hc)).symm.trans (H.out 1 2)
  tfae_have 2 ↔ 3 := H.out 2 3
  tfae_finish

end LineSystem

/-! ### Lemma 2.9: the role of `x` -/

namespace SimpleGraph.HasTriangleProperty

variable {U : Type*} {X : SimpleGraph U}

-- Lemma 2.9
/-- Lemma 2.9 of [CGSS] (p. 308), in pure graph form, with the isomorphism sending the
universal vertex `x` to the common vertex `none` of the triangles. The construction is that of
`nonempty_iso_friendship_of_forall_adj`. -/
theorem exists_iso_friendship_apply_eq_none (hX : X.HasTriangleProperty) [Finite U] (x : U)
    (hx : ∀ y, y ≠ x → X.Adj x y) : ∃ m, ∃ e : X ≃g friendship m, e x = none := by
  classical
  obtain ⟨m, e, he⟩ := hX.exists_neighbor_pair_labels x
  let e' : X.neighborSet x ≃ {y // y ≠ x} :=
    Equiv.subtypeEquivRight (fun y ↦ ⟨fun hy ↦ hy.ne.symm, hx y⟩)
  let E : Option (Fin m × Bool) ≃ U :=
    (Equiv.optionCongr (e.trans e')).trans (Equiv.optionSubtypeNe x)
  have hE : ∀ {a b : Option (Fin m × Bool)}, X.Adj (E a) (E b) ↔ (friendship m).Adj a b := by
    rintro (_ | p) (_ | q)
    · exact iff_of_false X.irrefl (by simp [friendship])
    · change X.Adj x (e q) ↔ True
      exact iff_true_intro (e q).property
    · change X.Adj (e p) x ↔ True
      exact iff_true_intro (e p).property.symm
    · exact he p q
  let F : friendship m ≃g X := ⟨E, fun {_ _} ↦ hE⟩
  have hF : F none = x := rfl
  exact ⟨m, F.symm, by rw [← hF, RelIso.symm_apply_apply]⟩

end SimpleGraph.HasTriangleProperty

namespace LineSystem.Hyp24

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Lemma 2.9
/-- Lemma 2.9 of [CGSS] (p. 308), as `orthGraph_iso_friendship_of_forall_adj`, with the
isomorphism sending `x` to the common vertex `none` of the triangles. For `m ≥ 2` every
isomorphism does so; for `m ≤ 1` the graph is a point or a triangle. -/
theorem exists_iso_friendship_apply_eq_none (H : Hyp24 V) (x : H.Γa)
    (hx : ∀ y, y ≠ x → H.orthGraph.Adj x y) :
    ∃ m, ∃ e : H.orthGraph ≃g SimpleGraph.friendship m, e x = none :=
  H.orthGraph_hasTriangleProperty.exists_iso_friendship_apply_eq_none x hx

end LineSystem.Hyp24
