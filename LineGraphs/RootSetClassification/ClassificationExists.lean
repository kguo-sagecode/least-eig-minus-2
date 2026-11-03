/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.BaseBridge
import LineGraphs.RootSetClassification.Models
import LineGraphs.RootSetClassification.Similarity
import LineGraphs.RootSystems.Irreducible
import LineGraphs.Cartan.Classification

/-!
# Existence in the indecomposable classification

Steps `rBpairing`--`rBsimilarity` of `lem:rem-indecomp-classification` in the
blueprint for Remark 3.11 of [CGSS]. Apply blueprint Theorem A to a Mathlib base, compare
with the prescribed coordinate base, and use the root-pairing equivalence and
the common-factor lemma. Uniqueness is a separate invariant argument.
-/

open scoped RealInnerProductSpace

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Φ : Set V} (hΦ : IsRootSet Φ)

/-- Step `rBrealcartan`: the real weight-basis pairing is the cast integer Cartan matrix. -/
theorem cartanPairing_toWeightBasis [Finite Φ] (b : hΦ.toRootPairing.Base)
    (i j : b.support) : cartanPairing b.toWeightBasis i j = (b.cartanMatrix i j : ℝ) := by
  symm
  change algebraMap ℤ ℝ (b.cartanMatrixIn ℤ i j) = _
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply, hΦ.toRootPairing_pairing]
  simp only [cartanPairing, RootPairing.Base.toWeightBasis_apply]
  rfl

/-- Step `rBconnected`: the base of an indecomposable root set has connected
nonorthogonality graph, through its indecomposable finite Cartan matrix. -/
theorem connected_toWeightBasis [Finite Φ] (hI : hΦ.IsIndecomposable)
    (b : hΦ.toRootPairing.Base) : (nonorthogonalityGraph b.toWeightBasis).Connected := by
  classical
  let := hΦ.isIrreducible_of_isIndecomposable hI
  let : Nonempty Φ := hI.1.to_subtype
  obtain ⟨i₀, hi₀⟩ := b.support_nonempty
  let : Nonempty b.support := ⟨⟨i₀, hi₀⟩⟩
  have hb := b.cartanMatrix_isFiniteCartan
  have he : nonorthogonalityGraph b.toWeightBasis =
      b.cartanMatrix.supportGraph hb.zero_comm := by
    ext i j
    change (i ≠ j ∧ ⟪b.toWeightBasis i, b.toWeightBasis j⟫ ≠ 0) ↔
      (i ≠ j ∧ b.cartanMatrix i j ≠ 0)
    have hn : ⟪b.toWeightBasis j, b.toWeightBasis j⟫ ≠ 0 :=
      ne_of_gt (real_inner_self_pos.mpr (b.toWeightBasis.ne_zero j))
    have hz : b.cartanMatrix i j = 0 ↔ ⟪b.toWeightBasis i, b.toWeightBasis j⟫ = 0 := by
      rw [← Int.cast_eq_zero (α := ℝ), ← hΦ.cartanPairing_toWeightBasis]
      simp only [cartanPairing, div_eq_zero_iff, mul_eq_zero,
        OfNat.ofNat_ne_zero, false_or, hn, or_false]
    exact and_congr_right fun _ ↦ not_congr hz.symm
  rw [he]
  exact (Matrix.isIndecomposable_iff_connected_support _ hb.zero_comm).mp
    b.cartanMatrix_isIndecomposable

/-- Steps `rBpairing`--`rBsimilarity` of Remark 3.11: every indecomposable root
set is similar to a coordinate model in the canonical list of blueprint Theorem B. -/
theorem exists_similarity_model (hI : hΦ.IsIndecomposable) :
    ∃ n : ℕ, ∃ t : CartanMatrix.FiniteType n,
      ∃ f : V ≃ₗ[ℝ] RootSetModel.Space t, ∃ a : ℝ,
        IsSimilarity Φ (RootSetModel.roots t) f a := by
  classical
  let := hΦ.finite_root_index
  let := hΦ.isIrreducible_of_isIndecomposable hI
  let : Nonempty Φ := hI.1.to_subtype
  obtain ⟨b⟩ := RootPairing.nonempty_base hΦ.toRootPairing
  obtain ⟨i₀, hi₀⟩ := b.support_nonempty
  let : Nonempty b.support := ⟨⟨i₀, hi₀⟩⟩
  obtain ⟨n, e, t, ht⟩ := b.cartanMatrix_isFiniteCartan.classification
    b.cartanMatrix_isIndecomposable
  let hΨ := RootSetModel.isRootSet t
  let := hΨ.finite_root_index
  let b₂ := (RootSetModel.base t).toRootPairingBase
  let k : b.support ≃ b₂.support := e.symm.trans (RootSetModel.base t).baseIndexEquiv
  have hcart (i j : b.support) : b₂.cartanMatrix (k i) (k j) = b.cartanMatrix i j := by
    apply Int.cast_injective (α := ℝ)
    calc
      (b₂.cartanMatrix (k i) (k j) : ℝ) =
          cartanPairing (RootSetModel.simpleRoot t) (e.symm i) (e.symm j) :=
        (RootSetModel.base t).cartanMatrix_toRootPairingBase _ _
      _ = (CartanMatrix.modelEntries t (e.symm i) (e.symm j) : ℝ) :=
        RootSetModel.cartanMatrix t _ _
      _ = (b.cartanMatrix i j : ℝ) := by
        rw [ht]
        simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  let E := b.equivOfCartanMatrixEq b₂ k hcart
  let f := E.weightEquiv
  have hf (i : b.support) : f (b.toWeightBasis i) = b₂.toWeightBasis (k i) := by
    change (b.toWeightBasis.equiv b₂.toWeightBasis k) (b.toWeightBasis i) = _
    exact Module.Basis.equiv_apply _ _ _ _
  have hroots (r : Φ) : f r = ((E.indexEquiv r : RootSetModel.roots t) :
      RootSetModel.Space t) := by
    exact RootPairing.Hom.root_weightMap_apply _ _ r E.toHom
  have himage : f '' Φ = RootSetModel.roots t := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hroots ⟨x, hx⟩]
      exact (E.indexEquiv ⟨x, hx⟩).property
    · intro hy
      let r := E.indexEquiv.symm ⟨y, hy⟩
      refine ⟨r, r.property, ?_⟩
      rw [hroots]
      exact congrArg Subtype.val (E.indexEquiv.apply_symm_apply ⟨y, hy⟩)
  let β := b₂.toWeightBasis.reindex k.symm
  have he (i j : b.support) : cartanPairing b.toWeightBasis i j = cartanPairing β i j := by
    rw [hΦ.cartanPairing_toWeightBasis]
    simp only [cartanPairing, β, Module.Basis.reindex_apply, Equiv.symm_symm]
    change (b.cartanMatrix i j : ℝ) =
      cartanPairing b₂.toWeightBasis (k i) (k j)
    rw [hΨ.cartanPairing_toWeightBasis, hcart]
  obtain ⟨a, ha⟩ := similarity_of_cartanMatrix_eq b.toWeightBasis β he
    (hΦ.connected_toWeightBasis hI b) f
    (fun i ↦ by simpa only [β, Module.Basis.reindex_apply, Equiv.symm_symm] using hf i) himage
  exact ⟨n, t, f, a, ha⟩

end IsRootSet
