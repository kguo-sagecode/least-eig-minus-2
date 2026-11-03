/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.IntegerModel
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Frames, signings and the Gram polynomial

The frame operator of a line system is `x ↦ ∑_{r ∈ Φ} ⟪r, x⟫ r`. Computation C6 shows that for
each model it is a scalar on the span of `Φ` (not on the ambient space: `An n` and `E₇`, `E₆` do
not span it). This file contains the part of C6 and of Theorem 3.7 that is independent of the
models (`blueprint/sec3-rootsystems.tex`, Definition "signings", Lemmas "the frame identity
within the span" and "the Gram polynomial from a frame").

## Main definitions

* `LineSystem.frameSum`: the frame operator of the full signed root set.
* `LineSystem.IsFrame S t`: the frame operator is `t` times the identity on `span Φ`.
* `LineSystem.Signing S I`: one vector on each line, indexed by `I`; the map
  `(i, ε) ↦ ε σ(i)` is a bijection `I × Bool → Φ`.
* `LineSystem.signedAdj σ`: the matrix `C = M - 2I` of Theorem 3.7, where `M` is the Gram matrix.

## Main statements

* `LineSystem.isFrame_iff_gram`: the frame identity is equivalent to an identity between inner
  products of roots, so (`LineSystem.Iso.isFrame`) it is invariant under isomorphism.
* `LineSystem.Signing.frameSum_eq`: the full-root sum is twice the signing sum.
* `LineSystem.IntegerModel.frameSum_apply`: the frame operator of an integer model in
  coordinates, through the integer matrix `K = ∑ v vᵀ` of C6.
* `LineSystem.signedAdj_quadratic_of_frame`: a frame gives `(C + 2I)(C - (t - 2)I) = 0`.
-/

open scoped RealInnerProductSpace
open Finset Submodule

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The frame operator of the full signed root set, `x ↦ ∑_{r ∈ Φ} ⟪r, x⟫ r`. -/
noncomputable def frameSum (S : LineSystem V) (x : V) : V :=
  ∑ r ∈ S.finite.toFinset, ⟪r, x⟫ • r

theorem inner_frameSum (S : LineSystem V) (x y : V) :
    ⟪S.frameSum x, y⟫ = ∑ r ∈ S.finite.toFinset, ⟪r, x⟫ * ⟪r, y⟫ := by
  simp only [frameSum, sum_inner, real_inner_smul_left]

theorem frameSum_mem_span (S : LineSystem V) (x : V) : S.frameSum x ∈ span ℝ S.Φ :=
  Submodule.sum_mem _ fun _ hr =>
    Submodule.smul_mem _ _ (subset_span (S.finite.mem_toFinset.mp hr))

/-- A vector of the span that is orthogonal to every root is zero. -/
theorem eq_zero_of_mem_span_of_forall_inner (S : LineSystem V) {y : V}
    (hy : y ∈ span ℝ S.Φ) (h : ∀ r ∈ S.Φ, ⟪y, r⟫ = 0) : y = 0 := by
  have hz : ∀ z ∈ span ℝ S.Φ, ⟪y, z⟫ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => exact inner_zero_right _
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [real_inner_smul_right, ha, mul_zero]
  exact inner_self_eq_zero.mp (hz y hy)

/-- The frame identity within the span: the frame operator is `t` times the identity on
`span Φ`. This auxiliary identity is Computation C6 of the blueprint
`lem:sec3-frame`, used for Theorem 3.7 of [CGSS] (errata, Error 1); its scalar-identity
form holds on the span of the roots. -/
def IsFrame (S : LineSystem V) (t : ℝ) : Prop :=
  ∀ x ∈ span ℝ S.Φ, S.frameSum x = t • x

/-- The frame identity is an identity between inner products of roots. -/
theorem isFrame_iff_gram (S : LineSystem V) (t : ℝ) :
    S.IsFrame t ↔ ∀ r ∈ S.Φ, ∀ s ∈ S.Φ,
      ∑ u ∈ S.finite.toFinset, ⟪u, r⟫ * ⟪u, s⟫ = t * ⟪r, s⟫ := by
  constructor
  · intro h r hr s hs
    rw [← inner_frameSum, h r (subset_span hr), real_inner_smul_left]
  · intro h x hx
    have key : ∀ s ∈ S.Φ, ⟪S.frameSum x - t • x, s⟫ = 0 := by
      intro s hs
      rw [inner_sub_left, inner_frameSum, real_inner_smul_left, sub_eq_zero]
      induction hx using Submodule.span_induction with
      | mem r hr => exact h r hr s hs
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [inner_add_right, inner_add_left, add_mul, Finset.sum_add_distrib, ha, hb,
          mul_add]
      | smul c a _ ha =>
        simp only [real_inner_smul_right, real_inner_smul_left, mul_assoc,
          ← Finset.mul_sum, ha]
        ring
    exact sub_eq_zero.mp (S.eq_zero_of_mem_span_of_forall_inner
      (sub_mem (S.frameSum_mem_span x) (smul_mem _ _ hx)) key)

/-- An isomorphism carries sums over the roots of the target to sums over the source. -/
theorem Iso.sum_toFinset {S : LineSystem V} {T : LineSystem W} (e : S.Iso T)
    (f : W → ℝ) (g : V → ℝ) (hfg : ∀ r (hr : r ∈ S.Φ), f (e.toEquiv ⟨r, hr⟩) = g r) :
    ∑ u ∈ T.finite.toFinset, f u = ∑ u ∈ S.finite.toFinset, g u := by
  symm
  apply Finset.sum_bij (fun u hu => (e.toEquiv ⟨u, S.finite.mem_toFinset.mp hu⟩ : W))
  · intro u _
    exact T.finite.mem_toFinset.mpr (Subtype.property _)
  · intro u _ u' _ h
    exact congrArg Subtype.val (e.toEquiv.injective (Subtype.ext h))
  · intro w hw
    obtain ⟨⟨u, hu⟩, he⟩ := e.toEquiv.surjective ⟨w, T.finite.mem_toFinset.mp hw⟩
    exact ⟨u, S.finite.mem_toFinset.mpr hu, by rw [he]⟩
  · intro u hu
    exact (hfg u _).symm

/-- The frame identity is invariant under isomorphism: no ambient map is needed. -/
theorem Iso.isFrame {S : LineSystem V} {T : LineSystem W} (e : S.Iso T) {t : ℝ}
    (hT : T.IsFrame t) : S.IsFrame t := by
  rw [isFrame_iff_gram] at hT ⊢
  intro r hr s hs
  have h := hT _ (e.toEquiv ⟨r, hr⟩).2 _ (e.toEquiv ⟨s, hs⟩).2
  rw [e.inner_map] at h
  rw [← h]
  refine (e.sum_toFinset _ _ fun u hu => ?_).symm
  rw [e.inner_map ⟨u, hu⟩ ⟨r, hr⟩, e.inner_map ⟨u, hu⟩ ⟨s, hs⟩]

/-- The two signs of a family: `(i, false) ↦ v i` and `(i, true) ↦ -v i`. -/
def signedVec {I : Type*} (v : I → V) (p : I × Bool) : V :=
  if p.2 then -v p.1 else v p.1

/-- A signing (Definition "signings" of `blueprint/sec3-rootsystems.tex`): one vector of `Φ` on
each line, indexed by `I`, so that `(i, ε) ↦ ε σ(i)` is a bijection `I × Bool → Φ`. -/
structure Signing (S : LineSystem V) (I : Type*) where
  /-- The chosen vector on each line. -/
  toFun : I → V
  /-- With both signs, the chosen vectors are the roots, each once. -/
  bijOn : Set.BijOn (signedVec toFun) Set.univ S.Φ

-- Theorem 3.7
/-- Theorem 3.7 of [CGSS]: every line system admits a signing, indexed by its
number of lines. This includes the empty system. -/
theorem nonempty_signing (S : LineSystem V) : Nonempty (S.Signing (Fin S.numLines)) := by
  classical
  let : LinearOrder V := linearOrderOfSTO WellOrderingRel
  let R : Set V := {r | r ∈ S.Φ ∧ r < -r}
  let : Fintype R := (S.finite.subset fun _ h => h.1).fintype
  have hne (r : V) (hr : r ∈ S.Φ) : r ≠ -r := by
    intro h
    have he := congrArg (fun s => ⟪r, s⟫) h
    rw [S.inner_self r hr, inner_neg_right, S.inner_self r hr] at he
    norm_num at he
  have hsign : Set.BijOn (signedVec (fun r : R => (r : V))) Set.univ S.Φ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r, b⟩ _
      cases b
      · exact r.property.1
      · exact S.neg_mem _ r.property.1
    · rintro ⟨r, a⟩ _ ⟨s, b⟩ _ he
      cases a <;> cases b <;> simp only [signedVec, Bool.false_eq_true, ↓reduceIte] at he
      · exact Prod.ext (Subtype.ext he) rfl
      · have hs := s.property.2
        rw [← he] at hs
        exact False.elim ((lt_asymm r.property.2) (by simpa [he] using hs))
      · have hr := r.property.2
        rw [he] at hr
        exact False.elim ((lt_asymm s.property.2) (by simpa [← he] using hr))
      · exact Prod.ext (Subtype.ext (neg_injective he)) rfl
    · intro r hr
      rcases lt_or_gt_of_ne (hne r hr) with h | h
      · exact ⟨(⟨r, hr, h⟩, false), Set.mem_univ _, rfl⟩
      · exact ⟨(⟨-r, S.neg_mem r hr, by simpa using h⟩, true), Set.mem_univ _,
          by simp [signedVec]⟩
  let e : (R × Bool) ≃ S.Φ := Equiv.ofBijective
    (fun p => ⟨signedVec (fun r : R => (r : V)) p, hsign.mapsTo (Set.mem_univ p)⟩)
    ⟨fun _ _ h => hsign.injOn (Set.mem_univ _) (Set.mem_univ _)
        (congrArg Subtype.val h), fun r => by
      obtain ⟨p, _, hp⟩ := hsign.surjOn r.property
      exact ⟨p, Subtype.ext hp⟩⟩
  let := S.finite.fintype
  have hc : Fintype.card R = S.numLines := by
    have he := Fintype.card_congr e
    have hΦcard : Fintype.card S.Φ = S.Φ.ncard := Set.fintypeCard_eq_ncard _
    rw [Fintype.card_prod, Fintype.card_bool, hΦcard] at he
    dsimp [numLines]
    omega
  let f : Fin S.numLines ≃ R := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨⟨fun i => (f i : V), ?_⟩⟩
  refine ⟨fun p _ => hsign.mapsTo (Set.mem_univ (f p.1, p.2)), ?_, ?_⟩
  · intro p _ q _ h
    have he : (f p.1, p.2) = (f q.1, q.2) :=
      hsign.injOn (Set.mem_univ _) (Set.mem_univ _) h
    exact Prod.ext (f.injective (congrArg Prod.fst he)) (congrArg (fun z : R × Bool => z.2) he)
  · intro r hr
    obtain ⟨⟨i, b⟩, _, hi⟩ := hsign.surjOn hr
    exact ⟨(f.symm i, b), Set.mem_univ _, by simpa [signedVec] using hi⟩

namespace Signing

variable {S : LineSystem V} {I : Type*}

instance : CoeFun (S.Signing I) fun _ => I → V := ⟨Signing.toFun⟩

theorem mem (σ : S.Signing I) (i : I) : σ i ∈ S.Φ :=
  σ.bijOn.mapsTo (Set.mem_univ (i, false))

/-- The full-root frame sum is twice the signing sum. -/
theorem frameSum_eq [Fintype I] (σ : S.Signing I) (x : V) :
    S.frameSum x = (2 : ℝ) • ∑ i, ⟪σ i, x⟫ • σ i := by
  classical
  have h : S.frameSum x = ∑ p : I × Bool, ⟪signedVec σ.toFun p, x⟫ • signedVec σ.toFun p := by
    symm
    apply Finset.sum_nbij (signedVec σ.toFun)
    · intro p _
      exact S.finite.mem_toFinset.mpr (σ.bijOn.mapsTo (Set.mem_univ p))
    · intro p _ q _ hpq
      exact σ.bijOn.injOn (Set.mem_univ p) (Set.mem_univ q) hpq
    · intro r hr
      obtain ⟨p, _, hp⟩ := σ.bijOn.surjOn (S.finite.mem_toFinset.mp hr)
      exact ⟨p, Finset.mem_coe.mpr (Finset.mem_univ p), hp⟩
    · intro p _
      rfl
  rw [h, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.sum_bool, signedVec, ite_true, Bool.false_eq_true, ite_false,
    inner_neg_left, neg_smul, smul_neg, neg_neg]
  rw [two_smul]

/-- A frame of the full root set gives a frame of any signing, with half the constant. -/
theorem sum_eq_of_isFrame [Fintype I] (σ : S.Signing I) {t : ℝ} (h : S.IsFrame t)
    {x : V} (hx : x ∈ span ℝ S.Φ) : ∑ i, ⟪σ i, x⟫ • σ i = (t / 2) • x := by
  have h2 := h x hx
  rw [σ.frameSum_eq] at h2
  have : ∑ i, ⟪σ i, x⟫ • σ i = (1 / 2 : ℝ) • ((2 : ℝ) • ∑ i, ⟪σ i, x⟫ • σ i) := by
    rw [smul_smul]
    norm_num
  rw [this, h2, smul_smul]
  ring_nf

end Signing

/-- The signed adjacency matrix `C` before Theorem 3.7 of [CGSS]: its Gram matrix
is `2I + C`. Theorem 3.7 is proved for every signing and every index type, so its
proofs need neither a separate switching-invariance theorem nor a theorem listing
the off-diagonal entries. -/
noncomputable def signedAdj {S : LineSystem V} {I : Type*} [DecidableEq I] (σ : S.Signing I) :
    Matrix I I ℝ :=
  Matrix.gram ℝ σ.toFun - (2 : ℝ) • (1 : Matrix I I ℝ)

theorem signedAdj_add_two {S : LineSystem V} {I : Type*} [DecidableEq I] (σ : S.Signing I) :
    signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ) = Matrix.gram ℝ σ.toFun := by
  simp [signedAdj]

/-- The diagonal of `C` is zero. -/
theorem signedAdj_apply_self {S : LineSystem V} {I : Type*} [DecidableEq I] (σ : S.Signing I)
    (i : I) : signedAdj σ i i = 0 := by
  have h := S.inner_self _ (σ.mem i)
  simp only [signedAdj, Matrix.sub_apply, Matrix.gram_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [h, sub_self]

-- Lemma "the Gram polynomial from a frame"
/-- The Gram polynomial from a frame (blueprint, `lem:sec3-gram-polynomial`): if
`∑ᵢ ⟪σ i, x⟫ σ i = t x` on `span Φ`, then `M² = t M` for the Gram matrix `M = 2I + C`. -/
theorem gram_mul_self_of_frame {S : LineSystem V} {I : Type*} [Fintype I] (σ : S.Signing I)
    {t : ℝ} (h : ∀ x ∈ span ℝ S.Φ, ∑ i, ⟪σ i, x⟫ • σ i = t • x) :
    Matrix.gram ℝ σ.toFun * Matrix.gram ℝ σ.toFun = t • Matrix.gram ℝ σ.toFun := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.gram_apply, Matrix.smul_apply, smul_eq_mul]
  have hj := h (σ j) (subset_span (σ.mem j))
  have hij := congrArg (fun y => ⟪σ i, y⟫) hj
  simp only [inner_sum, real_inner_smul_right] at hij
  rw [← hij]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

-- Lemma "the Gram polynomial from a frame"
/-- The Gram polynomial from a frame (blueprint, `lem:sec3-gram-polynomial`):
`(C + 2I)(C - (t - 2)I) = 0`. -/
theorem signedAdj_quadratic_of_frame {S : LineSystem V} {I : Type*} [Fintype I] [DecidableEq I]
    (σ : S.Signing I) {t : ℝ} (h : ∀ x ∈ span ℝ S.Φ, ∑ i, ⟪σ i, x⟫ • σ i = t • x) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (t - 2) • (1 : Matrix I I ℝ)) = 0 := by
  have hM := gram_mul_self_of_frame σ h
  have hC : signedAdj σ - (t - 2) • (1 : Matrix I I ℝ) =
      Matrix.gram ℝ σ.toFun - t • (1 : Matrix I I ℝ) := by
    rw [signedAdj, sub_smul]
    abel
  rw [signedAdj_add_two, hC, Matrix.mul_sub, hM, Matrix.mul_smul, Matrix.mul_one, sub_self]

/-- A frame of the full root set, with constant `t`, gives `(C + 2I)(C - (t/2 - 2)I) = 0` for
every signing. -/
theorem signedAdj_quadratic_of_isFrame {S : LineSystem V} {I : Type*} [Fintype I]
    [DecidableEq I] (σ : S.Signing I) {t : ℝ} (h : S.IsFrame t) :
    (signedAdj σ + (2 : ℝ) • (1 : Matrix I I ℝ)) *
      (signedAdj σ - (t / 2 - 2) • (1 : Matrix I I ℝ)) = 0 :=
  signedAdj_quadratic_of_frame σ fun _ hx => σ.sum_eq_of_isFrame h hx

/-- The frame operator of an integer model in coordinates: `(∑ r ⟪r, x⟫ r)ₖ = c² (K x)ₖ` for the
integer matrix `K = ∑ₐ vₐ vₐᵀ` of computation C6. -/
theorem IntegerModel.frameSum_apply {n : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin n))}
    (M : IntegerModel S) (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    S.frameSum x k =
      M.c * M.c * ∑ j, ((∑ a, M.v a k * M.v a j : ℤ) : ℝ) * x j := by
  rw [frameSum, M.sum_Φ]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.inner_apply, integerVector_apply, RCLike.inner_apply, conj_trivial, smul_eq_mul,
    Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

end LineSystem
