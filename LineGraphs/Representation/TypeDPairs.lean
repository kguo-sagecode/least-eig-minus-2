/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Basic
import LineGraphs.LineSystem.Models

/-!
# The pairs in a type D representation

Coordinate lemmas for Theorem 4.2 of [CGSS], especially step `s42petal` of the blueprint
(Gap 19). A petal coordinate in a pair occurs at precisely the two vertices of the pair.
-/

open scoped RealInnerProductSpace
open EuclideanSpace

namespace LineSystem.Dn

/-- Theorem 4.2 of [CGSS], step `s42form`: every root is a signed pair of coordinate vectors. -/
theorem mem_iff_exists_signed_single {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ (Dn n).Φ ↔ ∃ (i j : Fin n) (b c : Bool), i ≠ j ∧
      x = single i (rootSign b : ℝ) + single j (rootSign c : ℝ) := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.1.1.1, p.1.1.2, p.2.1, p.2.2, p.1.2.ne, ?_⟩
    ext k
    simp [integerVector, dnRoot, pairVector, Pi.single_apply, PiLp.single_apply]
  · rintro ⟨i, j, b, c, hij, rfl⟩
    obtain ⟨p, hp⟩ := exists_dnRoot_eq_pairVector i j hij b c
    refine ⟨p, ?_⟩
    ext k
    simp [integerVector, hp, pairVector, Pi.single_apply, PiLp.single_apply]

/-- Theorem 4.2 of [CGSS], step `s42form`: coordinates belong to `{0, 1, -1}`. -/
theorem apply_eq_zero_or_one_or_neg_one {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (Dn n).Φ) (k : Fin n) : x k = 0 ∨ x k = 1 ∨ x k = -1 := by
  obtain ⟨i, j, b, c, hij, rfl⟩ := mem_iff_exists_signed_single.mp hx
  cases b <;> cases c <;>
    simp only [PiLp.add_apply, PiLp.single_apply, rootSign, Bool.false_eq_true,
      ite_false, ite_true, Int.cast_one, Int.cast_neg]
  all_goals by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Theorem 4.2 of [CGSS], step `s42form`: orient a signed pair around a nonzero coordinate. -/
theorem exists_signed_single_of_apply_ne_zero {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (Dn n).Φ) {p : Fin n} (hp : x p ≠ 0) :
    ∃ (c : Fin n) (b d : Bool), c ≠ p ∧
      x = single c (rootSign b : ℝ) + single p (rootSign d : ℝ) := by
  obtain ⟨i, j, b, d, hij, hform⟩ := mem_iff_exists_signed_single.mp hx
  have hs : p = i ∨ p = j := by
    by_contra h
    push Not at h
    apply hp
    rw [hform]
    simp [h.1, h.2]
  rcases hs with rfl | rfl
  · exact ⟨j, d, b, hij.symm, hform.trans (add_comm _ _)⟩
  · exact ⟨i, b, d, hij, hform⟩

end LineSystem.Dn

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {X : SimpleGraph V} [DecidableRel X.Adj]
  {n : ℕ} {x : V → EuclideanSpace ℝ (Fin n)}

/-- Theorem 4.2 of [CGSS], Gap 19: all unordered pairs of distinct vertices with
equal coordinate supports. For a type D representation these pairs are disjoint. -/
def representationPairs (x : V → EuclideanSpace ℝ (Fin n)) : Set (Sym2 V) :=
  {e | ∃ u v, u ≠ v ∧
    Function.support (fun i ↦ x u i) = Function.support (fun i ↦ x v i) ∧ e = s(u, v)}

/-- Theorem 4.2 of [CGSS], steps `s42same` and `s42onesign`: opposite coefficients
at a coordinate force a pair, with the same signed centre at the other coordinate. -/
theorem IsRepresentation.exists_pair_of_opposite_coordinates (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v : V} {p : Fin n}
    (hu : x u p = 1) (hv : x v p = -1) :
    ∃ (c : Fin n) (b : Bool), c ≠ p ∧
      x u = single c (LineSystem.rootSign b : ℝ) + single p 1 ∧
      x v = single c (LineSystem.rootSign b : ℝ) - single p 1 := by
  obtain ⟨c, b, d, hcp, huf⟩ :=
    LineSystem.Dn.exists_signed_single_of_apply_ne_zero (hm u) (by rw [hu]; norm_num)
  obtain ⟨c', b', d', hcp', hvf⟩ :=
    LineSystem.Dn.exists_signed_single_of_apply_ne_zero (hm v) (by rw [hv]; norm_num)
  have hxu : x u = single c (LineSystem.rootSign b : ℝ) + single p 1 := by
    cases d with
    | false => simpa [LineSystem.rootSign] using huf
    | true =>
      have h := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y p) huf
      norm_num [hu, hcp.symm, LineSystem.rootSign] at h
  have hxv : x v = single c' (LineSystem.rootSign b' : ℝ) + single p (-1) := by
    cases d' with
    | true => simpa [LineSystem.rootSign] using hvf
    | false =>
      have h := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y p) hvf
      norm_num [hv, hcp'.symm, LineSystem.rootSign] at h
  have hcc : c = c' := by
    by_contra hcc
    have hn := hx.inner_nonneg u v
    norm_num [hxu, hxv, inner_add_left, inner_add_right, inner_single_left, hcc,
      hcp, hcp'.symm] at hn
  subst c'
  have hbb : b = b' := by
    cases b <;> cases b'
    · rfl
    · have hn := hx.inner_nonneg u v
      norm_num [hxu, hxv, LineSystem.rootSign, inner_add_left, inner_add_right,
        inner_single_left, hcp, hcp.symm] at hn
    · have hn := hx.inner_nonneg u v
      norm_num [hxu, hxv, LineSystem.rootSign, inner_add_left, inner_add_right,
        inner_single_left, hcp, hcp.symm] at hn
    · rfl
  subst b'
  refine ⟨c, b, hcp, hxu, ?_⟩
  rw [hxv]
  ext i
  simp [PiLp.single_apply]
  split_ifs <;> ring

/-- Theorem 4.2 of [CGSS], step `s42petal` (Gap 19): a coordinate on which a pair has
opposite unit coefficients occurs at no third vertex. The difference of the two inner
products is twice an integer coordinate, whereas both off-diagonal products are zero or one. -/
theorem IsRepresentation.eq_or_eq_of_petal_ne_zero (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v w : V} {c p : Fin n} {s t : ℝ}
    (hu : x u = single c s + single p t) (hv : x v = single c s - single p t)
    (ht : t = 1 ∨ t = -1) (hw : x w p ≠ 0) : w = u ∨ w = v := by
  by_contra h
  push Not at h
  have hwu := hx.inner_eq_zero_or_one h.1.symm
  have hwv := hx.inner_eq_zero_or_one h.2.symm
  have hcoord := LineSystem.Dn.apply_eq_zero_or_one_or_neg_one (hm w) p
  have hdiff : ⟪x u, x w⟫ - ⟪x v, x w⟫ = 2 * t * x w p := by
    rw [hu, hv, inner_add_left, inner_sub_left, inner_single_left, inner_single_left]
    simp only [conj_trivial]
    ring
  rcases hcoord with hz | hz | hz
  · exact hw hz
  · rcases ht with ht | ht <;> rcases hwu with hwu | hwu <;>
      rcases hwv with hwv | hwv <;> rw [ht, hz, hwu, hwv] at hdiff <;> norm_num at hdiff
  · rcases ht with ht | ht <;> rcases hwu with hwu | hwu <;>
      rcases hwv with hwv | hwv <;> rw [ht, hz, hwu, hwv] at hdiff <;> norm_num at hdiff

/-- Theorem 4.2 of [CGSS], step `s42petal` (Gap 19): the vertices using the petal
coordinate are exactly the pair, including both signs. -/
theorem IsRepresentation.apply_ne_zero_iff_of_pair (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v : V} {c p : Fin n} {s t : ℝ}
    (hcp : c ≠ p) (hu : x u = single c s + single p t)
    (hv : x v = single c s - single p t) (ht : t = 1 ∨ t = -1) (w : V) :
    x w p ≠ 0 ↔ w = u ∨ w = v := by
  constructor
  · exact hx.eq_or_eq_of_petal_ne_zero hm hu hv ht
  · rintro (rfl | rfl) <;> rcases ht with rfl | rfl <;>
      simp [hu, hv, hcp.symm]

/-- Theorem 4.2 of [CGSS], step `s42centre` (Gap 19): two pairs with the same petal
coordinate are the same unordered pair of vertices. -/
theorem IsRepresentation.pair_eq_of_common_petal (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v u' v' : V} {c c' p : Fin n}
    {s t s' t' : ℝ} (hcp : c ≠ p) (hcp' : c' ≠ p)
    (hu : x u = single c s + single p t) (hv : x v = single c s - single p t)
    (hu' : x u' = single c' s' + single p t')
    (hv' : x v' = single c' s' - single p t')
    (ht : t = 1 ∨ t = -1) (ht' : t' = 1 ∨ t' = -1) :
    ({u, v} : Set V) = {u', v'} := by
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact (hx.apply_ne_zero_iff_of_pair hm hcp hu hv ht w).symm.trans
    (hx.apply_ne_zero_iff_of_pair hm hcp' hu' hv' ht' w)

/-- Theorem 4.2 of [CGSS], steps `s42same`--`s42petal` (Gap 19): at most two
representing roots can have the same two-coordinate support. -/
theorem IsRepresentation.eq_or_eq_of_support_eq (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v w : V} (huv : u ≠ v)
    (hsuv : Function.support (fun i ↦ x u i) = Function.support (fun i ↦ x v i))
    (hsuw : Function.support (fun i ↦ x u i) = Function.support (fun i ↦ x w i)) :
    w = u ∨ w = v := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, x u p ≠ x v p := by
    by_contra h
    push Not at h
    exact huv (hx.injective (by ext i; exact h i))
  have hs : x u p ≠ 0 ↔ x v p ≠ 0 := by
    change p ∈ Function.support (fun i ↦ x u i) ↔ p ∈ Function.support (fun i ↦ x v i)
    rw [hsuv]
  have hop : (x u p = 1 ∧ x v p = -1) ∨ (x v p = 1 ∧ x u p = -1) := by
    rcases LineSystem.Dn.apply_eq_zero_or_one_or_neg_one (hm u) p with hu | hu | hu <;>
      rcases LineSystem.Dn.apply_eq_zero_or_one_or_neg_one (hm v) p with hv | hv | hv <;>
      simp_all
  have hwp : x w p ≠ 0 := by
    change p ∈ Function.support (fun i ↦ x w i)
    rw [← hsuw]
    change x u p ≠ 0
    rcases hop with h | h <;> simp [h]
  rcases hop with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · obtain ⟨c, b, _, hxu, hxv⟩ := hx.exists_pair_of_opposite_coordinates hm hu hv
    exact hx.eq_or_eq_of_petal_ne_zero hm hxu hxv (Or.inl rfl) hwp
  · obtain ⟨c, b, _, hxv, hxu⟩ := hx.exists_pair_of_opposite_coordinates hm hv hu
    exact (hx.eq_or_eq_of_petal_ne_zero hm hxv hxu (Or.inl rfl) hwp).symm

/-- Theorem 4.2 of [CGSS], step `s42bij` (Gap 19): a vertex in a pair has a unique
partner. Consequently the collection of all equal-support pairs is already disjoint. -/
theorem IsRepresentation.existsUnique_partner_of_support_eq (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) {u v : V} (huv : u ≠ v)
    (hsuv : Function.support (fun i ↦ x u i) = Function.support (fun i ↦ x v i)) :
    ∃! w, u ≠ w ∧
      Function.support (fun i ↦ x u i) = Function.support (fun i ↦ x w i) := by
  refine ⟨v, ⟨huv, hsuv⟩, ?_⟩
  intro w hw
  exact (hx.eq_or_eq_of_support_eq hm huv hsuv hw.2).resolve_left (Ne.symm hw.1)

/-- Theorem 4.2 of [CGSS], steps `s42petal` and `s42bij` (Gap 19): all pairs are
already disjoint as sets of vertices. -/
theorem IsRepresentation.pairwise_disjoint_representationPairs (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) :
    (representationPairs x).Pairwise (fun e f ↦ Disjoint (e : Set V) (f : Set V)) := by
  have horient {e : Sym2 V} (he : e ∈ representationPairs x) {z : V} (hz : z ∈ e) :
      ∃ w, z ≠ w ∧
        Function.support (fun i ↦ x z i) = Function.support (fun i ↦ x w i) ∧ e = s(z, w) := by
    obtain ⟨u, v, huv, hs, rfl⟩ := he
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact ⟨v, huv, hs, rfl⟩
    · exact ⟨u, huv.symm, hs.symm, Sym2.eq_swap⟩
  intro e he f hf hef
  rw [Set.disjoint_left]
  intro z hze hzf
  obtain ⟨u, hzu, hsu, rfl⟩ := horient he hze
  obtain ⟨v, hzv, hsv, hfv⟩ := horient hf hzf
  have hvu : v = u := (hx.eq_or_eq_of_support_eq hm hzu hsu hsv).resolve_left hzv.symm
  exact hef (by rw [hfv, hvu])

/-- Theorem 4.2 of [CGSS], Gap 19's unique maximal set of pairs: among disjoint
collections of equal-support pairs there is exactly one inclusion-maximal collection.
It consists of all equal-support pairs. -/
theorem IsRepresentation.existsUnique_maximal_representationPairs (hx : X.IsRepresentation x)
    (hm : ∀ u, x u ∈ (LineSystem.Dn n).Φ) :
    ∃! P : Set (Sym2 V), Maximal (fun Q ↦ Q ⊆ representationPairs x ∧
      Q.Pairwise (fun e f ↦ Disjoint (e : Set V) (f : Set V))) P := by
  have hfull : representationPairs x ⊆ representationPairs x ∧
      (representationPairs x).Pairwise (fun e f ↦ Disjoint (e : Set V) (f : Set V)) :=
    ⟨Set.Subset.rfl, hx.pairwise_disjoint_representationPairs hm⟩
  refine ⟨representationPairs x, ⟨hfull, fun Q hQ _ ↦ hQ.1⟩, ?_⟩
  intro P hP
  exact Set.Subset.antisymm hP.1.1 (hP.2 hfull hP.1.1)

end SimpleGraph
