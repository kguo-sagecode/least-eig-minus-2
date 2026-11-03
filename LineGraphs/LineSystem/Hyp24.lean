/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Hypothesis 2.4 and Lemmas 2.3, 2.5–2.8 of [CGSS]

The sets in Hypothesis 2.4 are `Set V`, with membership in the finite signed root set bundled
into their definitions. This keeps translations, differences and orthogonal partitions literal.
The sets have `Finite` and canonical noncomputable `Fintype` instances. Cardinalities of sets use
`Set.ncard`, as in `LineSystem.numLines`; `Set.fintypeCard_eq_ncard` (or
`Nat.card_coe_set_eq` and `Nat.card_eq_fintype_card`) bridges to graph statements using
`Fintype.card`. The graph's adjacency is decidable by classical choice. No finite-dimensionality
assumption is needed: these arguments use only inner-product identities and indecomposability,
and apply equally in any real inner product space.

The three equivalences in Lemma 2.6 act on the set subtypes. Their preservation of inner products
is stated separately. Step comments follow `blueprint/sec2-lines.tex`; the elementary endpoint
identities and the cyclic calculation are factored out so that each is proved only once.

## Main definitions

* `LineSystem.Hyp24`: an indecomposable, star-closed line system with an ordered star.
* `LineSystem.Hyp24.c`, `Γa`, `Γb`, `Γc`, `Δ`, `sigmaSet`: the sets of Hypothesis 2.4.
* `LineSystem.Hyp24.orthGraph`: the orthogonality graph on `Γa`.
* `LineSystem.Hyp24.recoverySet`: the recovery expressions of Lemma 2.7.
* `LineSystem.Hyp24.third`: the third vertex on an orthogonal pair in Lemma 2.8.

## Main statements

* `LineSystem.IsMaximal.isStarClosed`: Lemma 2.3, with maximality within the root span.
* `LineSystem.Hyp24.Φ_eq_sigmaSet_union_neg`: the signed cover of Lemma 2.5.
* `LineSystem.Hyp24.ΓaEquivΓb`, `ΓbEquivΓc`, `ΓcEquivΓa`: the equivalences of Lemma 2.6.
* `LineSystem.Hyp24.inner_eq_zero_or_one`: the inner products in `Γa` from Lemma 2.6.
* `LineSystem.Hyp24.Δ_eq_sub`, `Φ_eq_recovery_union_neg`, `Φ_eq_of_Γa_eq`: Lemma 2.7.
* `LineSystem.Hyp24.image_recoverySet`, `image_Φ_eq`: recovery across two ambient spaces.
* `LineSystem.Hyp24.span_Φ_eq_span_pair_union_Γa`: the spanning assertion of step 212recover.
* `LineSystem.Hyp24.triangle`: Lemma 2.8, with the three possible product patterns.
-/

open scoped RealInnerProductSpace Pointwise

namespace LineSystem

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

-- Elementary identities
/-- The endpoint identities of the blueprint (before Definition 2.1): product 2 means equality. -/
theorem inner_eq_two_iff (S : LineSystem V) {r s : V} (hr : r ∈ S.Φ) (hs : s ∈ S.Φ) :
    ⟪r, s⟫ = 2 ↔ r = s := by
  constructor
  · intro h
    have hz : ⟪r - s, r - s⟫ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, S.inner_self r hr,
        S.inner_self s hs, real_inner_comm r s, h]
      norm_num
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  · rintro rfl
    exact S.inner_self r hr

-- Elementary identities
/-- The endpoint identities of the blueprint (before Definition 2.1): product -2 means opposite
roots. -/
theorem inner_eq_neg_two_iff (S : LineSystem V) {r s : V} (hr : r ∈ S.Φ)
    (hs : s ∈ S.Φ) : ⟪r, s⟫ = -2 ↔ r = -s := by
  rw [← S.inner_eq_two_iff hr (S.neg_mem s hs), inner_neg_right]
  constructor <;> intro h <;> linarith

-- Elementary identities
/-- The endpoint identities of the blueprint (before Definition 2.1) exclude products ±2 for
roots on different lines. -/
theorem inner_eq_neg_one_or_zero_or_one (S : LineSystem V) {r s : V}
    (hr : r ∈ S.Φ) (hs : s ∈ S.Φ) (hne : r ≠ s) (hneg : r ≠ -s) :
    ⟪r, s⟫ = -1 ∨ ⟪r, s⟫ = 0 ∨ ⟪r, s⟫ = 1 := by
  have h := S.inner_mem r hr s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · exact False.elim (hneg ((S.inner_eq_neg_two_iff hr hs).mp h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact False.elim (hne ((S.inner_eq_two_iff hr hs).mp h))

-- Lemma 2.3
/-- Lemma 2.3 of [CGSS]. A maximal line system is star-closed. -/
theorem IsMaximal.isStarClosed {S : LineSystem V} (hS : S.IsMaximal) : S.IsStarClosed := by
  -- ⟨1⟩1
  intro r hr s hs hrs
  -- ⟨2⟩1
  have s2_1 : ⟪r + s, r + s⟫ = 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right, S.inner_self r hr,
      S.inner_self s hs, real_inner_comm r s, hrs]
    norm_num
  -- ⟨2⟩2
  have s2_2 : ∀ t ∈ S.Φ, ⟪r + s, t⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
    intro t ht
    -- ⟨3⟩1
    have s3_1 (h : t = r ∨ t = -r ∨ t = s ∨ t = -s) :
        ⟪r + s, t⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
      rcases h with h | h | h | h <;> rw [h] <;>
        norm_num only [inner_add_left, inner_neg_right, S.inner_self r hr,
          S.inner_self s hs, real_inner_comm r s, hrs,
          Set.mem_insert_iff, Set.mem_singleton_iff, or_true, true_or, false_or, or_false]
    -- ⟨3⟩2
    have s3_2 (h : ¬ (t = r ∨ t = -r ∨ t = s ∨ t = -s)) :
        ⟪r + s, t⟫ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
      -- ⟨4⟩1
      have s4_1 : (⟪r, t⟫ = -1 ∨ ⟪r, t⟫ = 0 ∨ ⟪r, t⟫ = 1) ∧
          (⟪s, t⟫ = -1 ∨ ⟪s, t⟫ = 0 ∨ ⟪s, t⟫ = 1) := by
        constructor
        · apply S.inner_eq_neg_one_or_zero_or_one hr ht
          · exact fun he ↦ h (Or.inl he.symm)
          · exact fun he ↦ h (Or.inr (Or.inl (neg_eq_iff_eq_neg.mpr he).symm))
        · apply S.inner_eq_neg_one_or_zero_or_one hs ht
          · exact fun he ↦ h (Or.inr (Or.inr (Or.inl he.symm)))
          · exact fun he ↦ h (Or.inr (Or.inr (Or.inr
              (neg_eq_iff_eq_neg.mpr he).symm)))
      rcases s4_1 with ⟨hr', hs'⟩
      rcases hr' with hr' | hr' | hr' <;> rcases hs' with hs' | hs' | hs' <;>
        norm_num [inner_add_left, hr', hs']
    by_cases h : t = r ∨ t = -r ∨ t = s ∨ t = -s
    · exact s3_1 h
    · exact s3_2 h
  -- ⟨2⟩3
  have s2_3 : r + s ∈ Submodule.span ℝ S.Φ :=
    Submodule.add_mem _ (Submodule.subset_span hr) (Submodule.subset_span hs)
  exact hS (r + s) s2_3 s2_1 s2_2

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. An indecomposable, star-closed system with an oriented star. -/
structure Hyp24 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- The line system carrying the fixed star. -/
  S : LineSystem V
  /-- The system has no nontrivial orthogonal partition. -/
  isIndecomposable : S.IsIndecomposable
  /-- The system contains the third line of every star on two of its lines. -/
  isStarClosed : S.IsStarClosed
  /-- The first root of the ordered star. -/
  a : V
  /-- The second root of the ordered star. -/
  b : V
  /-- The first root belongs to the system. -/
  a_mem : a ∈ S.Φ
  /-- The second root belongs to the system. -/
  b_mem : b ∈ S.Φ
  /-- The two chosen roots are oriented to have inner product -1. -/
  inner_a_b : ⟪a, b⟫ = -1

namespace Hyp24

variable (H : Hyp24 V)

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The third vector of the fixed star. -/
def c : V := -H.a - H.b

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The roots with products `(0, 1, -1)` against `(a, b, c)`. -/
def Γa : Set V := {x ∈ H.S.Φ | ⟪x, H.a⟫ = 0 ∧ ⟪x, H.b⟫ = 1 ∧ ⟪x, H.c⟫ = -1}

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The roots with products `(0, 1, -1)` against `(b, c, a)`. -/
def Γb : Set V := {x ∈ H.S.Φ | ⟪x, H.b⟫ = 0 ∧ ⟪x, H.c⟫ = 1 ∧ ⟪x, H.a⟫ = -1}

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The roots with products `(0, 1, -1)` against `(c, a, b)`. -/
def Γc : Set V := {x ∈ H.S.Φ | ⟪x, H.c⟫ = 0 ∧ ⟪x, H.a⟫ = 1 ∧ ⟪x, H.b⟫ = -1}

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The roots orthogonal to the fixed star, with both signs. -/
def Δ : Set V := {x ∈ H.S.Φ | ⟪x, H.a⟫ = 0 ∧ ⟪x, H.b⟫ = 0 ∧ ⟪x, H.c⟫ = 0}

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The signed covering set; `Δ` already contains both signs. -/
def sigmaSet : Set V := {H.a, H.b, H.c} ∪ H.Γa ∪ H.Γb ∪ H.Γc ∪ H.Δ

-- Lemma 2.8
/-- Lemma 2.8 of [CGSS]. The third vertex of the triangle on an orthogonal pair. -/
def third (x y : V) : V := H.b - H.c - x - y

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. Every member of `Γa` is a root. -/
theorem Γa_subset_Φ : H.Γa ⊆ H.S.Φ := fun _ hx ↦ hx.1

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The set `Γa` is finite. -/
theorem finite_Γa : H.Γa.Finite := H.S.finite.subset H.Γa_subset_Φ

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The subtype of `Γa` is finite. -/
instance instFiniteΓa : Finite H.Γa := H.finite_Γa.to_subtype

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The fixed finite enumeration of `Γa`. -/
noncomputable instance instFintypeΓa : Fintype H.Γa := Fintype.ofFinite _

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. Every member of `Γb` is a root. -/
theorem Γb_subset_Φ : H.Γb ⊆ H.S.Φ := fun _ hx ↦ hx.1

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The set `Γb` is finite. -/
theorem finite_Γb : H.Γb.Finite := H.S.finite.subset H.Γb_subset_Φ

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The subtype of `Γb` is finite. -/
instance instFiniteΓb : Finite H.Γb := H.finite_Γb.to_subtype

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The fixed finite enumeration of `Γb`. -/
noncomputable instance instFintypeΓb : Fintype H.Γb := Fintype.ofFinite _

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. Every member of `Γc` is a root. -/
theorem Γc_subset_Φ : H.Γc ⊆ H.S.Φ := fun _ hx ↦ hx.1

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The set `Γc` is finite. -/
theorem finite_Γc : H.Γc.Finite := H.S.finite.subset H.Γc_subset_Φ

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The subtype of `Γc` is finite. -/
instance instFiniteΓc : Finite H.Γc := H.finite_Γc.to_subtype

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The fixed finite enumeration of `Γc`. -/
noncomputable instance instFintypeΓc : Fintype H.Γc := Fintype.ofFinite _

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. Every member of `Δ` is a root. -/
theorem Δ_subset_Φ : H.Δ ⊆ H.S.Φ := fun _ hx ↦ hx.1

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The set `Δ` is finite. -/
theorem finite_Δ : H.Δ.Finite := H.S.finite.subset H.Δ_subset_Φ

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The subtype of `Δ` is finite. -/
instance instFiniteΔ : Finite H.Δ := H.finite_Δ.to_subtype

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The fixed finite enumeration of `Δ`. -/
noncomputable instance instFintypeΔ : Fintype H.Δ := Fintype.ofFinite _

-- Hypothesis 2.4
/-- The graph from the opening of Section 2 of [CGSS], restricted to `Γa` as used
in Lemma 2.8. Squared norm two excludes loops. -/
def orthGraph : SimpleGraph H.Γa where
  Adj x y := ⟪(x : V), y⟫ = 0
  symm := ⟨fun x y h ↦ by rwa [real_inner_comm] at h⟩
  loopless := ⟨fun x h ↦ by
    rw [H.S.inner_self x (H.Γa_subset_Φ x.property)] at h
    norm_num at h⟩

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]: orthogonality in `Γa` is decidable by classical choice. -/
noncomputable instance instDecidableRelOrthGraphAdj : DecidableRel H.orthGraph.Adj :=
  Classical.decRel _

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. Adjacency in the orthogonality graph is inner product zero. -/
@[simp] theorem orthGraph_adj (x y : H.Γa) : H.orthGraph.Adj x y ↔ ⟪(x : V), y⟫ = 0 :=
  Iff.rfl

-- Star identities
/-- The star identities of the blueprint: the third root belongs to the system. -/
theorem c_mem : H.c ∈ H.S.Φ := by
  -- ⟨1⟩1, ⟨2⟩1
  have s2_1 : H.a + H.b ∈ H.S.Φ :=
    H.isStarClosed H.a H.a_mem H.b H.b_mem H.inner_a_b
  simpa only [c, neg_add, sub_eq_add_neg] using H.S.neg_mem _ s2_1

-- Star identities
/-- The star identities of the blueprint: the product of `b` and `c`. -/
theorem inner_b_c : ⟪H.b, H.c⟫ = -1 := by
  rw [c, inner_sub_right, inner_neg_right, real_inner_comm H.a H.b,
    H.inner_a_b, H.S.inner_self H.b H.b_mem]
  norm_num

-- Star identities
/-- The star identities of the blueprint: the product of `c` and `a`. -/
theorem inner_c_a : ⟪H.c, H.a⟫ = -1 := by
  rw [c, inner_sub_left, inner_neg_left, real_inner_comm H.a H.b,
    H.inner_a_b, H.S.inner_self H.a H.a_mem]
  norm_num

-- Star identities
/-- The star identities of the blueprint: the product of `c` and `b`. -/
theorem inner_c_b : ⟪H.c, H.b⟫ = -1 := by
  rw [real_inner_comm, H.inner_b_c]

-- Star identities
/-- The star identities of the blueprint: the product of `a` and `c`. -/
theorem inner_a_c : ⟪H.a, H.c⟫ = -1 := (real_inner_comm _ _).trans H.inner_c_a

-- Star identities
/-- The star identities of the blueprint: the product of `b` and `a`. -/
theorem inner_b_a : ⟪H.b, H.a⟫ = -1 := (real_inner_comm _ _).trans H.inner_a_b

-- Star identities
/-- The star identities of the blueprint: the third root and the four displayed products. -/
theorem star : H.c ∈ H.S.Φ ∧ ⟪H.a, H.b⟫ = -1 ∧ ⟪H.b, H.c⟫ = -1 ∧
    ⟪H.c, H.a⟫ = -1 ∧ ⟪H.c, H.b⟫ = -1 :=
  -- ⟨1⟩1
  ⟨H.c_mem, H.inner_a_b, H.inner_b_c, H.inner_c_a, H.inner_c_b⟩

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The defining conditions for membership in `Γa`. -/
theorem mem_Γa_iff {x : V} : x ∈ H.Γa ↔
    x ∈ H.S.Φ ∧ ⟪x, H.a⟫ = 0 ∧ ⟪x, H.b⟫ = 1 ∧ ⟪x, H.c⟫ = -1 := Iff.rfl

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The defining conditions for membership in `Γb`. -/
theorem mem_Γb_iff {x : V} : x ∈ H.Γb ↔
    x ∈ H.S.Φ ∧ ⟪x, H.b⟫ = 0 ∧ ⟪x, H.c⟫ = 1 ∧ ⟪x, H.a⟫ = -1 := Iff.rfl

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The defining conditions for membership in `Γc`. -/
theorem mem_Γc_iff {x : V} : x ∈ H.Γc ↔
    x ∈ H.S.Φ ∧ ⟪x, H.c⟫ = 0 ∧ ⟪x, H.a⟫ = 1 ∧ ⟪x, H.b⟫ = -1 := Iff.rfl

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The defining conditions for membership in `Δ`. -/
theorem mem_Δ_iff {x : V} : x ∈ H.Δ ↔
    x ∈ H.S.Φ ∧ ⟪x, H.a⟫ = 0 ∧ ⟪x, H.b⟫ = 0 ∧ ⟪x, H.c⟫ = 0 := Iff.rfl

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γa` with `a`. -/
theorem inner_a_of_mem_Γa {x : V} (hx : x ∈ H.Γa) : ⟪x, H.a⟫ = 0 := hx.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γa` with `b`. -/
theorem inner_b_of_mem_Γa {x : V} (hx : x ∈ H.Γa) : ⟪x, H.b⟫ = 1 := hx.2.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γa` with `c`. -/
theorem inner_c_of_mem_Γa {x : V} (hx : x ∈ H.Γa) : ⟪x, H.c⟫ = -1 := hx.2.2.2

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product with `c` on the left. -/
theorem inner_c_left_of_mem_Γa {x : V} (hx : x ∈ H.Γa) : ⟪H.c, x⟫ = -1 := by
  rw [real_inner_comm, H.inner_c_of_mem_Γa hx]

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γb` with `b`. -/
theorem inner_b_of_mem_Γb {x : V} (hx : x ∈ H.Γb) : ⟪x, H.b⟫ = 0 := hx.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γb` with `c`. -/
theorem inner_c_of_mem_Γb {x : V} (hx : x ∈ H.Γb) : ⟪x, H.c⟫ = 1 := hx.2.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γb` with `a`. -/
theorem inner_a_of_mem_Γb {x : V} (hx : x ∈ H.Γb) : ⟪x, H.a⟫ = -1 := hx.2.2.2

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γc` with `c`. -/
theorem inner_c_of_mem_Γc {x : V} (hx : x ∈ H.Γc) : ⟪x, H.c⟫ = 0 := hx.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γc` with `a`. -/
theorem inner_a_of_mem_Γc {x : V} (hx : x ∈ H.Γc) : ⟪x, H.a⟫ = 1 := hx.2.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Γc` with `b`. -/
theorem inner_b_of_mem_Γc {x : V} (hx : x ∈ H.Γc) : ⟪x, H.b⟫ = -1 := hx.2.2.2

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Δ` with `a`. -/
theorem inner_a_of_mem_Δ {x : V} (hx : x ∈ H.Δ) : ⟪x, H.a⟫ = 0 := hx.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Δ` with `b`. -/
theorem inner_b_of_mem_Δ {x : V} (hx : x ∈ H.Δ) : ⟪x, H.b⟫ = 0 := hx.2.2.1

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The product of a member of `Δ` with `c`. -/
theorem inner_c_of_mem_Δ {x : V} (hx : x ∈ H.Δ) : ⟪x, H.c⟫ = 0 := hx.2.2.2

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. The first two prescribed products determine membership in `Γa`. -/
theorem mem_Γa_of {x : V} (hx : x ∈ H.S.Φ) (ha : ⟪x, H.a⟫ = 0)
    (hb : ⟪x, H.b⟫ = 1) : x ∈ H.Γa := by
  refine H.mem_Γa_iff.mpr ⟨hx, ha, hb, ?_⟩
  rw [c, inner_sub_right, inner_neg_right, ha, hb]
  norm_num

-- Hypothesis 2.4
/-- Hypothesis 2.4 of [CGSS]. Membership in the signed covering set, by its seven parts. -/
theorem mem_sigmaSet_iff {x : V} : x ∈ H.sigmaSet ↔
    x = H.a ∨ x = H.b ∨ x = H.c ∨ x ∈ H.Γa ∨ x ∈ H.Γb ∨ x ∈ H.Γc ∨ x ∈ H.Δ := by
  simp only [sigmaSet, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

-- Lemma 2.5
/-- Lemma 2.5 of [CGSS]. Every vector of the covering set is a root. -/
theorem sigmaSet_subset_Φ : H.sigmaSet ⊆ H.S.Φ := by
  intro x hx
  rcases H.mem_sigmaSet_iff.mp hx with h | h | h | h | h | h | h
  · exact h ▸ H.a_mem
  · exact h ▸ H.b_mem
  · exact h ▸ H.c_mem
  · exact H.Γa_subset_Φ h
  · exact H.Γb_subset_Φ h
  · exact H.Γc_subset_Φ h
  · exact H.Δ_subset_Φ h

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The signed covering set is finite. -/
theorem finite_sigmaSet : H.sigmaSet.Finite := H.S.finite.subset H.sigmaSet_subset_Φ

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The subtype of the signed covering set is finite. -/
instance instFiniteSigmaSet : Finite H.sigmaSet := H.finite_sigmaSet.to_subtype

-- Hypothesis 2.4
/-- Helper for Hypothesis 2.4 of [CGSS]. The fixed finite enumeration of the signed covering set. -/
noncomputable instance instFintypeSigmaSet : Fintype H.sigmaSet := Fintype.ofFinite _

-- Lemma 2.5
/-- Lemma 2.5 of [CGSS]. The roots are exactly the covering set and its negative. -/
theorem Φ_eq_sigmaSet_union_neg : H.S.Φ = H.sigmaSet ∪ -H.sigmaSet := by
  -- ⟨1⟩1
  have s1_1 : ∀ u ∈ H.S.Φ, ∀ ε : ℝ, ε = -1 ∨ ε = 1 →
      ⟪u, H.a⟫ = ε → ⟪u, H.b⟫ = ε → u = -ε • H.c := by
    intro u hu ε hε hua hub
    have heps : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    -- ⟨2⟩1
    have s2_1 : ⟪H.a + H.b - ε • u, H.a + H.b - ε • u⟫ = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, H.S.inner_self H.a H.a_mem,
        H.S.inner_self H.b H.b_mem, H.S.inner_self u hu, real_inner_comm u H.a,
        real_inner_comm u H.b, real_inner_comm H.a H.b, H.inner_a_b, hua, hub]
      linear_combination (-2 : ℝ) * heps
    have heq : H.a + H.b = ε • u := sub_eq_zero.mp (inner_self_eq_zero.mp s2_1)
    calc
      u = (ε * ε) • u := by rw [heps, one_smul]
      _ = ε • (ε • u) := (smul_smul ε ε u).symm
      _ = ε • (H.a + H.b) := by rw [heq]
      _ = -ε • H.c := by simp [c, smul_sub, smul_add]
  -- ⟨1⟩2
  have s1_2 : ∀ v ∈ H.S.Φ, v ∈ H.sigmaSet ∨ -v ∈ H.sigmaSet := by
    intro v hv
    -- ⟨2⟩1
    have s2_1 (h : v = H.a ∨ v = -H.a ∨ v = H.b ∨ v = -H.b ∨
        v = H.c ∨ v = -H.c) : v ∈ H.sigmaSet ∨ -v ∈ H.sigmaSet := by
      rcases h with h | h | h | h | h | h <;> rw [h] <;>
        simp [H.mem_sigmaSet_iff]
    -- ⟨2⟩2
    have s2_2 (h : ¬ (v = H.a ∨ v = -H.a ∨ v = H.b ∨ v = -H.b ∨
        v = H.c ∨ v = -H.c)) : v ∈ H.sigmaSet ∨ -v ∈ H.sigmaSet := by
      have ha := H.S.inner_eq_neg_one_or_zero_or_one hv H.a_mem
        (fun e ↦ h (Or.inl e)) (fun e ↦ h (Or.inr (Or.inl e)))
      have hb := H.S.inner_eq_neg_one_or_zero_or_one hv H.b_mem
        (fun e ↦ h (Or.inr (Or.inr (Or.inl e))))
        (fun e ↦ h (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      -- ⟨3⟩1
      have s3_1 :
          (⟪v, H.a⟫ = 0 ∧ ⟪v, H.b⟫ = 0) ∨
          (⟪v, H.a⟫ = 0 ∧ ⟪v, H.b⟫ = 1) ∨
          (⟪v, H.a⟫ = 0 ∧ ⟪v, H.b⟫ = -1) ∨
          (⟪v, H.a⟫ = 1 ∧ ⟪v, H.b⟫ = 0) ∨
          (⟪v, H.a⟫ = -1 ∧ ⟪v, H.b⟫ = 0) ∨
          (⟪v, H.a⟫ = 1 ∧ ⟪v, H.b⟫ = -1) ∨
          (⟪v, H.a⟫ = -1 ∧ ⟪v, H.b⟫ = 1) := by
        have hminus : ¬ (⟪v, H.a⟫ = -1 ∧ ⟪v, H.b⟫ = -1) := by
          rintro ⟨ha', hb'⟩
          have he := s1_1 v hv (-1) (Or.inl rfl) ha' hb'
          simp only [neg_neg, one_smul] at he
          exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
        have hplus : ¬ (⟪v, H.a⟫ = 1 ∧ ⟪v, H.b⟫ = 1) := by
          rintro ⟨ha', hb'⟩
          have he := s1_1 v hv 1 (Or.inr rfl) ha' hb'
          simp only [neg_one_smul] at he
          exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
        rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
          first
          | exact False.elim (hminus ⟨ha, hb⟩)
          | exact False.elim (hplus ⟨ha, hb⟩)
          | norm_num [ha, hb]
      -- ⟨3⟩2
      have s3_2 : v ∈ H.sigmaSet ∨ -v ∈ H.sigmaSet := by
        have hc : ⟪v, H.c⟫ = -⟪v, H.a⟫ - ⟪v, H.b⟫ := by
          rw [c, inner_sub_right, inner_neg_right]
        rcases s3_1 with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩ |
          ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩
        · -- `(0, 0)`: choose `v ∈ Δ`.
          apply Or.inl
          apply H.mem_sigmaSet_iff.mpr
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
          exact H.mem_Δ_iff.mpr ⟨hv, ha', hb', by rw [hc, ha', hb']; norm_num⟩
        · -- `(0, 1)`: choose `v ∈ Γa`.
          exact Or.inl (H.mem_sigmaSet_iff.mpr
            (Or.inr (Or.inr (Or.inr (Or.inl (H.mem_Γa_of hv ha' hb'))))))
        · -- `(0, -1)`: choose `-v ∈ Γa`.
          apply Or.inr
          apply H.mem_sigmaSet_iff.mpr
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          apply H.mem_Γa_of (H.S.neg_mem v hv)
          · rw [inner_neg_left, ha', neg_zero]
          · rw [inner_neg_left, hb']; norm_num
        · -- `(1, 0)`: choose `-v ∈ Γb`.
          apply Or.inr
          apply H.mem_sigmaSet_iff.mpr
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          apply H.mem_Γb_iff.mpr
          refine ⟨H.S.neg_mem v hv, ?_, ?_, ?_⟩
          · rw [inner_neg_left, hb', neg_zero]
          · rw [inner_neg_left, hc, ha', hb']; norm_num
          · rw [inner_neg_left, ha']
        · -- `(-1, 0)`: choose `v ∈ Γb`.
          apply Or.inl
          apply H.mem_sigmaSet_iff.mpr
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          exact H.mem_Γb_iff.mpr ⟨hv, hb', by rw [hc, ha', hb']; norm_num, ha'⟩
        · -- `(1, -1)`: choose `v ∈ Γc`.
          apply Or.inl
          apply H.mem_sigmaSet_iff.mpr
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          exact H.mem_Γc_iff.mpr ⟨hv, by rw [hc, ha', hb']; norm_num, ha', hb'⟩
        · -- `(-1, 1)`: choose `-v ∈ Γc`.
          apply Or.inr
          apply H.mem_sigmaSet_iff.mpr
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          apply H.mem_Γc_iff.mpr
          refine ⟨H.S.neg_mem v hv, ?_, ?_, ?_⟩
          · rw [inner_neg_left, hc, ha', hb']; norm_num
          · rw [inner_neg_left, ha']; norm_num
          · rw [inner_neg_left, hb']
      exact s3_2
    by_cases h : v = H.a ∨ v = -H.a ∨ v = H.b ∨ v = -H.b ∨ v = H.c ∨ v = -H.c
    · exact s2_1 h
    · exact s2_2 h
  apply Set.Subset.antisymm
  · intro v hv
    simpa only [Set.mem_union, Set.mem_neg] using s1_2 v hv
  · intro v hv
    rcases hv with hv | hv
    · exact H.sigmaSet_subset_Φ hv
    · simpa only [neg_neg] using H.S.neg_mem (-v) (H.sigmaSet_subset_Φ (Set.mem_neg.mp hv))

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS], the common calculation for the three cyclic translations. -/
private theorem add_mem_cyclic (S : LineSystem V) (hS : S.IsStarClosed) {r s t x : V}
    (ht : t ∈ S.Φ) (htr : ⟪t, r⟫ = -1) (hts : ⟪t, s⟫ = -1)
    (hx : x ∈ S.Φ) (hxr : ⟪x, r⟫ = 0) (hxs : ⟪x, s⟫ = 1) (hxt : ⟪x, t⟫ = -1) :
    x + t ∈ S.Φ ∧ ⟪x + t, s⟫ = 0 ∧ ⟪x + t, t⟫ = 1 ∧ ⟪x + t, r⟫ = -1 := by
  -- ⟨1⟩1, ⟨2⟩1
  have s2_1 : x + t ∈ S.Φ := hS x hx t ht hxt
  -- ⟨2⟩2
  have s2_2 : ⟪x + t, r⟫ = -1 ∧ ⟪x + t, s⟫ = 0 ∧ ⟪x + t, t⟫ = 1 := by
    simp only [inner_add_left, hxr, hxs, hxt, htr, hts, S.inner_self t ht]
    norm_num
  exact ⟨s2_1, s2_2.2.1, s2_2.2.2, s2_2.1⟩

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Translation by `c` takes `Γa` into `Γb`. -/
theorem add_c_mem_Γb {x : V} (hx : x ∈ H.Γa) : x + H.c ∈ H.Γb :=
  -- ⟨1⟩1
  H.mem_Γb_iff.mpr (add_mem_cyclic H.S H.isStarClosed H.c_mem H.inner_c_a H.inner_c_b
    (H.Γa_subset_Φ hx) (H.inner_a_of_mem_Γa hx)
    (H.inner_b_of_mem_Γa hx) (H.inner_c_of_mem_Γa hx))

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Translation by `a` takes `Γb` into `Γc`. -/
theorem add_a_mem_Γc {x : V} (hx : x ∈ H.Γb) : x + H.a ∈ H.Γc :=
  -- ⟨1⟩1
  H.mem_Γc_iff.mpr (add_mem_cyclic H.S H.isStarClosed H.a_mem H.inner_a_b H.inner_a_c
    (H.Γb_subset_Φ hx) (H.inner_b_of_mem_Γb hx)
    (H.inner_c_of_mem_Γb hx) (H.inner_a_of_mem_Γb hx))

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Translation by `b` takes `Γc` into `Γa`. -/
theorem add_b_mem_Γa {x : V} (hx : x ∈ H.Γc) : x + H.b ∈ H.Γa :=
  -- ⟨1⟩1
  H.mem_Γa_iff.mpr (add_mem_cyclic H.S H.isStarClosed H.b_mem H.inner_b_c H.inner_b_a
    (H.Γc_subset_Φ hx) (H.inner_c_of_mem_Γc hx)
    (H.inner_a_of_mem_Γc hx) (H.inner_b_of_mem_Γc hx))

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Subtraction of `b` takes `Γa` into `Γc`. -/
theorem sub_b_mem_Γc {x : V} (hx : x ∈ H.Γa) : x - H.b ∈ H.Γc := by
  have heq : x + H.c + H.a = x - H.b := by rw [c]; abel
  rw [← heq]
  exact H.add_a_mem_Γc (H.add_c_mem_Γb hx)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The first cyclic translation, with the next two as inverse. -/
def ΓaEquivΓb : H.Γa ≃ H.Γb where
  -- ⟨1⟩2
  toFun x := ⟨(x : V) + H.c, H.add_c_mem_Γb x.property⟩
  invFun y := ⟨(y : V) + H.a + H.b, H.add_b_mem_Γa (H.add_a_mem_Γc y.property)⟩
  -- ⟨2⟩1
  left_inv x := Subtype.ext (by simp only [c]; abel)
  right_inv y := Subtype.ext (by simp only [c]; abel)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The underlying vector of the first cyclic equivalence. -/
@[simp] theorem coe_ΓaEquivΓb_apply (x : H.Γa) :
    (H.ΓaEquivΓb x : V) = x + H.c := rfl

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The underlying vector of the inverse first cyclic equivalence. -/
@[simp] theorem coe_ΓaEquivΓb_symm_apply (y : H.Γb) :
    (H.ΓaEquivΓb.symm y : V) = y + H.a + H.b := rfl

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The second cyclic translation, with the next two as inverse. -/
def ΓbEquivΓc : H.Γb ≃ H.Γc where
  -- ⟨1⟩2
  toFun x := ⟨(x : V) + H.a, H.add_a_mem_Γc x.property⟩
  invFun y := ⟨(y : V) + H.b + H.c, H.add_c_mem_Γb (H.add_b_mem_Γa y.property)⟩
  -- ⟨2⟩1
  left_inv x := Subtype.ext (by simp only [c]; abel)
  right_inv y := Subtype.ext (by simp only [c]; abel)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The underlying vector of the second cyclic equivalence. -/
@[simp] theorem coe_ΓbEquivΓc_apply (x : H.Γb) :
    (H.ΓbEquivΓc x : V) = x + H.a := rfl

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The underlying vector of the inverse second cyclic equivalence. -/
@[simp] theorem coe_ΓbEquivΓc_symm_apply (y : H.Γc) :
    (H.ΓbEquivΓc.symm y : V) = y + H.b + H.c := rfl

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The third cyclic translation, with the next two as inverse. -/
def ΓcEquivΓa : H.Γc ≃ H.Γa where
  -- ⟨1⟩2
  toFun x := ⟨(x : V) + H.b, H.add_b_mem_Γa x.property⟩
  invFun y := ⟨(y : V) + H.c + H.a, H.add_a_mem_Γc (H.add_c_mem_Γb y.property)⟩
  -- ⟨2⟩1
  left_inv x := Subtype.ext (by simp only [c]; abel)
  right_inv y := Subtype.ext (by simp only [c]; abel)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The underlying vector of the third cyclic equivalence. -/
@[simp] theorem coe_ΓcEquivΓa_apply (x : H.Γc) :
    (H.ΓcEquivΓa x : V) = x + H.b := rfl

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The underlying vector of the inverse third cyclic equivalence. -/
@[simp] theorem coe_ΓcEquivΓa_symm_apply (y : H.Γa) :
    (H.ΓcEquivΓa.symm y : V) = y + H.c + H.a := rfl

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS], the common inner-product calculation for a translation. -/
private theorem inner_add_translation {x y t : V} (hxt : ⟪x, t⟫ = -1)
    (hyt : ⟪y, t⟫ = -1) (htt : ⟪t, t⟫ = 2) : ⟪x + t, y + t⟫ = ⟪x, y⟫ := by
  -- ⟨1⟩2, ⟨2⟩2
  have s2_2 : ⟪x + t, y + t⟫ = ⟪x, y⟫ - 1 - 1 + 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm y t,
      hxt, hyt, htt]
    ring
  linarith

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The first cyclic equivalence preserves inner products. -/
theorem inner_ΓaEquivΓb (x y : H.Γa) :
    ⟪(H.ΓaEquivΓb x : V), (H.ΓaEquivΓb y : V)⟫ = ⟪(x : V), (y : V)⟫ :=
  inner_add_translation (H.inner_c_of_mem_Γa x.property) (H.inner_c_of_mem_Γa y.property)
    (H.S.inner_self H.c H.c_mem)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The second cyclic equivalence preserves inner products. -/
theorem inner_ΓbEquivΓc (x y : H.Γb) :
    ⟪(H.ΓbEquivΓc x : V), (H.ΓbEquivΓc y : V)⟫ = ⟪(x : V), (y : V)⟫ :=
  inner_add_translation (H.inner_a_of_mem_Γb x.property)
    (H.inner_a_of_mem_Γb y.property) (H.S.inner_self H.a H.a_mem)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The third cyclic equivalence preserves inner products. -/
theorem inner_ΓcEquivΓa (x y : H.Γc) :
    ⟪(H.ΓcEquivΓa x : V), (H.ΓcEquivΓa y : V)⟫ = ⟪(x : V), (y : V)⟫ :=
  inner_add_translation (H.inner_b_of_mem_Γc x.property)
    (H.inner_b_of_mem_Γc y.property) (H.S.inner_self H.b H.b_mem)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS], exclusion of negative products in a cyclic part. -/
private theorem inner_eq_zero_or_one_cyclic (S : LineSystem V) (hS : S.IsStarClosed)
    {r s t x y : V} (ht : t ∈ S.Φ) (htr : ⟪t, r⟫ = -1) (hts : ⟪t, s⟫ = -1)
    (hx : x ∈ S.Φ) (hxr : ⟪x, r⟫ = 0) (hxs : ⟪x, s⟫ = 1) (hxt : ⟪x, t⟫ = -1)
    (hy : y ∈ S.Φ) (hyr : ⟪y, r⟫ = 0) (hys : ⟪y, s⟫ = 1) (hyt : ⟪y, t⟫ = -1)
    (hne : x ≠ y) : ⟪x, y⟫ = 0 ∨ ⟪x, y⟫ = 1 := by
  -- ⟨1⟩3, ⟨2⟩1
  have s2_1 : ⟪x, y⟫ ≠ 2 ∧ ⟪x, y⟫ ≠ -2 := by
    refine ⟨fun he ↦ hne ((S.inner_eq_two_iff hx hy).mp he), ?_⟩
    intro he
    have heq := (S.inner_eq_neg_two_iff hx hy).mp he
    have hip : ⟪x, s⟫ = -⟪y, s⟫ := by rw [heq, inner_neg_left]
    linarith
  -- ⟨2⟩2
  have s2_2 : ⟪x, y⟫ ≠ -1 := by
    intro hxy
    -- ⟨3⟩1
    have s3_1 : x = -(y + t) := by
      apply (S.inner_eq_neg_two_iff hx
        (add_mem_cyclic S hS ht htr hts hy hyr hys hyt).1).mp
      rw [inner_add_right, hxy, hxt]
      norm_num
    have hip : ⟪x, r⟫ = -(⟪y, r⟫ + ⟪t, r⟫) := by
      rw [s3_1, inner_neg_left, inner_add_left]
    linarith
  have h := S.inner_mem x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h
  · exact False.elim (s2_1.2 h)
  · exact False.elim (s2_2 h)
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (s2_1.1 h)

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Distinct members of `Γa` have inner product 0 or 1. -/
theorem inner_eq_zero_or_one {x y : V} (hx : x ∈ H.Γa) (hy : y ∈ H.Γa) (hne : x ≠ y) :
    ⟪x, y⟫ = 0 ∨ ⟪x, y⟫ = 1 :=
  -- ⟨1⟩3
  inner_eq_zero_or_one_cyclic H.S H.isStarClosed H.c_mem H.inner_c_a H.inner_c_b
    (H.Γa_subset_Φ hx) (H.inner_a_of_mem_Γa hx)
    (H.inner_b_of_mem_Γa hx) (H.inner_c_of_mem_Γa hx)
    (H.Γa_subset_Φ hy) (H.inner_a_of_mem_Γa hy)
    (H.inner_b_of_mem_Γa hy) (H.inner_c_of_mem_Γa hy) hne

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Distinct members of `Γb` have inner product 0 or 1. -/
theorem inner_eq_zero_or_one_of_mem_Γb {x y : V} (hx : x ∈ H.Γb) (hy : y ∈ H.Γb)
    (hne : x ≠ y) : ⟪x, y⟫ = 0 ∨ ⟪x, y⟫ = 1 :=
  -- ⟨1⟩3
  inner_eq_zero_or_one_cyclic H.S H.isStarClosed H.a_mem H.inner_a_b H.inner_a_c
    (H.Γb_subset_Φ hx) (H.inner_b_of_mem_Γb hx)
    (H.inner_c_of_mem_Γb hx) (H.inner_a_of_mem_Γb hx)
    (H.Γb_subset_Φ hy) (H.inner_b_of_mem_Γb hy)
    (H.inner_c_of_mem_Γb hy) (H.inner_a_of_mem_Γb hy) hne

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. Distinct members of `Γc` have inner product 0 or 1. -/
theorem inner_eq_zero_or_one_of_mem_Γc {x y : V} (hx : x ∈ H.Γc) (hy : y ∈ H.Γc)
    (hne : x ≠ y) : ⟪x, y⟫ = 0 ∨ ⟪x, y⟫ = 1 :=
  -- ⟨1⟩3
  inner_eq_zero_or_one_cyclic H.S H.isStarClosed H.b_mem H.inner_b_c H.inner_b_a
    (H.Γc_subset_Φ hx) (H.inner_c_of_mem_Γc hx)
    (H.inner_a_of_mem_Γc hx) (H.inner_b_of_mem_Γc hx)
    (H.Γc_subset_Φ hy) (H.inner_c_of_mem_Γc hy)
    (H.inner_a_of_mem_Γc hy) (H.inner_b_of_mem_Γc hy) hne

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The second part is the image of the first under translation by `c`. -/
theorem Γb_eq_image_add_c : H.Γb = (fun x ↦ x + H.c) '' H.Γa := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := H.ΓaEquivΓb.surjective ⟨y, hy⟩
    exact ⟨x, x.property, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact H.add_c_mem_Γb hx

-- Lemma 2.6
/-- Lemma 2.6 of [CGSS]. The third part is the image of the first under subtraction of `b`. -/
theorem Γc_eq_image_sub_b : H.Γc = (fun x ↦ x - H.b) '' H.Γa := by
  ext y
  constructor
  · intro hy
    exact ⟨y + H.b, H.add_b_mem_Γa hy, add_sub_cancel_right y H.b⟩
  · rintro ⟨x, hx, rfl⟩
    exact H.sub_b_mem_Γc hx

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. A difference with inner product 1 belongs to `Δ`. -/
theorem sub_mem_Δ {x y : V} (hx : x ∈ H.Γa) (hy : y ∈ H.Γa) (hxy : ⟪x, y⟫ = 1) :
    x - y ∈ H.Δ := by
  -- ⟨1⟩1, ⟨2⟩1
  have s2_1 : x - y ∈ H.S.Φ := by
    have hip : ⟪x, -y⟫ = -1 := by rw [inner_neg_right, hxy]
    simpa only [sub_eq_add_neg] using
      H.isStarClosed x (H.Γa_subset_Φ hx) (-y) (H.S.neg_mem y (H.Γa_subset_Φ hy)) hip
  refine H.mem_Δ_iff.mpr ⟨s2_1, ?_, ?_, ?_⟩
  · rw [inner_sub_left, H.inner_a_of_mem_Γa hx, H.inner_a_of_mem_Γa hy, sub_self]
  · rw [inner_sub_left, H.inner_b_of_mem_Γa hx, H.inner_b_of_mem_Γa hy, sub_self]
  · rw [inner_sub_left, H.inner_c_of_mem_Γa hx, H.inner_c_of_mem_Γa hy, sub_self]

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. A nonzero product with `Γa` expresses a root of `Δ` as a difference. -/
theorem exists_sub_of_inner_ne_zero {t x : V} (ht : t ∈ H.Δ) (hx : x ∈ H.Γa)
    (htx : ⟪t, x⟫ ≠ 0) : ∃ u ∈ H.Γa, ∃ v ∈ H.Γa, ⟪u, v⟫ = 1 ∧ t = u - v := by
  -- ⟨1⟩2, ⟨2⟩1
  have s2_1 : ⟪t, x⟫ = -1 ∨ ⟪t, x⟫ = 1 := by
    have hne : t ≠ x := by
      intro he
      have hb := H.inner_b_of_mem_Δ ht
      rw [he, H.inner_b_of_mem_Γa hx] at hb
      norm_num at hb
    have hneg : t ≠ -x := by
      intro he
      have hb := H.inner_b_of_mem_Δ ht
      rw [he, inner_neg_left, H.inner_b_of_mem_Γa hx] at hb
      norm_num at hb
    rcases H.S.inner_eq_neg_one_or_zero_or_one (H.Δ_subset_Φ ht) (H.Γa_subset_Φ hx) hne hneg
      with h | h | h
    · exact Or.inl h
    · exact False.elim (htx h)
    · exact Or.inr h
  -- ⟨2⟩2
  have s2_2 (h : ⟪t, x⟫ = -1) :
      ∃ u ∈ H.Γa, ∃ v ∈ H.Γa, ⟪u, v⟫ = 1 ∧ t = u - v := by
    -- ⟨3⟩1
    have s3_1 : x + t ∈ H.Γa := by
      refine H.mem_Γa_iff.mpr ⟨H.isStarClosed x (H.Γa_subset_Φ hx) t (H.Δ_subset_Φ ht)
        ((real_inner_comm t x).trans h), ?_, ?_, ?_⟩
      · rw [inner_add_left, H.inner_a_of_mem_Γa hx, H.inner_a_of_mem_Δ ht, add_zero]
      · rw [inner_add_left, H.inner_b_of_mem_Γa hx, H.inner_b_of_mem_Δ ht, add_zero]
      · rw [inner_add_left, H.inner_c_of_mem_Γa hx, H.inner_c_of_mem_Δ ht, add_zero]
    refine ⟨x + t, s3_1, x, hx, ?_, ?_⟩
    · rw [inner_add_left, H.S.inner_self x (H.Γa_subset_Φ hx), h]
      norm_num
    · abel
  -- ⟨2⟩3
  have s2_3 (h : ⟪t, x⟫ = 1) :
      ∃ u ∈ H.Γa, ∃ v ∈ H.Γa, ⟪u, v⟫ = 1 ∧ t = u - v := by
    -- ⟨3⟩1
    have s3_1 : x - t ∈ H.Γa := by
      have hip : ⟪x, -t⟫ = -1 := by rw [inner_neg_right, real_inner_comm t x, h]
      have hroot : x - t ∈ H.S.Φ := by
        simpa only [sub_eq_add_neg] using
          H.isStarClosed x (H.Γa_subset_Φ hx) (-t) (H.S.neg_mem t (H.Δ_subset_Φ ht)) hip
      refine H.mem_Γa_iff.mpr ⟨hroot, ?_, ?_, ?_⟩
      · rw [inner_sub_left, H.inner_a_of_mem_Γa hx, H.inner_a_of_mem_Δ ht, sub_zero]
      · rw [inner_sub_left, H.inner_b_of_mem_Γa hx, H.inner_b_of_mem_Δ ht, sub_zero]
      · rw [inner_sub_left, H.inner_c_of_mem_Γa hx, H.inner_c_of_mem_Δ ht, sub_zero]
    refine ⟨x, hx, x - t, s3_1, ?_, ?_⟩
    · rw [inner_sub_right, H.S.inner_self x (H.Γa_subset_Φ hx), real_inner_comm t x, h]
      norm_num
    · abel
  rcases s2_1 with h | h
  · exact s2_2 h
  · exact s2_3 h

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The roots orthogonal to the star are exactly these differences. -/
theorem Δ_eq_sub : H.Δ =
    {t | ∃ x ∈ H.Γa, ∃ y ∈ H.Γa, ⟪x, y⟫ = 1 ∧ t = x - y} := by
  -- ⟨1⟩1
  have s1_1 : ∀ x ∈ H.Γa, ∀ y ∈ H.Γa, ⟪x, y⟫ = 1 → x - y ∈ H.Δ :=
    fun _ hx _ hy hxy ↦ H.sub_mem_Δ hx hy hxy
  -- ⟨1⟩2
  have s1_2 : ∀ t ∈ H.Δ, ∀ x ∈ H.Γa, ⟪t, x⟫ ≠ 0 →
      ∃ u ∈ H.Γa, ∃ v ∈ H.Γa, ⟪u, v⟫ = 1 ∧ t = u - v :=
    fun _ ht _ hx htx ↦ H.exists_sub_of_inner_ne_zero ht hx htx
  -- ⟨1⟩3
  have s1_3 : ∀ t ∈ H.Δ, ∃ x ∈ H.Γa, ⟪t, x⟫ ≠ 0 := by
    let P : Set V := {t ∈ H.Δ | ∀ x ∈ H.Γa, ⟪t, x⟫ = 0}
    let Q : Set V := H.S.Φ \ P
    -- ⟨2⟩1
    have s2_1 : P = -P ∧ H.a ∈ Q := by
      have hneg : ∀ t ∈ P, -t ∈ P := by
        intro t ht
        refine ⟨H.mem_Δ_iff.mpr ⟨H.S.neg_mem t (H.Δ_subset_Φ ht.1), ?_, ?_, ?_⟩, ?_⟩
        · rw [inner_neg_left, H.inner_a_of_mem_Δ ht.1, neg_zero]
        · rw [inner_neg_left, H.inner_b_of_mem_Δ ht.1, neg_zero]
        · rw [inner_neg_left, H.inner_c_of_mem_Δ ht.1, neg_zero]
        · intro x hx
          rw [inner_neg_left, ht.2 x hx, neg_zero]
      constructor
      · ext t
        constructor
        · exact fun ht ↦ Set.mem_neg.mpr (hneg t ht)
        · intro ht
          simpa only [neg_neg] using hneg (-t) (Set.mem_neg.mp ht)
      · refine ⟨H.a_mem, ?_⟩
        intro ha
        have hzero := H.inner_a_of_mem_Δ ha.1
        rw [H.S.inner_self H.a H.a_mem] at hzero
        norm_num at hzero
    -- ⟨2⟩2
    have s2_2 : ∀ t ∈ P, ∀ u ∈ H.sigmaSet \ P, ⟪t, u⟫ = 0 := by
      intro t ht u hu
      -- ⟨3⟩1
      have s3_1 (h : u ∈ {H.a, H.b, H.c} ∪ H.Γa ∪ H.Γb ∪ H.Γc) : ⟪t, u⟫ = 0 := by
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] at h
        rcases h with h | h | h | h | h | h
        · rw [h]
          exact H.inner_a_of_mem_Δ ht.1
        · rw [h]
          exact H.inner_b_of_mem_Δ ht.1
        · rw [h]
          exact H.inner_c_of_mem_Δ ht.1
        · exact ht.2 u h
        · rw [H.Γb_eq_image_add_c] at h
          obtain ⟨x, hx, rfl⟩ := h
          rw [inner_add_right, ht.2 x hx, H.inner_c_of_mem_Δ ht.1, add_zero]
        · rw [H.Γc_eq_image_sub_b] at h
          obtain ⟨x, hx, rfl⟩ := h
          rw [inner_sub_right, ht.2 x hx, H.inner_b_of_mem_Δ ht.1, sub_zero]
      -- ⟨3⟩2
      have s3_2 (h : u ∈ H.Δ \ P) : ⟪t, u⟫ = 0 := by
        -- ⟨4⟩1
        have s4_1 : ∃ x ∈ H.Γa, ∃ y ∈ H.Γa, u = x - y := by
          have hex : ∃ x ∈ H.Γa, ⟪u, x⟫ ≠ 0 := by
            by_contra hn
            simp only [not_exists, not_and, not_not] at hn
            exact h.2 ⟨h.1, hn⟩
          obtain ⟨x, hx, hux⟩ := hex
          obtain ⟨v, hv, w, hw, _, heq⟩ := s1_2 u h.1 x hx hux
          exact ⟨v, hv, w, hw, heq⟩
        obtain ⟨x, hx, y, hy, heq⟩ := s4_1
        rw [heq, inner_sub_right, ht.2 x hx, ht.2 y hy, sub_self]
      rcases hu.1 with h | h
      · exact s3_1 h
      · exact s3_2 ⟨h, hu.2⟩
    -- ⟨2⟩3
    have s2_3 : ∀ t ∈ P, ∀ u ∈ Q, ⟪t, u⟫ = 0 := by
      intro t ht u hu
      have hcover := hu.1
      rw [H.Φ_eq_sigmaSet_union_neg] at hcover
      rcases hcover with h | h
      · exact s2_2 t ht u ⟨h, hu.2⟩
      · have hnp : -u ∉ P := by
          intro hnu
          rw [s2_1.1] at hnu
          exact hu.2 (by simpa only [Set.mem_neg, neg_neg] using hnu)
        have hip := s2_2 t ht (-u) ⟨Set.mem_neg.mp h, hnp⟩
        rw [inner_neg_right] at hip
        exact neg_eq_zero.mp hip
    have hcover : P ∪ Q = H.S.Φ := by
      apply Set.Subset.antisymm
      · rintro t (ht | ht)
        · exact (H.Δ_subset_Φ ht.1)
        · exact ht.1
      · intro t ht
        by_cases hp : t ∈ P
        · exact Or.inl hp
        · exact Or.inr ⟨ht, hp⟩
    have hempty : P = ∅ := by
      rcases H.isIndecomposable P Q hcover s2_3 with hp | hq
      · exact hp
      · exact False.elim (Set.notMem_empty H.a (hq ▸ s2_1.2))
    intro t ht
    by_contra hn
    simp only [not_exists, not_and, not_not] at hn
    exact Set.notMem_empty t (hempty ▸ (show t ∈ P from ⟨ht, hn⟩))
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx, htx⟩ := s1_3 t ht
    exact s1_2 t ht x hx htx
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact s1_1 x hx y hy hxy

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The covering set recovered from `a`, `b` and `Γa`. -/
def recoverySet : Set V :=
  {H.a, H.b, H.c} ∪ H.Γa ∪ (fun x ↦ x + H.c) '' H.Γa ∪
    (fun x ↦ x - H.b) '' H.Γa ∪ {t | ∃ x ∈ H.Γa, ∃ y ∈ H.Γa, ⟪x, y⟫ = 1 ∧ t = x - y}

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The covering set equals the explicit recovery set. -/
theorem sigmaSet_eq_recoverySet : H.sigmaSet = H.recoverySet := by
  rw [sigmaSet, recoverySet, H.Γb_eq_image_add_c, H.Γc_eq_image_sub_b, H.Δ_eq_sub]

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The recovery set is finite. -/
theorem finite_recoverySet : H.recoverySet.Finite :=
  H.sigmaSet_eq_recoverySet ▸ H.finite_sigmaSet

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The subtype of the recovery set is finite. -/
instance instFiniteRecoverySet : Finite H.recoverySet := H.finite_recoverySet.to_subtype

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The fixed finite enumeration of the recovery set. -/
noncomputable instance instFintypeRecoverySet : Fintype H.recoverySet := Fintype.ofFinite _

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The roots are the recovered set and its negative. -/
theorem Φ_eq_recovery_union_neg : H.S.Φ = H.recoverySet ∪ -H.recoverySet := by
  rw [H.Φ_eq_sigmaSet_union_neg, H.sigmaSet_eq_recoverySet]

-- Lemma 2.7, used in Lemma 2.12
/-- Lemma 2.7 of [CGSS]. A linear map carrying the ordered star and `Γa` onto their counterparts
and preserving products on `Γa` carries the recovery set onto its counterpart. -/
theorem image_recoverySet (H' : Hyp24 W) (f : V →ₗ[ℝ] W)
    (ha : f H.a = H'.a) (hb : f H.b = H'.b) (hΓ : f '' H.Γa = H'.Γa)
    (hinner : ∀ x ∈ H.Γa, ∀ y ∈ H.Γa, ⟪f x, f y⟫ = ⟪x, y⟫) :
    f '' H.recoverySet = H'.recoverySet := by
  have hc : f H.c = H'.c := by simp only [c, map_sub, map_neg, ha, hb]
  have hdiff :
      f '' {t | ∃ x ∈ H.Γa, ∃ y ∈ H.Γa, ⟪x, y⟫ = 1 ∧ t = x - y} =
      {t | ∃ x ∈ H'.Γa, ∃ y ∈ H'.Γa, ⟪x, y⟫ = 1 ∧ t = x - y} := by
    ext t
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
      refine ⟨f x, ?_, f y, ?_, (hinner x hx y hy).trans hxy, map_sub f x y⟩
      · rw [← hΓ]
        exact Set.mem_image_of_mem f hx
      · rw [← hΓ]
        exact Set.mem_image_of_mem f hy
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      rw [← hΓ] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u - v, ⟨u, hu, v, hv, (hinner u hu v hv).symm.trans hxy, rfl⟩,
        map_sub f u v⟩
  simp only [recoverySet, Set.image_union, Set.image_insert_eq, Set.image_singleton,
    Set.image_image, ha, hb, hc, map_add, map_sub, hdiff, ← hΓ]

-- Lemma 2.7, used in Lemma 2.12
/-- Lemma 2.7 of [CGSS]. The same transport hypotheses carry the full signed root set onto its
counterpart, without requiring injectivity on the ambient space. -/
theorem image_Φ_eq (H' : Hyp24 W) (f : V →ₗ[ℝ] W)
    (ha : f H.a = H'.a) (hb : f H.b = H'.b) (hΓ : f '' H.Γa = H'.Γa)
    (hinner : ∀ x ∈ H.Γa, ∀ y ∈ H.Γa, ⟪f x, f y⟫ = ⟪x, y⟫) :
    f '' H.S.Φ = H'.S.Φ := by
  rw [H.Φ_eq_recovery_union_neg, H'.Φ_eq_recovery_union_neg, Set.image_union,
    Set.image_neg f, H.image_recoverySet H' f ha hb hΓ hinner]

-- Lemma 2.12
/-- Lemma 2.12 of [CGSS], step 212recover: the ordered pair and `Γa` span all roots. -/
theorem span_Φ_eq_span_pair_union_Γa :
    Submodule.span ℝ H.S.Φ = Submodule.span ℝ ({H.a, H.b} ∪ H.Γa) := by
  let U := Submodule.span ℝ ({H.a, H.b} ∪ H.Γa)
  have ha : H.a ∈ U := Submodule.subset_span (Or.inl (Or.inl rfl))
  have hb : H.b ∈ U := Submodule.subset_span (Or.inl (Or.inr rfl))
  have hc : H.c ∈ U := by
    rw [c]
    exact U.sub_mem (U.neg_mem ha) hb
  have hΓ : ∀ x ∈ H.Γa, x ∈ U := fun _ hx ↦ Submodule.subset_span (Or.inr hx)
  -- ⟨1⟩2, ⟨2⟩1 (212formulas)
  have hrec : H.recoverySet ⊆ U := by
    intro t ht
    simp only [recoverySet, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_assoc] at ht
    rcases ht with rfl | rfl | rfl | ht | ht | ht | ht
    · exact ha
    · exact hb
    · exact hc
    · exact hΓ t ht
    · obtain ⟨x, hx, rfl⟩ := ht
      exact U.add_mem (hΓ x hx) hc
    · obtain ⟨x, hx, rfl⟩ := ht
      exact U.sub_mem (hΓ x hx) hb
    · obtain ⟨x, hx, y, hy, _, rfl⟩ := ht
      exact U.sub_mem (hΓ x hx) (hΓ y hy)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro t ht
    rw [H.Φ_eq_recovery_union_neg] at ht
    rcases ht with ht | ht
    · exact hrec ht
    · change t ∈ U
      simpa only [neg_neg] using U.neg_mem (hrec (Set.mem_neg.mp ht))
  · apply Submodule.span_mono
    rintro t (ht | ht)
    · rcases ht with rfl | rfl
      · exact H.a_mem
      · exact H.b_mem
    · exact H.Γa_subset_Φ ht

-- Lemma 2.7
/-- Lemma 2.7 of [CGSS]. The ordered star and `Γa` determine the signed root set. -/
theorem Φ_eq_of_Γa_eq (H' : Hyp24 V) (ha : H.a = H'.a) (hb : H.b = H'.b)
    (hΓa : H.Γa = H'.Γa) : H.S.Φ = H'.S.Φ := by
  have hc : H.c = H'.c := by rw [c, c, ha, hb]
  have hrec : H.recoverySet = H'.recoverySet := by rw [recoverySet, recoverySet, ha, hb, hc, hΓa]
  rw [H.Φ_eq_recovery_union_neg, H'.Φ_eq_recovery_union_neg, hrec]

-- Lemma 2.8
/-- Lemma 2.8 of [CGSS]. An orthogonal pair extends to a triangle, and every other vertex
is orthogonal to exactly one of its three vertices. -/
theorem triangle {x y : V} (hx : x ∈ H.Γa) (hy : y ∈ H.Γa) (hxy : ⟪x, y⟫ = 0) :
    H.third x y ∈ H.Γa ∧ ∀ w ∈ H.Γa, w ≠ x → w ≠ y → w ≠ H.third x y →
      (⟪w, x⟫ = 0 ∧ ⟪w, y⟫ = 1 ∧ ⟪w, H.third x y⟫ = 1) ∨
      (⟪w, x⟫ = 1 ∧ ⟪w, y⟫ = 0 ∧ ⟪w, H.third x y⟫ = 1) ∨
      (⟪w, x⟫ = 1 ∧ ⟪w, y⟫ = 1 ∧ ⟪w, H.third x y⟫ = 0) := by
  -- ⟨1⟩1
  have s1_1 : x + H.c ∈ H.Γb ∧ y - H.b ∈ H.Γc :=
    ⟨H.add_c_mem_Γb hx, H.sub_b_mem_Γc hy⟩
  -- ⟨1⟩2
  have s1_2 : ⟪x + H.c, y - H.b⟫ = -1 := by
    calc
      ⟪x + H.c, y - H.b⟫ = ⟪x, y⟫ - ⟪x, H.b⟫ + ⟪H.c, y⟫ - ⟪H.c, H.b⟫ := by
        simp only [inner_add_left, inner_sub_right]
        ring
      _ = 0 - 1 - 1 + 1 := by
        rw [hxy, H.inner_b_of_mem_Γa hx, H.inner_c_left_of_mem_Γa hy, H.inner_c_b]
        ring
      _ = -1 := by norm_num
  -- ⟨1⟩3
  have s1_3 : H.third x y ∈ H.S.Φ := by
    have hs := H.isStarClosed _ (H.Γb_subset_Φ s1_1.1) _ (H.Γc_subset_Φ s1_1.2) s1_2
    have heq : -((x + H.c) + (y - H.b)) = H.third x y := by rw [third]; abel
    rw [← heq]
    exact H.S.neg_mem _ hs
  -- ⟨1⟩4
  have s1_4 : H.third x y ∈ H.Γa := by
    refine H.mem_Γa_iff.mpr ⟨s1_3, ?_, ?_, ?_⟩
    · rw [third, inner_sub_left, inner_sub_left, inner_sub_left,
        H.inner_b_a, H.inner_c_a, H.inner_a_of_mem_Γa hx, H.inner_a_of_mem_Γa hy]
      norm_num
    · rw [third, inner_sub_left, inner_sub_left, inner_sub_left,
        H.S.inner_self H.b H.b_mem, H.inner_c_b, H.inner_b_of_mem_Γa hx, H.inner_b_of_mem_Γa hy]
      norm_num
    · rw [third, inner_sub_left, inner_sub_left, inner_sub_left,
        H.inner_b_c, H.S.inner_self H.c H.c_mem, H.inner_c_of_mem_Γa hx, H.inner_c_of_mem_Γa hy]
      norm_num
  -- ⟨1⟩5
  have s1_5 : ∀ w ∈ H.Γa, w ≠ x → w ≠ y → w ≠ H.third x y →
      (⟪w, x⟫ = 0 ∧ ⟪w, y⟫ = 1 ∧ ⟪w, H.third x y⟫ = 1) ∨
      (⟪w, x⟫ = 1 ∧ ⟪w, y⟫ = 0 ∧ ⟪w, H.third x y⟫ = 1) ∨
      (⟪w, x⟫ = 1 ∧ ⟪w, y⟫ = 1 ∧ ⟪w, H.third x y⟫ = 0) := by
    intro w hw hwx hwy hwz
    -- ⟨2⟩1
    have s2_1 : ⟪w, x⟫ + ⟪w, y⟫ + ⟪w, H.third x y⟫ = 2 := by
      rw [third, inner_sub_right, inner_sub_right, inner_sub_right,
        H.inner_b_of_mem_Γa hw, H.inner_c_of_mem_Γa hw]
      ring
    -- ⟨2⟩2
    have s2_2 : (⟪w, x⟫ = 0 ∨ ⟪w, x⟫ = 1) ∧ (⟪w, y⟫ = 0 ∨ ⟪w, y⟫ = 1) ∧
        (⟪w, H.third x y⟫ = 0 ∨ ⟪w, H.third x y⟫ = 1) :=
      ⟨H.inner_eq_zero_or_one hw hx hwx, H.inner_eq_zero_or_one hw hy hwy,
        H.inner_eq_zero_or_one hw s1_4 hwz⟩
    rcases s2_2 with ⟨hwx', hwy', hwz'⟩
    rcases hwx' with h | h <;> rcases hwy' with h' | h' <;> rcases hwz' with h'' | h'' <;>
      norm_num only [h, h', h''] at s2_1 <;> norm_num [h, h', h'']
  exact ⟨s1_4, s1_5⟩

-- Lemma 2.8
/-- Lemma 2.8 of [CGSS]. The third vertex on an orthogonal pair belongs to `Γa`. -/
theorem third_mem_Γa {x y : V} (hx : x ∈ H.Γa) (hy : y ∈ H.Γa) (hxy : ⟪x, y⟫ = 0) :
    H.third x y ∈ H.Γa := (H.triangle hx hy hxy).1

-- Corollary of Lemma 2.8
/-- Corollary of Lemma 2.8 of [CGSS]. The first endpoint is orthogonal to the third vertex. -/
theorem inner_third_left {x y : V} (hx : x ∈ H.Γa) (hxy : ⟪x, y⟫ = 0) :
    ⟪x, H.third x y⟫ = 0 := by
  -- ⟨1⟩1, ⟨2⟩1 (28products)
  rw [third, inner_sub_right, inner_sub_right, inner_sub_right,
    H.inner_b_of_mem_Γa hx, H.inner_c_of_mem_Γa hx, H.S.inner_self x (H.Γa_subset_Φ hx), hxy]
  norm_num

-- Corollary of Lemma 2.8
/-- Corollary of Lemma 2.8 of [CGSS]. The second endpoint is orthogonal to the third vertex. -/
theorem inner_third_right {x y : V} (hy : y ∈ H.Γa) (hxy : ⟪x, y⟫ = 0) :
    ⟪y, H.third x y⟫ = 0 := by
  -- ⟨1⟩1, ⟨2⟩1 (28products)
  rw [third, inner_sub_right, inner_sub_right, inner_sub_right,
    H.inner_b_of_mem_Γa hy, H.inner_c_of_mem_Γa hy, real_inner_comm x y, hxy,
    H.S.inner_self y (H.Γa_subset_Φ hy)]
  norm_num

end Hyp24
end LineSystem
