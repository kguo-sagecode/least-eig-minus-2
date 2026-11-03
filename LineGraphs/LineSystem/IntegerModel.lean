/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Integer presentations of line systems

Reusable transfers for counting, sums, Gram isomorphisms and finite certificates.
-/

open scoped RealInnerProductSpace
open Finset

namespace LineSystem

/-- The integer dot product used by the explicit models. -/
abbrev integerInner {n : ℕ} (v w : Fin n → ℤ) : ℤ := dotProduct v w

/-- Transfer integer coordinates to real Euclidean space at scale `c`. -/
noncomputable def integerVector {n : ℕ} (c : ℝ) (v : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ c * (v i : ℝ))

/-- Inner products commute with the integer-coordinate transfer. -/
theorem inner_integerVector {n : ℕ} (c : ℝ) (v w : Fin n → ℤ) :
    ⟪integerVector c v, integerVector c w⟫ = c * c * (integerInner v w : ℝ) := by
  simp only [PiLp.inner_apply, integerVector, RCLike.inner_apply,
    conj_trivial, integerInner, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A nonzero scale preserves distinct integer vectors. -/
theorem integerVector_injective {n : ℕ} {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (integerVector (n := n) c) := by
  intro v w h
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) h
  have : (v i : ℝ) = (w i : ℝ) := mul_left_cancel₀ hc hi
  exact_mod_cast this

/-- Build a line system from integer roots of squared norm `2q`.
The equation on `c` supplies the normalization; all angle checks are over the integers. -/
noncomputable def ofIntegerRoots {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Fin n → ℤ) (q : ℤ) (c : ℝ) (hc : c * c * (q : ℝ) = 1)
    (hnorm : ∀ a, integerInner (v a) (v a) = 2 * q)
    (hneg : ∀ a, ∃ b, v b = -v a)
    (hinner : ∀ a b, integerInner (v a) (v b) ∈ ({-2 * q, -q, 0, q, 2 * q} : Set ℤ)) :
    LineSystem (EuclideanSpace ℝ (Fin n)) where
  Φ := Set.range (fun a ↦ integerVector c (v a))
  finite := Set.finite_range _
  inner_self := by
    rintro _ ⟨a, rfl⟩
    rw [inner_integerVector, hnorm]
    push_cast
    nlinarith [hc]
  neg_mem := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hneg a
    refine ⟨b, ?_⟩
    ext i
    simp [integerVector, hb]
  inner_mem := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [inner_integerVector]
    have h := hinner a b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h | h
    · left
      rw [h]
      push_cast
      nlinarith [hc]
    · right; left
      rw [h]
      push_cast
      nlinarith [hc]
    · right; right; left
      simp [h]
    · right; right; right; left
      rwa [h]
    · right; right; right; right
      rw [h]
      push_cast
      nlinarith [hc]

@[simp] theorem integerVector_apply {n : ℕ} (c : ℝ) (v : Fin n → ℤ) (i : Fin n) :
    integerVector c v i = c * (v i : ℝ) := rfl

@[simp] theorem integerVector_add {n : ℕ} (c : ℝ) (v w : Fin n → ℤ) :
    integerVector c (v + w) = integerVector c v + integerVector c w := by
  ext i
  simp [mul_add]

@[simp] theorem integerVector_neg {n : ℕ} (c : ℝ) (v : Fin n → ℤ) :
    integerVector c (-v) = -integerVector c v := by
  ext i
  simp

/-- An injective finite integer presentation, independently of how `S` was constructed. -/
class IntegerModel {n : ℕ} (S : LineSystem (EuclideanSpace ℝ (Fin n))) where
  ι : Type
  fintype : Fintype ι
  v : ι → Fin n → ℤ
  q : ℤ
  c : ℝ
  hc : c * c * (q : ℝ) = 1
  inj : Function.Injective v
  Φ_eq : S.Φ = Set.range (integerVector c ∘ v)

attribute [instance_reducible, instance] IntegerModel.fintype

namespace IntegerModel

variable {n : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin n))} (M : IntegerModel S)

theorem c_ne_zero : M.c ≠ 0 := by
  intro h
  have := M.hc
  simp [h] at this

theorem q_ne_zero : (M.q : ℝ) ≠ 0 := by
  intro h
  have := M.hc
  simp [h] at this

theorem root_mem (a : M.ι) : integerVector M.c (M.v a) ∈ S.Φ := by
  rw [M.Φ_eq]
  exact Set.mem_range_self a

theorem mem_iff (w : Fin n → ℤ) :
    integerVector M.c w ∈ S.Φ ↔ ∃ a, M.v a = w := by
  rw [M.Φ_eq]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, integerVector_injective M.c_ne_zero ha⟩,
    fun ⟨a, ha⟩ ↦ ⟨a, congrArg (integerVector M.c) ha⟩⟩

/-- The real normalization recovers the integer squared norm `2q` for every presentation. -/
theorem inner_self (a : M.ι) : integerInner (M.v a) (M.v a) = 2 * M.q := by
  have h := S.inner_self _ (M.root_mem a)
  rw [inner_integerVector] at h
  have hc : M.c * M.c ≠ 0 := mul_ne_zero M.c_ne_zero M.c_ne_zero
  have he : (integerInner (M.v a) (M.v a) : ℝ) = 2 * (M.q : ℝ) := by
    apply mul_left_cancel₀ hc
    nlinarith [M.hc]
  exact_mod_cast he

/-- A decoder may be any executable membership test with the given specification. -/
theorem mem_iff_decode (isRoot : (Fin n → ℤ) → Bool)
    (h : ∀ w, isRoot w = true ↔ ∃ a, M.v a = w) (w : Fin n → ℤ) :
    integerVector M.c w ∈ S.Φ ↔ isRoot w = true := (M.mem_iff w).trans (h w).symm

/-- The integer indices are in bijection with the real roots. -/
noncomputable def equiv : M.ι ≃ S.Φ :=
  Equiv.ofBijective (fun a ↦ ⟨integerVector M.c (M.v a), M.root_mem a⟩) ⟨
    fun _ _ h ↦ M.inj (integerVector_injective M.c_ne_zero (congrArg Subtype.val h)), by
      rintro ⟨r, hr⟩
      rw [M.Φ_eq] at hr
      obtain ⟨a, rfl⟩ := hr
      exact ⟨a, rfl⟩⟩

@[simp] theorem equiv_apply (a : M.ι) :
    (M.equiv a : EuclideanSpace ℝ (Fin n)) = integerVector M.c (M.v a) := rfl

/-- All seven model counts use this same transfer. -/
theorem numLines_eq : S.numLines = Fintype.card M.ι / 2 := by
  rw [numLines, M.Φ_eq, Set.ncard_range_of_injective
    ((integerVector_injective M.c_ne_zero).comp M.inj), Nat.card_eq_fintype_card]

/-- Reindex a sum over the actual root set by its integer indices, without multiplicities. -/
theorem sum_Φ {A : Type*} [AddCommMonoid A] (f : EuclideanSpace ℝ (Fin n) → A) :
    ∑ r ∈ S.finite.toFinset, f r = ∑ a : M.ι, f (integerVector M.c (M.v a)) := by
  classical
  symm
  apply Finset.sum_bij (fun a _ ↦ integerVector M.c (M.v a))
  · intro a _
    exact S.finite.mem_toFinset.mpr (M.root_mem a)
  · intro a _ b _ h
    exact M.inj (integerVector_injective M.c_ne_zero h)
  · intro r hr
    have hr' := S.finite.mem_toFinset.mp hr
    rw [M.Φ_eq] at hr'
    obtain ⟨a, rfl⟩ := hr'
    exact ⟨a, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

theorem inner_eq_neg_one_iff (a b : M.ι) :
    ⟪integerVector M.c (M.v a), integerVector M.c (M.v b)⟫ = -1 ↔
      integerInner (M.v a) (M.v b) = -M.q := by
  rw [inner_integerVector]
  constructor
  · intro h
    have hc : M.c * M.c ≠ 0 := mul_ne_zero M.c_ne_zero M.c_ne_zero
    have he : (integerInner (M.v a) (M.v b) : ℝ) = -(M.q : ℝ) := by
      apply mul_left_cancel₀ hc
      nlinarith [M.hc]
    exact_mod_cast he
  · intro h
    rw [h, Int.cast_neg]
    nlinarith [M.hc]

/-- A sum-root certificate suffices for star-closure. -/
theorem isStarClosed_of
    (h : ∀ a b, integerInner (M.v a) (M.v b) = -M.q → ∃ d, M.v d = M.v a + M.v b) :
    S.IsStarClosed := by
  intro r hr s hs hrs
  rw [M.Φ_eq] at hr hs
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := hs
  obtain ⟨d, hd⟩ := h a b ((M.inner_eq_neg_one_iff a b).mp hrs)
  simp only [Function.comp_apply]
  rw [← integerVector_add, ← hd]
  exact M.root_mem d

/-- The certificate may instead use any sound integer decoder. -/
theorem isStarClosed_of_decoder (isRoot : (Fin n → ℤ) → Bool)
    (sound : ∀ w, isRoot w = true → ∃ a, M.v a = w)
    (h : ∀ a b, integerInner (M.v a) (M.v b) = -M.q → isRoot (M.v a + M.v b) = true) :
    S.IsStarClosed := M.isStarClosed_of (fun a b hab ↦ sound _ (h a b hab))

/-- A parent certificate proves connectivity using only one dot product per non-base root. -/
theorem isIndecomposable_of_parent (a₀ : M.ι) (parent : M.ι → M.ι) (depth : M.ι → ℕ)
    (decreases : ∀ a, a ≠ a₀ → depth (parent a) < depth a)
    (edge : ∀ a, a ≠ a₀ → integerInner (M.v a) (M.v (parent a)) ≠ 0) :
    S.IsIndecomposable := by
  intro P Q hPQ horth
  have hmem (a : M.ι) : integerVector M.c (M.v a) ∈ P ∪ Q := hPQ ▸ M.root_mem a
  have hn (a : M.ι) (ha : a ≠ a₀) :
      ⟪integerVector M.c (M.v a), integerVector M.c (M.v (parent a))⟫ ≠ 0 := by
    rw [inner_integerVector]
    exact mul_ne_zero (mul_ne_zero M.c_ne_zero M.c_ne_zero)
      (by exact_mod_cast edge a ha)
  have same (R T : Set (EuclideanSpace ℝ (Fin n)))
      (hm : ∀ a, integerVector M.c (M.v a) ∈ R ∪ T)
      (ho : ∀ r ∈ R, ∀ t ∈ T, ⟪r, t⟫ = 0)
      (hbase : integerVector M.c (M.v a₀) ∈ R) :
      ∀ a, integerVector M.c (M.v a) ∈ R := by
    intro a
    induction ha : depth a using Nat.strong_induction_on generalizing a with
    | h k ih =>
      by_cases he : a = a₀
      · simpa only [he] using hbase
      · have hp := ih (depth (parent a)) (ha ▸ decreases a he) (parent a) rfl
        rcases hm a with hR | hT
        · exact hR
        · exact False.elim (hn a he (by rw [real_inner_comm]; exact ho _ hp _ hT))
  rcases hmem a₀ with hP | hQ
  · right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrS : r ∈ S.Φ := hPQ ▸ Or.inr hr
    rw [M.Φ_eq] at hrS
    obtain ⟨a, rfl⟩ := hrS
    have hp := same P Q hmem horth hP a
    have hzero := horth _ hp _ hr
    have htwo := S.inner_self _ (M.root_mem a)
    dsimp only [Function.comp_apply] at hzero
    linarith
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrS : r ∈ S.Φ := hPQ ▸ Or.inl hr
    rw [M.Φ_eq] at hrS
    obtain ⟨a, rfl⟩ := hrS
    have hq := same Q P (fun a ↦ (hmem a).symm)
      (fun q hq p hp ↦ by rw [real_inner_comm]; exact horth p hp q hq) hQ a
    have hzero := horth _ hr _ hq
    have htwo := S.inner_self _ (M.root_mem a)
    dsimp only [Function.comp_apply] at hzero
    linarith

end IntegerModel

/-- A matching scaled integer Gram matrix defines an isomorphism, with no ambient linear map. -/
noncomputable def Iso.ofIntegerModels {n m : ℕ}
    {S : LineSystem (EuclideanSpace ℝ (Fin n))}
    {T : LineSystem (EuclideanSpace ℝ (Fin m))}
    (M : IntegerModel S) (N : IntegerModel T) (e : M.ι ≃ N.ι)
    (h : ∀ a b, N.q * integerInner (M.v a) (M.v b) =
      M.q * integerInner (N.v (e a)) (N.v (e b))) : S.Iso T where
  toEquiv := M.equiv.symm.trans (e.trans N.equiv)
  inner_map := by
    intro r s
    obtain ⟨a, rfl⟩ := M.equiv.surjective r
    obtain ⟨b, rfl⟩ := M.equiv.surjective s
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, IntegerModel.equiv_apply,
      inner_integerVector]
    have hab : (N.q : ℝ) * (integerInner (M.v a) (M.v b) : ℝ) =
        (M.q : ℝ) * (integerInner (N.v (e a)) (N.v (e b)) : ℝ) := by exact_mod_cast h a b
    apply mul_right_cancel₀ (mul_ne_zero M.q_ne_zero N.q_ne_zero)
    calc
      _ = (N.c * N.c * (N.q : ℝ)) *
          ((M.q : ℝ) * (integerInner (N.v (e a)) (N.v (e b)) : ℝ)) := by ring
      _ = (M.c * M.c * (M.q : ℝ)) *
          ((N.q : ℝ) * (integerInner (M.v a) (M.v b) : ℝ)) := by rw [M.hc, N.hc, hab]
      _ = _ := by ring

/-- The canonical presentation of a line system constructed from integer roots. -/
@[instance_reducible] noncomputable def ofIntegerRootsModel {n : ℕ} {ι : Type} [Fintype ι]
    (v : ι → Fin n → ℤ) (q : ℤ) (c : ℝ) (hc : c * c * (q : ℝ) = 1)
    (hnorm : ∀ a, integerInner (v a) (v a) = 2 * q)
    (hneg : ∀ a, ∃ b, v b = -v a)
    (hinner : ∀ a b, integerInner (v a) (v b) ∈ ({-2 * q, -q, 0, q, 2 * q} : Set ℤ))
    (hinj : Function.Injective v) :
    IntegerModel (ofIntegerRoots v q c hc hnorm hneg hinner) where
  ι := ι
  fintype := inferInstance
  v := v
  q := q
  c := c
  hc := hc
  inj := hinj
  Φ_eq := rfl

/-- Counting specialized to the integer-root constructor. -/
theorem numLines_ofIntegerRoots {n : ℕ} {ι : Type} [Fintype ι]
    (v : ι → Fin n → ℤ) (q : ℤ) (c : ℝ) (hc : c * c * (q : ℝ) = 1)
    (hnorm : ∀ a, integerInner (v a) (v a) = 2 * q)
    (hneg : ∀ a, ∃ b, v b = -v a)
    (hinner : ∀ a b, integerInner (v a) (v b) ∈ ({-2 * q, -q, 0, q, 2 * q} : Set ℤ))
    (hinj : Function.Injective v) :
    (ofIntegerRoots v q c hc hnorm hneg hinner).numLines = Fintype.card ι / 2 :=
  (ofIntegerRootsModel v q c hc hnorm hneg hinner hinj).numLines_eq

end LineSystem
