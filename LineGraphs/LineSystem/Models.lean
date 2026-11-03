/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.IntegerModel
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# The explicit root systems of Section 3 of [CGSS]

Roots are images of structured finite index types in integer coordinates. A single transfer
construction normalizes them to squared norm two in real Euclidean space. Both signs occur.
The paper's coordinate `eᵢ` is coordinate `i - 1` in `Fin n`.

## Main definitions

* `An`, `Dn`, `E₈viaD₈`, `E₈viaA₈`, `E₈viaSteiner`, `E₇`, `E₆`: the seven models.
* Each model has an `IntegerModel` presentation, also for orthogonal restrictions.
* `e₇Normal`, `e₆Normal`: the fixed normals used in Definition 3.3.

## Main statements

* `numLines_An`, `numLines_Dn` and their exceptional analogues: Lemma 3.4.
* The root inclusions and integer descriptions support computations C3, C4 and C6.
* `ModelSpans.lean` computes the span dimensions. The C6 frame identity is for vectors
  in these spans (or, on the ambient space, uses the orthogonal projection onto the span).
-/

open scoped RealInnerProductSpace
open Finset

namespace LineSystem

/-- An integer vector supported on two coordinates. -/
def pairVector {n : ℕ} (i j : Fin n) (a b : ℤ) : Fin n → ℤ :=
  Pi.single i a + Pi.single j b

/-- Dot products against a vector supported on two coordinates. -/
theorem integerInner_pairVector {n : ℕ} (i j : Fin n) (a b : ℤ) (v : Fin n → ℤ) :
    integerInner (pairVector i j a b) v = a * v i + b * v j := by
  exact (add_dotProduct _ _ _).trans (by rw [single_dotProduct, single_dotProduct])

/-- Ordered distinct coordinates index the roots of type A. -/
abbrev AnIndex (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2}

/-- The integer root `eᵢ - eⱼ`. -/
def anRoot {n : ℕ} (p : AnIndex n) : Fin (n + 1) → ℤ :=
  pairVector p.val.1 p.val.2 1 (-1)

/-- Each coordinate of an A root is between minus and plus one. -/
theorem anRoot_bounds {n : ℕ} (p : AnIndex n) (i : Fin (n + 1)) :
    -1 ≤ anRoot p i ∧ anRoot p i ≤ 1 := by
  have := p.property
  simp only [anRoot, pairVector, Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

/-- A roots have squared length two. -/
theorem integerInner_anRoot_self {n : ℕ} (p : AnIndex n) :
    integerInner (anRoot p) (anRoot p) = 2 * 1 := by
  rw [anRoot, integerInner_pairVector]
  simp [pairVector, p.property, Ne.symm p.property]

/-- Reversing the ordered pair negates an A root. -/
theorem anRoot_neg {n : ℕ} (p : AnIndex n) : ∃ q, anRoot q = -anRoot p := by
  refine ⟨⟨(p.val.2, p.val.1), Ne.symm p.property⟩, ?_⟩
  ext i
  simp only [anRoot, pairVector, Pi.add_apply, Pi.neg_apply, Pi.single_apply]
  split_ifs <;> ring

/-- The integer angle condition for A roots. -/
theorem integerInner_anRoot_mem {n : ℕ} (p q : AnIndex n) :
    integerInner (anRoot p) (anRoot q) ∈ ({-2 * 1, -1, 0, 1, 2 * 1} : Set ℤ) := by
  rw [anRoot, integerInner_pairVector]
  have hi := anRoot_bounds q p.val.1
  have hj := anRoot_bounds q p.val.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The positive and negative coordinates recover an A root's index. -/
theorem anRoot_injective {n : ℕ} : Function.Injective (anRoot (n := n)) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [anRoot, pairVector, Pi.add_apply, Pi.single_apply] at hi hj
  have hik : i = k := by split_ifs at hi <;> omega
  have hjl : j = l := by split_ifs at hj <;> omega
  subst k
  subst l
  rfl

-- Definition 3.1
/-- Definition 3.1 of [CGSS]. The A root system in `n + 1` coordinates, with both signs.
The same construction also gives the empty system for `n = 0`. -/
noncomputable def An (n : ℕ) : LineSystem (EuclideanSpace ℝ (Fin (n + 1))) :=
  ofIntegerRoots anRoot 1 1 (by norm_num) integerInner_anRoot_self anRoot_neg
    integerInner_anRoot_mem

/-- Integer presentation of `An`. -/
noncomputable instance An.integerModel (n : ℕ) : IntegerModel (An n) :=
  ofIntegerRootsModel _ _ _ _ _ _ _ anRoot_injective

/-- There are `n(n + 1)` oriented A roots. -/
theorem card_AnIndex (n : ℕ) : Fintype.card (AnIndex n) = n * (n + 1) := by
  rw [Fintype.card_subtype_compl (fun p : Fin (n + 1) × Fin (n + 1) ↦ p.1 = p.2)]
  have hd : Fintype.card {p : Fin (n + 1) × Fin (n + 1) // p.1 = p.2} = n + 1 := by
    let e : {p : Fin (n + 1) × Fin (n + 1) // p.1 = p.2} ≃ Fin (n + 1) :=
      { toFun := fun p ↦ p.val.1
        invFun := fun i ↦ ⟨(i, i), rfl⟩
        left_inv := fun ⟨⟨i, j⟩, h⟩ ↦ by dsimp at h; subst j; rfl
        right_inv := fun _ ↦ rfl }
    simpa using Fintype.card_congr e
  rw [hd]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Nat.add_mul]
  simp

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. The A root system has `n(n + 1)/2` lines. -/
theorem numLines_An (n : ℕ) : (An n).numLines = n * (n + 1) / 2 := by
  rw [(An.integerModel n).numLines_eq]
  change Fintype.card (AnIndex n) / 2 = _
  rw [card_AnIndex]

/-- A Boolean sign, with `false` positive. -/
def rootSign (b : Bool) : ℤ := if b then -1 else 1

/-- Boolean signs are nonzero. -/
theorem rootSign_ne_zero (b : Bool) : rootSign b ≠ 0 := by cases b <;> decide

/-- The integer sign remembers its Boolean index. -/
theorem rootSign_injective : Function.Injective rootSign := by decide

/-- Increasing pairs and two independent signs index the D roots. -/
abbrev DnIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2} × (Bool × Bool)

/-- The integer D root with its two independently signed coordinates. -/
def dnRoot {n : ℕ} (p : DnIndex n) : Fin n → ℤ :=
  pairVector p.1.val.1 p.1.val.2 (rootSign p.2.1) (rootSign p.2.2)

/-- The two coordinates supporting a D root. -/
theorem dnRoot_ne_zero_iff {n : ℕ} (p : DnIndex n) (i : Fin n) :
    dnRoot p i ≠ 0 ↔ i = p.1.val.1 ∨ i = p.1.val.2 := by
  have h := ne_of_lt p.1.property
  have ha := rootSign_ne_zero p.2.1
  have hb := rootSign_ne_zero p.2.2
  simp only [dnRoot, pairVector, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- Every D coordinate lies between minus and plus one. -/
theorem dnRoot_bounds {n : ℕ} (p : DnIndex n) (i : Fin n) :
    -1 ≤ dnRoot p i ∧ dnRoot p i ≤ 1 := by
  have h := ne_of_lt p.1.property
  simp only [dnRoot, pairVector, Pi.add_apply, Pi.single_apply, rootSign]
  split_ifs <;> omega

/-- D roots have squared length two. -/
theorem integerInner_dnRoot_self {n : ℕ} (p : DnIndex n) :
    integerInner (dnRoot p) (dnRoot p) = 2 * 1 := by
  rw [dnRoot, integerInner_pairVector]
  simp only [pairVector, Pi.add_apply, Pi.single_apply, rootSign]
  have := ne_of_lt p.1.property
  split_ifs <;> omega

/-- Complementing both signs negates a D root. -/
theorem dnRoot_neg {n : ℕ} (p : DnIndex n) : ∃ q, dnRoot q = -dnRoot p := by
  refine ⟨(p.1, (!p.2.1, !p.2.2)), ?_⟩
  ext i
  simp only [dnRoot, pairVector, Pi.add_apply, Pi.neg_apply, Pi.single_apply, rootSign]
  cases p.2.1 <;> cases p.2.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    Bool.not_false, Bool.not_true] <;> split_ifs <;> ring

/-- The integer angle condition for D roots. -/
theorem integerInner_dnRoot_mem {n : ℕ} (p q : DnIndex n) :
    integerInner (dnRoot p) (dnRoot q) ∈ ({-2 * 1, -1, 0, 1, 2 * 1} : Set ℤ) := by
  rw [dnRoot, integerInner_pairVector]
  have hi := dnRoot_bounds q p.1.val.1
  have hj := dnRoot_bounds q p.1.val.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, rootSign]
  split_ifs <;> omega

/-- Supports and signs recover a D root's index. -/
theorem dnRoot_injective {n : ℕ} : Function.Injective (dnRoot (n := n)) := by
  rintro ⟨⟨⟨i, j⟩, hij⟩, a, b⟩ ⟨⟨⟨k, l⟩, hkl⟩, c, d⟩ h
  dsimp at hij hkl
  have hi : i = k ∨ i = l := by
    apply (dnRoot_ne_zero_iff (⟨(k, l), hkl⟩, c, d) i).mp
    rw [← h]
    exact (dnRoot_ne_zero_iff _ i).mpr (Or.inl rfl)
  have hj : j = k ∨ j = l := by
    apply (dnRoot_ne_zero_iff (⟨(k, l), hkl⟩, c, d) j).mp
    rw [← h]
    exact (dnRoot_ne_zero_iff _ j).mpr (Or.inr rfl)
  have hik : i = k := by rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
  have hjl : j = l := by rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
  subst k
  subst l
  have ha : a = c := rootSign_injective (by
    have := congrFun h i
    simpa [dnRoot, pairVector, ne_of_lt hij, ne_of_gt hij] using this)
  have hb : b = d := rootSign_injective (by
    have := congrFun h j
    simpa [dnRoot, pairVector, ne_of_lt hij, ne_of_gt hij] using this)
  subst c
  subst d
  rfl

-- Definition 3.1
/-- Definition 3.1 of [CGSS]. The D root system in `n` coordinates, with both signs.
The paper uses `n ≥ 4`; the coordinate construction is defined in every dimension.
`Dn 0` and `Dn 1` are empty; `Dn 2` consists of two orthogonal lines and is decomposable;
The classification uses this family for `n ≥ 4`. -/
noncomputable def Dn (n : ℕ) : LineSystem (EuclideanSpace ℝ (Fin n)) :=
  ofIntegerRoots dnRoot 1 1 (by norm_num) integerInner_dnRoot_self dnRoot_neg
    integerInner_dnRoot_mem

/-- Integer presentation of `Dn`. -/
noncomputable instance Dn.integerModel (n : ℕ) : IntegerModel (Dn n) :=
  ofIntegerRootsModel _ _ _ _ _ _ _ dnRoot_injective

/-- The D roots have four sign choices per increasing pair. -/
theorem card_DnIndex (n : ℕ) : Fintype.card (DnIndex n) = n.choose 2 * 4 := by
  simp [DnIndex, Fintype.card_subtype, Fintype.card_product_filter_lt]

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. The D root system has `n(n - 1)` lines. -/
theorem numLines_Dn (n : ℕ) : (Dn n).numLines = n * (n - 1) := by
  rw [(Dn.integerModel n).numLines_eq]
  change Fintype.card (DnIndex n) / 2 = _
  rw [card_DnIndex]
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.sub_zero, Nat.mul_one] at h
  rw [Nat.mul_comm (n - 1) n] at h
  omega

/-- Multiplication of signs is Boolean exclusive-or. -/
theorem rootSign_xor (a b : Bool) : rootSign (a ^^ b) = rootSign a * rootSign b := by
  cases a <;> cases b <;> decide

/-- Model (ii). Seven signs determine the eighth by even parity. -/
def halfRoot (s : Fin 7 → Bool) : Fin 8 → ℤ :=
  Fin.lastCases (rootSign ((List.ofFn s).foldl Bool.xor false)) (fun i ↦ rootSign (s i))

/-- The inexpensive Boolean fold agrees with the mathematical parity product. -/
theorem rootSign_foldl_xor : ∀ s : Fin 7 → Bool,
    rootSign ((List.ofFn s).foldl Bool.xor false) = ∏ i, rootSign (s i) := by
  decide +kernel

/-- Model (ii). Every half-root coordinate is a sign. -/
theorem halfRoot_mem : ∀ s i, halfRoot s i = 1 ∨ halfRoot s i = -1 := by
  decide +kernel

/-- Model (ii). The sign product is positive. -/
theorem prod_halfRoot : ∀ s, ∏ i, halfRoot s i = 1 := by
  decide +kernel

/-- Model (ii). Doubled half-roots have squared norm eight. -/
theorem integerInner_halfRoot_self : ∀ s, integerInner (halfRoot s) (halfRoot s) = 8 := by
  decide +kernel

/-- Model (ii). Complementing seven signs negates all eight. -/
theorem halfRoot_neg : ∀ s, halfRoot (fun i ↦ !(s i)) = -halfRoot s := by
  decide +kernel

/-- Model (ii). Multiplying coordinates preserves even parity. -/
theorem halfRoot_mul (s t : Fin 7 → Bool) (i : Fin 8) :
    halfRoot (fun j ↦ s j ^^ t j) i = halfRoot s i * halfRoot t i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [halfRoot, Fin.lastCases_last, rootSign_foldl_xor,
      rootSign_xor, Finset.prod_mul_distrib]
  · simp only [halfRoot, Fin.lastCases_castSucc, rootSign_xor]

/-- Model (ii). A parity sign vector has sum divisible by four. -/
theorem sum_halfRoot_mem : ∀ s, (∑ i, halfRoot s i) ∈ ({-8, -4, 0, 4, 8} : Set ℤ) := by
  decide +kernel

/-- Model (ii). The integer angle condition between half-roots.
Only 128 sums are checked: coordinatewise multiplication reduces a pair to one sign vector. -/
theorem integerInner_halfRoot_mem (s t : Fin 7 → Bool) :
    integerInner (halfRoot s) (halfRoot t) ∈ ({-8, -4, 0, 4, 8} : Set ℤ) := by
  simpa only [integerInner, dotProduct, halfRoot_mul] using sum_halfRoot_mem (fun i ↦ s i ^^ t i)

/-- Model (ii). The first seven coordinates recover the sign index. -/
theorem halfRoot_injective : Function.Injective halfRoot := by
  intro s t h
  funext i
  apply rootSign_injective
  simpa [halfRoot] using congrFun h i.castSucc

/-- Model (ii). The 112 D roots and 128 even sign vectors. -/
abbrev E₈Index := DnIndex 8 ⊕ (Fin 7 → Bool)

/-- Model (ii). The E₈ roots in doubled integer coordinates. -/
def e₈Root : E₈Index → Fin 8 → ℤ
  | .inl p => fun i ↦ 2 * dnRoot p i
  | .inr s => halfRoot s

/-- Model (ii). Doubled E₈ roots have squared norm eight. -/
theorem integerInner_e₈Root_self (a : E₈Index) :
    integerInner (e₈Root a) (e₈Root a) = 2 * 4 := by
  cases a with
  | inl p =>
    have h := integerInner_dnRoot_self p
    change (∑ i, (2 * dnRoot p i) * (2 * dnRoot p i)) = 2 * 4
    simp_rw [show ∀ x : ℤ, (2 * x) * (2 * x) = 4 * (x * x) by intro x; ring]
    rw [← Finset.mul_sum]
    change 4 * integerInner (dnRoot p) (dnRoot p) = 2 * 4
    rw [h]
    norm_num
  | inr s => exact integerInner_halfRoot_self s

/-- Model (ii). The E₈ root list contains both signs. -/
theorem e₈Root_neg (a : E₈Index) : ∃ b, e₈Root b = -e₈Root a := by
  cases a with
  | inl p =>
    obtain ⟨q, hq⟩ := dnRoot_neg p
    refine ⟨.inl q, ?_⟩
    ext i
    simp [e₈Root, hq]
  | inr s => exact ⟨.inr (fun i ↦ !(s i)), halfRoot_neg s⟩

/-- Model (ii). Inner products between D roots and half-roots. -/
theorem integerInner_dnRoot_halfRoot_mem (p : DnIndex 8) (s : Fin 7 → Bool) :
    integerInner (e₈Root (.inl p)) (halfRoot s) ∈ ({-8, -4, 0, 4, 8} : Set ℤ) := by
  change (∑ i, (2 * dnRoot p i) * halfRoot s i) ∈ _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change 2 * integerInner (dnRoot p) (halfRoot s) ∈ _
  rw [dnRoot, integerInner_pairVector]
  have hi := halfRoot_mem s p.1.val.1
  have hj := halfRoot_mem s p.1.val.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, rootSign]
  split_ifs <;> rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega

/-- Model (ii). The integer angle condition for doubled E₈ roots. -/
theorem integerInner_e₈Root_mem (a b : E₈Index) :
    integerInner (e₈Root a) (e₈Root b) ∈ ({-2 * 4, -4, 0, 4, 2 * 4} : Set ℤ) := by
  rcases a with p | s <;> rcases b with q | t
  · have h := integerInner_dnRoot_mem p q
    change (∑ i, (2 * dnRoot p i) * (2 * dnRoot q i)) ∈ _
    simp_rw [show ∀ x y : ℤ, (2 * x) * (2 * y) = 4 * (x * y) by intros; ring]
    rw [← Finset.mul_sum]
    change 4 * integerInner (dnRoot p) (dnRoot q) ∈ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    omega
  · exact integerInner_dnRoot_halfRoot_mem p t
  · have h := integerInner_dnRoot_halfRoot_mem q s
    have he : integerInner (e₈Root (.inr s)) (e₈Root (.inl q)) =
        integerInner (e₈Root (.inl q)) (halfRoot s) := dotProduct_comm _ _
    rw [he]
    exact h
  · exact integerInner_halfRoot_mem s t

/-- Model (ii). Doubled D roots and even sign vectors are distinct. -/
theorem e₈Root_injective : Function.Injective e₈Root := by
  intro a b h
  rcases a with p | s <;> rcases b with q | t
  · congr 1
    apply dnRoot_injective
    funext i
    have hi := congrFun h i
    change 2 * dnRoot p i = 2 * dnRoot q i at hi
    omega
  · have hi := congrFun h p.1.val.1
    have hs := halfRoot_mem t p.1.val.1
    simp only [e₈Root, dnRoot, pairVector, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (ne_of_lt p.1.property), add_zero] at hi
    cases p.2.1 <;> simp only [rootSign] at hi <;> omega
  · have hi := congrFun h q.1.val.1
    have hs := halfRoot_mem s q.1.val.1
    simp only [e₈Root, dnRoot, pairVector, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (ne_of_lt q.1.property), add_zero] at hi
    cases q.2.1 <;> simp only [rootSign] at hi <;> omega
  · exact congrArg Sum.inr (halfRoot_injective h)

-- Definition 3.2
/-- Definition 3.2 of [CGSS]. Model (ii). D₈ together with all even-parity half-roots. -/
noncomputable def E₈viaD₈ : LineSystem (EuclideanSpace ℝ (Fin 8)) :=
  ofIntegerRoots e₈Root 4 (1 / 2) (by norm_num) integerInner_e₈Root_self e₈Root_neg
    integerInner_e₈Root_mem

-- Definition 3.2
/-- Definition 3.2 of [CGSS]. The default E₈ is model (ii), as used in Section 4. -/
noncomputable abbrev E₈ := E₈viaD₈

/-- Integer presentation of `E₈viaD₈`. -/
noncomputable instance E₈viaD₈.integerModel : IntegerModel E₈viaD₈ :=
  ofIntegerRootsModel _ _ _ _ _ _ _ e₈Root_injective

/-- The default E₈ has 240 oriented roots. -/
theorem card_E₈Index : Fintype.card E₈Index = 240 := by
  rw [Fintype.card_sum, card_DnIndex]
  norm_num [Nat.choose]

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. The E₈ root system has 120 lines. -/
theorem numLines_E₈ : E₈.numLines = 120 := by
  rw [E₈viaD₈.integerModel.numLines_eq,
    Fintype.card_congr (show E₈viaD₈.integerModel.ι ≃ E₈Index from Equiv.refl _),
    card_E₈Index]

/-- The fixed root `e₇ - e₈`, using indices 6 and 7 in `Fin 8`. -/
noncomputable def e₇Normal : EuclideanSpace ℝ (Fin 8) :=
  EuclideanSpace.single 6 1 - EuclideanSpace.single 7 1

/-- The second star root `e₆ - e₇`, using indices 5 and 6 in `Fin 8`. -/
noncomputable def e₆Normal : EuclideanSpace ℝ (Fin 8) :=
  EuclideanSpace.single 5 1 - EuclideanSpace.single 6 1

-- Definition 3.3
/-- Definition 3.3 of [CGSS]. The subsystem perpendicular to the fixed root `e₇ - e₈`. -/
noncomputable def E₇ : LineSystem (EuclideanSpace ℝ (Fin 8)) := E₈.orthogonalTo e₇Normal

-- Definition 3.3
/-- Definition 3.3 of [CGSS]. The subsystem perpendicular to the star generated by
`e₇ - e₈` and `e₆ - e₇`. These are coordinates `(6,7)` and `(5,6)` in `Fin 8`. -/
noncomputable def E₆ : LineSystem (EuclideanSpace ℝ (Fin 8)) := E₇.orthogonalTo e₆Normal

/-- Orthogonality to a coordinate difference is coordinate equality. -/
theorem integerVector_inner_sub_single_eq_zero {n : ℕ} (v : Fin n → ℤ)
    {c : ℝ} (hc : c ≠ 0) (i j : Fin n) :
    ⟪integerVector c v, EuclideanSpace.single i 1 - EuclideanSpace.single j 1⟫ = 0 ↔
      v i = v j := by
  rw [inner_sub_right, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right]
  simp only [integerVector, PiLp.toLp_apply, conj_trivial, one_mul, sub_eq_zero,
    mul_right_inj' hc, Int.cast_inj]

/-- Integer indices of the E₇ roots. -/
abbrev E₇Index := {a : E₈Index // e₈Root a 6 = e₈Root a 7}

/-- Integer indices of the E₆ roots. -/
abbrev E₆Index := {a : E₈Index // e₈Root a 6 = e₈Root a 7 ∧ e₈Root a 5 = e₈Root a 6}

/-- The filtered integer indices give precisely the E₇ subsystem. -/
theorem E₇_roots_eq_range :
    E₇.Φ = Set.range (fun a : E₇Index ↦ integerVector (1 / 2) (e₈Root a.val)) := by
  ext v
  constructor
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨⟨a, (integerVector_inner_sub_single_eq_zero _ (by norm_num) 6 7).mp ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.val, rfl⟩,
      (integerVector_inner_sub_single_eq_zero _ (by norm_num) 6 7).mpr a.property⟩

/-- The filtered integer indices give precisely the E₆ subsystem. -/
theorem E₆_roots_eq_range :
    E₆.Φ = Set.range (fun a : E₆Index ↦ integerVector (1 / 2) (e₈Root a.val)) := by
  ext v
  constructor
  · rintro ⟨⟨⟨a, rfl⟩, ha⟩, hb⟩
    refine ⟨⟨a, ?_, ?_⟩, rfl⟩
    · exact (integerVector_inner_sub_single_eq_zero _ (by norm_num) 6 7).mp ha
    · exact (integerVector_inner_sub_single_eq_zero _ (by norm_num) 5 6).mp hb
  · rintro ⟨a, rfl⟩
    exact ⟨⟨⟨a.val, rfl⟩,
      (integerVector_inner_sub_single_eq_zero _ (by norm_num) 6 7).mpr a.property.1⟩,
      (integerVector_inner_sub_single_eq_zero _ (by norm_num) 5 6).mpr a.property.2⟩

/-- Integer presentation of the orthogonal E₇ subsystem. -/
noncomputable instance E₇.integerModel : IntegerModel E₇ where
  ι := E₇Index
  fintype := inferInstance
  v := fun a ↦ e₈Root a.val
  q := 4
  c := 1 / 2
  hc := by norm_num
  inj := e₈Root_injective.comp Subtype.val_injective
  Φ_eq := E₇_roots_eq_range

/-- Integer presentation of the orthogonal E₆ subsystem. -/
noncomputable instance E₆.integerModel : IntegerModel E₆ where
  ι := E₆Index
  fintype := inferInstance
  v := fun a ↦ e₈Root a.val
  q := 4
  c := 1 / 2
  hc := by norm_num
  inj := e₈Root_injective.comp Subtype.val_injective
  Φ_eq := E₆_roots_eq_range

/-- There are 126 oriented roots perpendicular to the fixed root. -/
theorem card_E₇Index : Fintype.card E₇Index = 126 := by decide +kernel

/-- There are 72 oriented roots perpendicular to the fixed star. -/
theorem card_E₆Index : Fintype.card E₆Index = 72 := by decide +kernel

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. The E₇ root system has 63 lines. -/
theorem numLines_E₇ : E₇.numLines = 63 := by
  rw [E₇.integerModel.numLines_eq,
    Fintype.card_congr (show E₇.integerModel.ι ≃ E₇Index from Equiv.refl _),
    card_E₇Index]

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. The E₆ root system has 36 lines. -/
theorem numLines_E₆ : E₆.numLines = 36 := by
  rw [E₆.integerModel.numLines_eq,
    Fintype.card_congr (show E₆.integerModel.ι ≃ E₆Index from Equiv.refl _),
    card_E₆Index]

/-- Every coordinate difference is a root of the default E₈. -/
theorem sub_single_mem_E₈ (i j : Fin 8) (hij : i < j) :
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈ E₈.Φ := by
  refine ⟨Sum.inl (⟨(i, j), hij⟩, false, true), ?_⟩
  ext k
  simp [integerVector, e₈Root, dnRoot, pairVector, rootSign, Pi.single_apply,
    PiLp.single_apply]
  split_ifs <;> norm_num

/-- The fixed normal for E₇ is an E₈ root. -/
theorem e₇Normal_mem_E₈ : e₇Normal ∈ E₈.Φ := sub_single_mem_E₈ 6 7 (by decide)

/-- The second fixed normal for E₆ is an E₈ root. -/
theorem e₆Normal_mem_E₈ : e₆Normal ∈ E₈.Φ := sub_single_mem_E₈ 5 6 (by decide)

/-- The fixed normals generate a star. -/
theorem inner_e₇Normal_e₆Normal : ⟪e₇Normal, e₆Normal⟫ = -1 := by
  simp [e₇Normal, e₆Normal, inner_sub_left, inner_sub_right,
    EuclideanSpace.inner_single_left]

/-- The third line of the fixed star is also in E₈. -/
theorem e₇Normal_add_e₆Normal_mem_E₈ : e₇Normal + e₆Normal ∈ E₈.Φ := by
  have he : e₇Normal + e₆Normal =
      EuclideanSpace.single 5 (1 : ℝ) - EuclideanSpace.single 7 1 := by
    unfold e₇Normal e₆Normal
    abel
  rw [he]
  exact sub_single_mem_E₈ 5 7 (by decide)

/-- Scaling both integer vectors scales their dot product. -/
theorem integerInner_mul {n : ℕ} (a b : ℤ) (v w : Fin n → ℤ) :
    integerInner (fun i ↦ a * v i) (fun i ↦ b * w i) = a * b * integerInner v w := by
  change (a • v) ⬝ᵥ (b • w) = _
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, mul_assoc]

/-- Model (i). Three-subsets of the nine coordinates. -/
abbrev TripleIndex := {t : Finset (Fin 9) // t.card = 3}

/-- Model (i). Tripled extra roots: minus two on a triple, one off it. -/
def tripleRoot (t : TripleIndex) (i : Fin 9) : ℤ := if i ∈ t.val then -2 else 1

/-- Model (i). Intersections determine dot products of extra roots. -/
theorem integerInner_tripleRoot (s t : TripleIndex) :
    integerInner (tripleRoot s) (tripleRoot t) = 9 * ((s.val ∩ t.val).card : ℤ) - 9 := by
  have he (i : Fin 9) : tripleRoot s i * tripleRoot t i =
      1 - 3 * (if i ∈ s.val then 1 else 0) - 3 * (if i ∈ t.val then 1 else 0) +
        9 * (if i ∈ s.val ∩ t.val then 1 else 0) := by
    simp only [tripleRoot, Finset.mem_inter]
    split_ifs <;> norm_num <;> tauto
  simp only [integerInner, dotProduct, he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have hinter : Finset.univ.filter (fun i : Fin 9 ↦ i ∈ s.val ∧ i ∈ t.val) =
      s.val ∩ t.val := by ext; simp
  simp [s.property, t.property, hinter]
  ring

/-- Model (i). Tripled extra roots have squared norm eighteen. -/
theorem integerInner_tripleRoot_self (t : TripleIndex) :
    integerInner (tripleRoot t) (tripleRoot t) = 18 := by
  rw [integerInner_tripleRoot]
  simp [t.property]

/-- Model (i). The triple is recoverable from its coordinates. -/
theorem tripleRoot_injective : Function.Injective tripleRoot := by
  intro s t h
  apply Subtype.ext
  ext i
  have hi := congrFun h i
  simp only [tripleRoot] at hi
  split_ifs at hi <;> simp_all

/-- Model (i). The A₈ roots and signed three-subsets. -/
abbrev E₈AIndex := AnIndex 8 ⊕ (TripleIndex × Bool)

/-- Model (i). The nine-coordinate realization, tripled over ℤ. -/
def e₈ARoot : E₈AIndex → Fin 9 → ℤ
  | .inl p => fun i ↦ 3 * anRoot p i
  | .inr (t, b) => fun i ↦ rootSign b * tripleRoot t i

/-- Model (i). All tripled roots have squared norm eighteen. -/
theorem integerInner_e₈ARoot_self (a : E₈AIndex) :
    integerInner (e₈ARoot a) (e₈ARoot a) = 2 * 9 := by
  rcases a with p | ⟨t, b⟩
  · rw [e₈ARoot, integerInner_mul, integerInner_anRoot_self]
    norm_num
  · rw [e₈ARoot, integerInner_mul, integerInner_tripleRoot_self]
    cases b <;> rfl

/-- Model (i). Both signs occur. -/
theorem e₈ARoot_neg (a : E₈AIndex) : ∃ b, e₈ARoot b = -e₈ARoot a := by
  rcases a with p | ⟨t, b⟩
  · obtain ⟨q, hq⟩ := anRoot_neg p
    refine ⟨.inl q, ?_⟩
    ext i
    simp [e₈ARoot, hq]
  · refine ⟨.inr (t, !b), ?_⟩
    ext i
    cases b <;> simp [e₈ARoot, rootSign]

/-- Model (i). Inner products between an A root and an extra root. -/
theorem integerInner_anRoot_tripleRoot_mem (p : AnIndex 8) (t : TripleIndex) (b : Bool) :
    integerInner (e₈ARoot (.inl p)) (e₈ARoot (.inr (t, b))) ∈
      ({-18, -9, 0, 9, 18} : Set ℤ) := by
  rw [e₈ARoot, e₈ARoot, integerInner_mul, anRoot, integerInner_pairVector]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, tripleRoot, rootSign]
  split_ifs <;> norm_num

/-- Model (i). The integer angle condition for tripled E₈ roots. -/
theorem integerInner_e₈ARoot_mem (a b : E₈AIndex) :
    integerInner (e₈ARoot a) (e₈ARoot b) ∈ ({-2 * 9, -9, 0, 9, 2 * 9} : Set ℤ) := by
  rcases a with p | ⟨s, c⟩ <;> rcases b with q | ⟨t, d⟩
  · rw [e₈ARoot, e₈ARoot, integerInner_mul]
    have h := integerInner_anRoot_mem p q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    omega
  · exact integerInner_anRoot_tripleRoot_mem p t d
  · have he : integerInner (e₈ARoot (.inr (s, c))) (e₈ARoot (.inl q)) =
        integerInner (e₈ARoot (.inl q)) (e₈ARoot (.inr (s, c))) := dotProduct_comm _ _
    rw [he]
    exact integerInner_anRoot_tripleRoot_mem q s c
  · rw [e₈ARoot, e₈ARoot, integerInner_mul, integerInner_tripleRoot]
    have h : (s.val ∩ t.val).card ≤ 3 := by
      calc (s.val ∩ t.val).card ≤ t.val.card := Finset.card_le_card Finset.inter_subset_right
           _ = 3 := t.property
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, rootSign]
    split_ifs <;> omega

/-- Model (i). Signed triples give distinct vectors. -/
theorem tripleRoot_signed_injective :
    Function.Injective (fun p : TripleIndex × Bool ↦ fun i ↦ rootSign p.2 * tripleRoot p.1 i) := by
  rintro ⟨s, b⟩ ⟨t, c⟩ h
  have hbc : b = c := by
    have h0 := congrFun h 0
    cases b <;> cases c <;> try rfl
    all_goals
      simp only [rootSign, Bool.false_eq_true, ite_false, ite_true,
        tripleRoot] at h0
      split_ifs at h0 <;> norm_num at h0
  subst c
  congr 1
  apply tripleRoot_injective
  funext i
  exact mul_left_cancel₀ (rootSign_ne_zero b) (congrFun h i)

/-- Model (i). The structured index has no duplicate vectors. -/
theorem e₈ARoot_injective : Function.Injective e₈ARoot := by
  intro a b h
  rcases a with p | ⟨s, c⟩ <;> rcases b with q | ⟨t, d⟩
  · congr 1
    apply anRoot_injective
    funext i
    have hi := congrFun h i
    change 3 * anRoot p i = 3 * anRoot q i at hi
    omega
  · have hi := congrFun h p.val.1
    simp only [e₈ARoot, anRoot, pairVector, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne p.property, add_zero, rootSign, tripleRoot] at hi
    split_ifs at hi <;> norm_num at hi
  · have hi := congrFun h q.val.1
    simp only [e₈ARoot, anRoot, pairVector, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne q.property, add_zero, rootSign, tripleRoot] at hi
    split_ifs at hi <;> norm_num at hi
  · exact congrArg Sum.inr (tripleRoot_signed_injective h)

-- Definition 3.2
/-- Definition 3.2 of [CGSS]. Model (i). A₈ and the signed triple roots, in nine coordinates.
All roots lie in the hyperplane perpendicular to the all-ones vector. -/
noncomputable def E₈viaA₈ : LineSystem (EuclideanSpace ℝ (Fin 9)) :=
  ofIntegerRoots e₈ARoot 9 (1 / 3) (by norm_num) integerInner_e₈ARoot_self e₈ARoot_neg
    integerInner_e₈ARoot_mem

/-- Integer presentation of `E₈viaA₈`. -/
noncomputable instance E₈viaA₈.integerModel : IntegerModel E₈viaA₈ :=
  ofIntegerRootsModel _ _ _ _ _ _ _ e₈ARoot_injective

/-- Model (i) has 72 A₈ roots and twice 84 triple roots. -/
theorem card_E₈AIndex : Fintype.card E₈AIndex = 240 := by
  rw [Fintype.card_sum, card_AnIndex, Fintype.card_prod, Fintype.card_finset_len]
  norm_num [Nat.choose]

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. Model (i) has 120 lines. -/
theorem numLines_E₈viaA₈ : E₈viaA₈.numLines = 120 := by
  rw [E₈viaA₈.integerModel.numLines_eq,
    Fintype.card_congr (show E₈viaA₈.integerModel.ι ≃ E₈AIndex from Equiv.refl _),
    card_E₈AIndex]

-- Definition 3.2
/-- Definition 3.2 of [CGSS]. Model (iii). The fourteen blocks with the labelling of errata Gap 5.
The paper's labels 1 through 8 are represented by 0 through 7. -/
def steiner348 : Finset (Finset (Fin 8)) :=
  {{0, 1, 2, 3}, {0, 1, 4, 5}, {0, 1, 6, 7}, {0, 2, 4, 6}, {0, 2, 5, 7},
    {0, 3, 4, 7}, {0, 3, 5, 6}, {1, 2, 4, 7}, {1, 2, 5, 6}, {1, 3, 4, 6},
    {1, 3, 5, 7}, {2, 3, 4, 5}, {2, 3, 6, 7}, {4, 5, 6, 7}}

/-- Model (iii). A block of the fixed Steiner system. -/
abbrev SteinerBlock := {b : Finset (Fin 8) // b ∈ steiner348}

/-- Model (iii). All blocks contain four coordinates. -/
theorem steinerBlock_card : ∀ b : SteinerBlock, b.val.card = 4 := by decide +kernel

/-- Model (iii). Block intersections have even size. -/
theorem steinerBlock_inter_even : ∀ b c : SteinerBlock,
    ((b.val ∩ c.val).card : ℤ) % 2 = 0 := by decide +kernel

/-- Model (iii). Every triple lies in exactly one block. -/
theorem existsUnique_subset_steiner348 : ∀ t : {t : Finset (Fin 8) // t.card = 3},
    ∃! b : SteinerBlock, t.val ⊆ b.val := by
  unfold ExistsUnique
  decide +kernel

/-- Model (iii). An independent sign on each point of a block. -/
abbrev SteinerSignIndex := (b : SteinerBlock) × (b.val → Bool)

/-- Model (iii). The four signed unit coordinates on a block. -/
def steinerRoot (p : SteinerSignIndex) (i : Fin 8) : ℤ :=
  if h : i ∈ p.1.val then rootSign (p.2 ⟨i, h⟩) else 0

/-- Model (iii). The block is precisely the nonzero support. -/
theorem steinerRoot_ne_zero_iff (p : SteinerSignIndex) (i : Fin 8) :
    steinerRoot p i ≠ 0 ↔ i ∈ p.1.val := by
  simp only [steinerRoot]
  split_ifs <;> simp_all [rootSign_ne_zero]

/-- Model (iii). Each coordinate lies between minus and plus one. -/
theorem steinerRoot_bounds (p : SteinerSignIndex) (i : Fin 8) :
    -1 ≤ steinerRoot p i ∧ steinerRoot p i ≤ 1 := by
  simp only [steinerRoot, rootSign]
  split_ifs <;> omega

/-- Model (iii). The signed block roots have squared norm four. -/
theorem integerInner_steinerRoot_self (p : SteinerSignIndex) :
    integerInner (steinerRoot p) (steinerRoot p) = 4 := by
  have he (i : Fin 8) : steinerRoot p i * steinerRoot p i =
      if i ∈ p.1.val then 1 else 0 := by
    simp only [steinerRoot, rootSign]
    split_ifs <;> norm_num
  simp [integerInner, dotProduct, he, steinerBlock_card]

/-- Model (iii). Negation complements the four signs. -/
theorem steinerRoot_neg (p : SteinerSignIndex) :
    steinerRoot ⟨p.1, fun i ↦ !(p.2 i)⟩ = -steinerRoot p := by
  ext i
  simp only [steinerRoot, Pi.neg_apply]
  split_ifs with hi
  · cases p.2 ⟨i, hi⟩ <;> rfl
  · rfl

/-- Model (iii). Block intersections determine dot products modulo two.
This reduces the parity check to 196 pairs of blocks. -/
theorem integerInner_steinerRoot_even (p q : SteinerSignIndex) :
    integerInner (steinerRoot p) (steinerRoot q) % 2 = 0 := by
  have hs (a b : Bool) : (rootSign a * rootSign b) % 2 = 1 := by
    cases a <;> cases b <;> decide
  have he (i : Fin 8) : (steinerRoot p i * steinerRoot q i) % 2 =
      if i ∈ p.1.val ∩ q.1.val then 1 else 0 := by
    simp only [steinerRoot, Finset.mem_inter]
    split_ifs <;> simp only [hs, mul_zero, zero_mul, Int.zero_emod] <;> tauto
  rw [integerInner, dotProduct, Finset.sum_int_mod]
  simp_rw [he]
  have hinter : Finset.univ.filter (fun i : Fin 8 ↦ i ∈ p.1.val ∧ i ∈ q.1.val) =
      p.1.val ∩ q.1.val := by ext; simp
  simpa [hinter] using steinerBlock_inter_even p.1 q.1

/-- Model (iii). Four nonzero coordinates bound the dot product. -/
theorem integerInner_steinerRoot_bounds (p q : SteinerSignIndex) :
    -4 ≤ integerInner (steinerRoot p) (steinerRoot q) ∧
      integerInner (steinerRoot p) (steinerRoot q) ≤ 4 := by
  have hb (i : Fin 8) :
      -(if i ∈ p.1.val then 1 else 0) ≤ steinerRoot p i * steinerRoot q i ∧
      steinerRoot p i * steinerRoot q i ≤ (if i ∈ p.1.val then 1 else 0) := by
    have hq := steinerRoot_bounds q i
    by_cases hi : i ∈ p.1.val
    · rw [show steinerRoot p i = rootSign (p.2 ⟨i, hi⟩) by simp [steinerRoot, hi]]
      cases p.2 ⟨i, hi⟩ <;> simp [rootSign, hi] <;> omega
    · simp [steinerRoot, hi]
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 8))) ↦ (hb i).1)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 8))) ↦ (hb i).2)
  have hs : (∑ i : Fin 8, (if i ∈ p.1.val then 1 else 0 : ℤ)) = 4 := by
    simp [steinerBlock_card]
  rw [Finset.sum_neg_distrib, hs] at hl
  rw [hs] at hu
  exact ⟨hl, hu⟩

/-- Model (iii). The angle condition for block roots. -/
theorem integerInner_steinerRoot_mem (p q : SteinerSignIndex) :
    integerInner (steinerRoot p) (steinerRoot q) ∈ ({-4, -2, 0, 2, 4} : Set ℤ) := by
  have he := integerInner_steinerRoot_even p q
  have hb := integerInner_steinerRoot_bounds p q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Model (iii). Supports and their signs recover block-root indices. -/
theorem steinerRoot_injective : Function.Injective steinerRoot := by
  rintro ⟨b, s⟩ ⟨c, t⟩ h
  have hbc : b = c := by
    apply Subtype.ext
    ext i
    rw [← steinerRoot_ne_zero_iff ⟨b, s⟩, ← steinerRoot_ne_zero_iff ⟨c, t⟩, h]
  subst c
  congr 1
  funext i
  apply rootSign_injective
  simpa [steinerRoot, i.property] using congrFun h i.val

/-- Model (iii). A signed coordinate axis of length two. -/
def axisRoot (p : Fin 8 × Bool) : Fin 8 → ℤ := Pi.single p.1 (2 * rootSign p.2)

/-- Model (iii). Axis roots have squared norm four. -/
theorem integerInner_axisRoot_self : ∀ p, integerInner (axisRoot p) (axisRoot p) = 4 := by
  decide +kernel

/-- Model (iii). Negation reverses the axis sign. -/
theorem axisRoot_neg : ∀ p : Fin 8 × Bool, axisRoot (p.1, !p.2) = -axisRoot p := by
  decide +kernel

/-- Model (iii). The sixteen oriented axes are distinct. -/
theorem axisRoot_injective : Function.Injective axisRoot := by decide +kernel

/-- Model (iii). Dot products against the signed axes. -/
theorem integerInner_axisRoot (p : Fin 8 × Bool) (v : Fin 8 → ℤ) :
    integerInner (axisRoot p) v = 2 * rootSign p.2 * v p.1 := by
  simp [integerInner, dotProduct, axisRoot, Pi.single_apply, ite_mul]

/-- Model (iii). The signed axes and signed blocks. -/
abbrev E₈SteinerIndex := (Fin 8 × Bool) ⊕ SteinerSignIndex

/-- Model (iii). The integral roots of squared norm four. -/
def e₈SteinerRoot : E₈SteinerIndex → Fin 8 → ℤ
  | .inl p => axisRoot p
  | .inr p => steinerRoot p

/-- Model (iii). Every integer root has squared norm four. -/
theorem integerInner_e₈SteinerRoot_self (a : E₈SteinerIndex) :
    integerInner (e₈SteinerRoot a) (e₈SteinerRoot a) = 2 * 2 := by
  cases a with
  | inl p => exact integerInner_axisRoot_self p
  | inr p => exact integerInner_steinerRoot_self p

/-- Model (iii). Both signs of every root occur. -/
theorem e₈SteinerRoot_neg (a : E₈SteinerIndex) : ∃ b, e₈SteinerRoot b = -e₈SteinerRoot a := by
  cases a with
  | inl p => exact ⟨.inl (p.1, !p.2), axisRoot_neg p⟩
  | inr p => exact ⟨.inr ⟨p.1, fun i ↦ !(p.2 i)⟩, steinerRoot_neg p⟩

/-- Model (iii). The angle condition between an axis and a block root. -/
theorem integerInner_axisRoot_steinerRoot_mem (p : Fin 8 × Bool) (q : SteinerSignIndex) :
    integerInner (axisRoot p) (steinerRoot q) ∈ ({-4, -2, 0, 2, 4} : Set ℤ) := by
  rw [integerInner_axisRoot]
  have hq := steinerRoot_bounds q p.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, rootSign]
  split_ifs <;> omega

/-- Model (iii). The angle condition for the integral Steiner model. -/
theorem integerInner_e₈SteinerRoot_mem (a b : E₈SteinerIndex) :
    integerInner (e₈SteinerRoot a) (e₈SteinerRoot b) ∈ ({-2 * 2, -2, 0, 2, 2 * 2} : Set ℤ) := by
  rcases a with p | p <;> rcases b with q | q
  · have h : ∀ p q, integerInner (axisRoot p) (axisRoot q) ∈
        ({-4, -2, 0, 2, 4} : Set ℤ) := by decide +kernel
    exact h p q
  · exact integerInner_axisRoot_steinerRoot_mem p q
  · have he : integerInner (e₈SteinerRoot (.inr p)) (e₈SteinerRoot (.inl q)) =
        integerInner (axisRoot q) (steinerRoot p) := dotProduct_comm _ _
    rw [he]
    exact integerInner_axisRoot_steinerRoot_mem q p
  · exact integerInner_steinerRoot_mem p q

/-- Model (iii). The structured root indices have no duplicates. -/
theorem e₈SteinerRoot_injective : Function.Injective e₈SteinerRoot := by
  intro a b h
  rcases a with p | p <;> rcases b with q | q
  · exact congrArg Sum.inl (axisRoot_injective h)
  · have hi := congrFun h p.1
    have hb := steinerRoot_bounds q p.1
    simp only [e₈SteinerRoot, axisRoot, Pi.single_eq_same, rootSign] at hi
    split_ifs at hi <;> omega
  · have hi := congrFun h q.1
    have hb := steinerRoot_bounds p q.1
    simp only [e₈SteinerRoot, axisRoot, Pi.single_eq_same, rootSign] at hi
    split_ifs at hi <;> omega
  · exact congrArg Sum.inr (steinerRoot_injective h)

-- Definition 3.2
/-- Definition 3.2 of [CGSS]. Model (iii). The Steiner model, normalized by `1 / √2`. -/
noncomputable def E₈viaSteiner : LineSystem (EuclideanSpace ℝ (Fin 8)) :=
  ofIntegerRoots e₈SteinerRoot 2 (Real.sqrt 2)⁻¹
    (by norm_num only [Int.cast_ofNat]
        have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hp : Real.sqrt 2 ≠ 0 := by positivity
        field_simp
        nlinarith)
    integerInner_e₈SteinerRoot_self e₈SteinerRoot_neg integerInner_e₈SteinerRoot_mem

/-- Integer presentation of `E₈viaSteiner`. -/
noncomputable instance E₈viaSteiner.integerModel : IntegerModel E₈viaSteiner :=
  ofIntegerRootsModel _ _ _ _ _ _ _ e₈SteinerRoot_injective

/-- The fixed Steiner system has fourteen blocks. -/
theorem card_steiner348 : steiner348.card = 14 := by decide +kernel

/-- The model has sixteen axes and sixteen signs per block. -/
theorem card_E₈SteinerIndex : Fintype.card E₈SteinerIndex = 240 := by
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp [steinerBlock_card, card_steiner348, SteinerBlock]

-- Lemma 3.4
/-- Lemma 3.4 of [CGSS]. The Steiner model has 120 lines. -/
theorem numLines_E₈viaSteiner : E₈viaSteiner.numLines = 120 := by
  rw [E₈viaSteiner.integerModel.numLines_eq,
    Fintype.card_congr (show E₈viaSteiner.integerModel.ι ≃ E₈SteinerIndex from Equiv.refl _),
    card_E₈SteinerIndex]

/-- A signed pair has a D index regardless of the order of its coordinates. -/
theorem exists_dnRoot_eq_pairVector {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    ∃ p : DnIndex n, dnRoot p = pairVector i j (rootSign a) (rootSign b) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨(⟨(i, j), h⟩, a, b), rfl⟩
  · refine ⟨(⟨(j, i), h⟩, b, a), ?_⟩
    exact add_comm _ _

/-- Coordinate differences are A roots. -/
theorem sub_single_mem_An {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈ (An n).Φ := by
  refine ⟨⟨(i, j), hij⟩, ?_⟩
  ext k
  simp [integerVector, anRoot, pairVector, Pi.single_apply, PiLp.single_apply]
  split_ifs <;> norm_num

/-- The literal inclusion of the A family in the D family. -/
theorem An_Φ_subset_Dn (n : ℕ) : (An n).Φ ⊆ (Dn (n + 1)).Φ := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨p, hp⟩ := exists_dnRoot_eq_pairVector a.val.1 a.val.2 a.property false true
  exact ⟨p, congrArg (integerVector 1) hp⟩

/-- Positive signed pairs are D roots. -/
theorem add_single_mem_Dn {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 ∈ (Dn n).Φ := by
  obtain ⟨p, hp⟩ := exists_dnRoot_eq_pairVector i j hij false false
  refine ⟨p, ?_⟩
  ext k
  simp [integerVector, hp, pairVector, rootSign, Pi.single_apply, PiLp.single_apply]

/-- Oppositely signed pairs are D roots. -/
theorem sub_single_mem_Dn {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j 1 ∈ (Dn n).Φ := by
  obtain ⟨p, hp⟩ := exists_dnRoot_eq_pairVector i j hij false true
  refine ⟨p, ?_⟩
  ext k
  simp [integerVector, hp, pairVector, rootSign, Pi.single_apply, PiLp.single_apply]
  split_ifs <;> norm_num

/-- The D₈ roots are a literal subset of the default E₈ model. -/
theorem Dn_Φ_subset_E₈ : (Dn 8).Φ ⊆ E₈.Φ := by
  rintro _ ⟨a, rfl⟩
  refine ⟨Sum.inl a, ?_⟩
  ext i
  simp [integerVector, e₈Root]

/-- The A₈ roots are a literal subset of the nine-coordinate E₈ model. -/
theorem An_Φ_subset_E₈viaA₈ : (An 8).Φ ⊆ E₈viaA₈.Φ := by
  rintro _ ⟨a, rfl⟩
  refine ⟨Sum.inl a, ?_⟩
  ext i
  simp [integerVector, e₈ARoot]

/-- The first orthogonal restriction is an inclusion. -/
theorem E₇_Φ_subset_E₈ : E₇.Φ ⊆ E₈.Φ := E₈.orthogonalTo_Φ_subset e₇Normal

/-- The second orthogonal restriction is an inclusion. -/
theorem E₆_Φ_subset_E₇ : E₆.Φ ⊆ E₇.Φ := E₇.orthogonalTo_Φ_subset e₆Normal

/- The qualified API follows §10. The older unqualified names remain available to the
existing certificates, so their proofs need not be regenerated merely for a rename. -/
abbrev An.Index := AnIndex
abbrev An.root {n : ℕ} := anRoot (n := n)
abbrev Dn.Index := DnIndex
abbrev Dn.root {n : ℕ} := dnRoot (n := n)
abbrev E₈viaD₈.Index := E₈Index
abbrev E₈viaD₈.root := e₈Root
abbrev E₈viaA₈.Index := E₈AIndex
abbrev E₈viaA₈.root := e₈ARoot
abbrev E₈viaSteiner.Index := E₈SteinerIndex
abbrev E₈viaSteiner.root := e₈SteinerRoot
abbrev E₇.Index := E₇Index
abbrev E₇.root (a : E₇.Index) := e₈Root a.val
abbrev E₆.Index := E₆Index
abbrev E₆.root (a : E₆.Index) := e₈Root a.val

end LineSystem
