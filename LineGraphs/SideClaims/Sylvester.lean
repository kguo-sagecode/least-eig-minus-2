/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Hadamard.Pairs
import LineGraphs.Computations.C16Order2
import LineGraphs.Computations.C16Order4
import LineGraphs.Computations.C16Order8
import LineGraphs.Computations.C16Order16

/-!
# Sylvester matrices

Two side claims of [CGSS], J. Algebra 43 (1976), Section 6 (p. 326), about the Hadamard
matrices of Sylvester type.

* p. 326: "The only known examples are the Hadamard matrices of Sylvester type with
  `n = 2^s` and `x = n`, and the unique `H₁₂` with `n = 12` and `x = 4`." We prove that the
  Sylvester matrix of every order `n = 2 ^ s` satisfies Hypothesis 6.1 with `x = n`
  (`Matrix.sylvester_fourRowAgreement`). Computation C16 checks this for `n = 2, 4, 8, 16` only,
  and its four matrices are the ones defined here (`Computations.C16.h2_eq_sylvester`, ...,
  `Computations.C16.h16_eq_sylvester`). The words "only known" are history, and the uniqueness
  of `H₁₂` is set aside by the author's decision; neither is formalized.
* p. 326: "The Sylvester case corresponds to `d = 1` and yields `n − 1` mutually orthogonal
  lines, each line occurring `½n` times." Here `d = n / x = 1`. The product of rows `i` and `j`
  is row `i ^^^ j`, the bitwise exclusive or of the indices
  (`Matrix.hadamardRowProduct_sylvester`). So the `½n(n − 1)` rows of `P` are the `n − 1` rows
  of the Sylvester matrix other than the all-ones row `0`
  (`Matrix.exists_hadamardRowProduct_sylvester_eq`, `Matrix.image_hadamardRowProduct_sylvester`,
  `Matrix.card_image_hadamardRowProduct_sylvester`),
  each of them is the product of exactly `½n` pairs of rows
  (`Matrix.two_mul_card_filter_hadamardRowProduct_sylvester`), and distinct ones are orthogonal
  (`Matrix.inner_hadamardRowProduct_sylvester_of_ne`). `Matrix.sylvester_lines` states the claim
  for the lines that the rows of `P` span.

## The definition

`Matrix.sylvesterZMod s` is the closed form, indexed by `(ZMod 2)^s`: the entry in row `a` and
column `b` is `(-1)^(a ⬝ᵥ b)`. `Matrix.sylvester s` reindexes it by `Fin (2 ^ s)` through binary
digits (`Matrix.sylvesterEquiv`), under which addition of vectors is the bitwise exclusive or of
indices (`Matrix.sylvesterEquiv_add`). Sylvester's construction `H₂ₙ = H₂ ⊗ Hₙ` is
`Matrix.sylvester_succ`, with `Matrix.sylvester_zero` and `Matrix.sylvester_one`. So
`Matrix.sylvester s` is the classical iterated Kronecker product of `s` copies of
`!![1, 1; 1, -1]`, which is `Matrix.sylvesterKronecker s`
(`Matrix.sylvesterKronecker_eq_sylvester`).

## The proof of Hypothesis 6.1

For four distinct rows `i`, `j`, `k`, `l`, blueprint Lemma `lem:6-gram`
(`Matrix.IsHadamard.inner_hadamardPairs_of_disjoint`) gives `8 · agree = n + ⟪P_ij, P_kl⟫`. Both
`P_ij` and `P_kl` are rows of the Sylvester matrix, so their inner product is `n` or `0`, and
`8 · agree` is `2n = n + x` or `n`.
-/

open scoped BigOperators RealInnerProductSpace Kronecker
open Submodule

namespace Matrix

/-! ### The definition -/

/-- The indexing of the Sylvester matrix of order `2 ^ s`: the vector `a` of `(ZMod 2)^s` is the
index `∑ i, a i * 2 ^ i` of `Fin (2 ^ s)`, so that `a i` is its binary digit of weight `2 ^ i`. -/
def sylvesterEquiv (s : ℕ) : (Fin s → ZMod 2) ≃ Fin (2 ^ s) := finFunctionFinEquiv

/-- The Sylvester matrix of order `2 ^ s` in closed form, indexed by `(ZMod 2)^s`: the entry in
row `a` and column `b` is `(-1) ^ (a ⬝ᵥ b)`. -/
def sylvesterZMod (s : ℕ) : Matrix (Fin s → ZMod 2) (Fin s → ZMod 2) ℤ :=
  of fun a b ↦ (-1) ^ (a ⬝ᵥ b).val

/-- The Sylvester matrix of order `2 ^ s` ([CGSS], Section 6, p. 326, "Hadamard matrices of
Sylvester type"), indexed by `Fin (2 ^ s)`: the closed form `sylvesterZMod s`, reindexed by the
binary digits `sylvesterEquiv s`. It is the iterated Kronecker product of `s` copies of
`!![1, 1; 1, -1]` (`sylvester_zero`, `sylvester_succ`). -/
def sylvester (s : ℕ) : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℤ :=
  reindex (sylvesterEquiv s) (sylvesterEquiv s) (sylvesterZMod s)

theorem sylvesterZMod_apply (s : ℕ) (a b : Fin s → ZMod 2) :
    sylvesterZMod s a b = (-1) ^ (a ⬝ᵥ b).val :=
  rfl

theorem sylvester_apply (s : ℕ) (i j : Fin (2 ^ s)) :
    sylvester s i j =
      sylvesterZMod s ((sylvesterEquiv s).symm i) ((sylvesterEquiv s).symm j) :=
  rfl

theorem sylvester_apply_sylvesterEquiv (s : ℕ) (a b : Fin s → ZMod 2) :
    sylvester s (sylvesterEquiv s a) (sylvesterEquiv s b) = sylvesterZMod s a b := by
  simp [sylvester_apply]

theorem sylvesterEquiv_val (s : ℕ) (a : Fin s → ZMod 2) :
    (sylvesterEquiv s a : ℕ) = ∑ i : Fin s, (a i).val * 2 ^ (i : ℕ) :=
  rfl

/-- The zero vector is the index `0`. -/
theorem sylvesterEquiv_zero (s : ℕ) : sylvesterEquiv s 0 = 0 := by
  apply Fin.ext
  rw [sylvesterEquiv_val, Fin.val_zero]
  simp

/-! ### Arithmetic in `(ZMod 2)^s` -/

/-- The sign `(-1) ^ z` is additive in `z : ZMod 2`. -/
private theorem neg_one_pow_val_add (x y : ZMod 2) :
    (-1 : ℤ) ^ (x + y).val = (-1) ^ x.val * (-1) ^ y.val := by
  revert x y
  decide

private theorem add_self_zmod {s : ℕ} (x : Fin s → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  revert a
  decide

private theorem add_eq_zero_iff_zmod {s : ℕ} (x y : Fin s → ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + (y + y) := by rw [add_self_zmod, add_zero]
      _ = x + y + y := by rw [add_assoc]
      _ = y := by rw [h, zero_add]
  · rintro rfl
    exact add_self_zmod x

/-! ### The closed form as a matrix of characters -/

/-- The product of rows `a` and `b` of the closed form is row `a + b`. -/
theorem sylvesterZMod_mul_sylvesterZMod (s : ℕ) (a b c : Fin s → ZMod 2) :
    sylvesterZMod s a c * sylvesterZMod s b c = sylvesterZMod s (a + b) c := by
  simp only [sylvesterZMod_apply, add_dotProduct, neg_one_pow_val_add]

theorem sylvesterZMod_comm (s : ℕ) (a b : Fin s → ZMod 2) :
    sylvesterZMod s a b = sylvesterZMod s b a := by
  simp only [sylvesterZMod_apply, dotProduct_comm]

theorem sylvesterZMod_zero_left (s : ℕ) (b : Fin s → ZMod 2) : sylvesterZMod s 0 b = 1 := by
  simp [sylvesterZMod_apply]

/-- Row `a` of the closed form sums to `2 ^ s` if `a = 0`, and to `0` otherwise. -/
theorem sum_sylvesterZMod (s : ℕ) (a : Fin s → ZMod 2) :
    ∑ b, sylvesterZMod s a b = if a = 0 then 2 ^ s else 0 := by
  split_ifs with ha
  · subst ha
    simp [sylvesterZMod_zero_left, ZMod.card]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hai : a i = 1 := by
      have hi' : a i ≠ 0 := hi
      revert hi'
      generalize a i = x
      revert x
      decide
    have hshift (b : Fin s → ZMod 2) :
        sylvesterZMod s a (b + Pi.single i 1) = -sylvesterZMod s a b := by
      simp only [sylvesterZMod_apply, dotProduct_add, neg_one_pow_val_add, dotProduct_single,
        hai, mul_one]
      rw [show (-1 : ℤ) ^ (1 : ZMod 2).val = -1 by decide, mul_neg_one]
    have h := Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2)))
      (fun b ↦ sylvesterZMod s a b)
    simp only [Equiv.coe_addRight, hshift, Finset.sum_neg_distrib] at h
    linarith

/-! ### The Hadamard property -/

theorem isHadamard_sylvesterZMod (s : ℕ) : (sylvesterZMod s).IsHadamard := by
  have hsymm : (sylvesterZMod s)ᴴ = sylvesterZMod s := by
    ext a b
    rw [conjTranspose_apply, star_trivial, sylvesterZMod_comm]
  have hmul : sylvesterZMod s * (sylvesterZMod s)ᴴ =
      (Fintype.card (Fin s → ZMod 2) : ℤ) • (1 : Matrix (Fin s → ZMod 2) _ ℤ) := by
    rw [hsymm]
    ext a b
    simp only [mul_apply, smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp_rw [sylvesterZMod_comm s _ b, sylvesterZMod_mul_sylvesterZMod, sum_sylvesterZMod,
      add_eq_zero_iff_zmod]
    simp [ZMod.card]
  refine ⟨fun a b ↦ Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (neg_one_pow_eq_or ℤ _), hmul, ?_⟩
  rw [hsymm] at hmul ⊢
  exact hmul

/-- The Sylvester matrix of order `2 ^ s` is a Hadamard matrix ([CGSS], Section 6,
p. 326). -/
theorem isHadamard_sylvester (s : ℕ) : (sylvester s).IsHadamard :=
  (isHadamard_sylvesterZMod s).reindex _ _

/-- Row `0` of the Sylvester matrix is the all-ones row. -/
theorem sylvester_apply_zero_left (s : ℕ) (j : Fin (2 ^ s)) : sylvester s 0 j = 1 := by
  rw [sylvester_apply, ← sylvesterEquiv_zero, Equiv.symm_apply_apply, sylvesterZMod_zero_left]

/-! ### Sylvester's construction -/

/-- The index of the vector `a` extended by the top digit `x`. -/
theorem sylvesterEquiv_snoc (s : ℕ) (a : Fin s → ZMod 2) (x : ZMod 2) :
    (sylvesterEquiv (s + 1) (Fin.snoc a x : Fin (s + 1) → ZMod 2) : ℕ) =
      sylvesterEquiv s a + 2 ^ s * x.val := by
  rw [sylvesterEquiv_val, sylvesterEquiv_val, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  ring

private theorem snoc_dotProduct_snoc {s : ℕ} (a b : Fin s → ZMod 2) (x y : ZMod 2) :
    (Fin.snoc a x : Fin (s + 1) → ZMod 2) ⬝ᵥ (Fin.snoc b y : Fin (s + 1) → ZMod 2) =
      a ⬝ᵥ b + x * y := by
  simp only [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The indexing of `!![1, 1; 1, -1] ⊗ₖ sylvester s` by `Fin (2 ^ (s + 1))`: the pair `(x, i)`
is the index `2 ^ s * x + i`, so that `x` is the top binary digit. -/
def sylvesterProdEquiv (s : ℕ) : Fin 2 × Fin (2 ^ s) ≃ Fin (2 ^ (s + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ' 2 s).symm)

theorem sylvesterProdEquiv_apply_val (s : ℕ) (x : Fin 2) (i : Fin (2 ^ s)) :
    (sylvesterProdEquiv s (x, i) : ℕ) = i + 2 ^ s * x := by
  simp [sylvesterProdEquiv, finProdFinEquiv_apply_val]

private theorem sylvesterProdEquiv_sylvesterEquiv (s : ℕ) (x : Fin 2) (a : Fin s → ZMod 2) :
    sylvesterProdEquiv s (x, sylvesterEquiv s a) =
      sylvesterEquiv (s + 1) (Fin.snoc a ((x : ℕ) : ZMod 2) : Fin (s + 1) → ZMod 2) := by
  apply Fin.ext
  rw [sylvesterProdEquiv_apply_val, sylvesterEquiv_snoc, ZMod.val_cast_of_lt x.isLt]

/-- The Sylvester matrix of order `1`. -/
theorem sylvester_zero : sylvester 0 = !![1] := by
  have h : ∀ ij : Fin 1 × Fin 1, sylvester 0 ij.1 ij.2 = (!![1] : Matrix _ _ ℤ) ij.1 ij.2 := by
    decide +kernel
  ext i j
  exact h (i, j)

/-- The Sylvester matrix of order `2` is `H₂ = !![1, 1; 1, -1]`. -/
theorem sylvester_one : sylvester 1 = !![1, 1; 1, -1] := by
  have h : ∀ ij : Fin 2 × Fin 2,
      sylvester 1 ij.1 ij.2 = (!![1, 1; 1, -1] : Matrix _ _ ℤ) ij.1 ij.2 := by
    decide +kernel
  ext i j
  exact h (i, j)

/-- Sylvester's construction `H₂ₙ = H₂ ⊗ Hₙ`: `sylvester (s + 1)` is the Kronecker product of
`!![1, 1; 1, -1]` and `sylvester s`, that is, the block matrix `!![H, H; H, -H]` for
`H = sylvester s`, with the rows and columns indexed as in `sylvesterProdEquiv`. -/
theorem sylvester_succ (s : ℕ) :
    sylvester (s + 1) = reindex (sylvesterProdEquiv s) (sylvesterProdEquiv s)
      (!![1, 1; 1, -1] ⊗ₖ sylvester s) := by
  have h2 (x y : Fin 2) : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ) x y =
      (-1) ^ (((x : ℕ) : ZMod 2) * ((y : ℕ) : ZMod 2)).val := by
    fin_cases x <;> fin_cases y <;> decide
  ext I J
  obtain ⟨⟨x, i⟩, rfl⟩ := (sylvesterProdEquiv s).surjective I
  obtain ⟨⟨y, j⟩, rfl⟩ := (sylvesterProdEquiv s).surjective J
  obtain ⟨a, rfl⟩ := (sylvesterEquiv s).surjective i
  obtain ⟨b, rfl⟩ := (sylvesterEquiv s).surjective j
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply]
  simp only [sylvesterProdEquiv_sylvesterEquiv, sylvester_apply_sylvesterEquiv,
    sylvesterZMod_apply, snoc_dotProduct_snoc, neg_one_pow_val_add, h2]
  ring

/-- The classical definition of the Sylvester matrix of order `2 ^ s`: the iterated Kronecker
product `H₂ ⊗ (H₂ ⊗ (⋯ ⊗ H₂))` of `s` copies of `H₂ = !![1, 1; 1, -1]`, reindexed at each step
by `sylvesterProdEquiv`. It agrees with `sylvester s` (`sylvesterKronecker_eq_sylvester`). -/
def sylvesterKronecker : (s : ℕ) → Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℤ
  | 0 => !![1]
  | s + 1 => reindex (sylvesterProdEquiv s) (sylvesterProdEquiv s)
      (!![1, 1; 1, -1] ⊗ₖ sylvesterKronecker s)

/-- The iterated Kronecker product and the closed form define the same Sylvester matrix. -/
theorem sylvesterKronecker_eq_sylvester (s : ℕ) : sylvesterKronecker s = sylvester s := by
  induction s with
  | zero =>
    rw [sylvester_zero]
    rfl
  | succ s ih =>
    rw [sylvester_succ, ← ih]
    rfl

/-! ### Rows as real vectors -/

/-- Row `i` of `sylvester s`, as a vector of `ℝ^(2^s)`. -/
def sylvesterRow (s : ℕ) (i : Fin (2 ^ s)) : EuclideanSpace ℝ (Fin (2 ^ s)) :=
  WithLp.toLp 2 fun c ↦ (sylvester s i c : ℝ)

/-- Distinct rows of the Sylvester matrix are orthogonal, and each has squared norm `2 ^ s`. -/
theorem inner_sylvesterRow (s : ℕ) (i j : Fin (2 ^ s)) :
    ⟪sylvesterRow s i, sylvesterRow s j⟫ = if i = j then (2 : ℝ) ^ s else 0 := by
  have h := (isHadamard_sylvester s).sum_row_mul j i
  simp only [sylvesterRow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [h]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, hij.symm]

/-- Distinct rows of the Sylvester matrix are distinct vectors. -/
theorem sylvesterRow_injective (s : ℕ) : Function.Injective (sylvesterRow s) := by
  intro i j h
  by_contra hij
  have h1 := inner_sylvesterRow s i j
  rw [ite_eq_right hij, h, inner_sylvesterRow, ite_eq_left rfl] at h1
  exact pow_ne_zero s two_ne_zero h1

/-- Distinct rows of `sylvester s` span distinct lines. -/
theorem span_sylvesterRow_injective (s : ℕ) :
    Function.Injective fun i ↦ ℝ ∙ sylvesterRow s i := by
  intro i j h
  by_contra hij
  have hj : sylvesterRow s j ∈ ℝ ∙ sylvesterRow s i := by
    rw [show (ℝ ∙ sylvesterRow s i) = ℝ ∙ sylvesterRow s j from h]
    exact mem_span_singleton_self _
  obtain ⟨t, ht⟩ := mem_span_singleton.mp hj
  have h1 := inner_sylvesterRow s i j
  rw [ite_eq_right hij, ← ht, real_inner_smul_right, inner_sylvesterRow, ite_eq_left rfl] at h1
  have h2 := inner_sylvesterRow s j j
  rw [ite_eq_left rfl, ← ht, real_inner_smul_left, real_inner_smul_right, inner_sylvesterRow,
    ite_eq_left rfl, h1, mul_zero] at h2
  exact pow_ne_zero s two_ne_zero h2.symm

/-! ### Exclusive or on `Fin (2 ^ s)` -/

private theorem xor_mod_two (x y : ℕ) : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
  have h : (x ^^^ y) % 2 = 1 ↔ ¬ (x % 2 = 1 ↔ y % 2 = 1) := Nat.xor_mod_two_eq_one
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    rcases Nat.mod_two_eq_zero_or_one (x ^^^ y) with hxy | hxy <;>
    simp_all

/-- Under `sylvesterEquiv`, addition in `(ZMod 2)^s` is the bitwise exclusive or of indices. -/
theorem sylvesterEquiv_add (s : ℕ) (a b : Fin s → ZMod 2) :
    sylvesterEquiv s (a + b) = sylvesterEquiv s a ^^^ sylvesterEquiv s b := by
  apply (sylvesterEquiv s).symm.injective
  rw [Equiv.symm_apply_apply]
  funext k
  apply ZMod.val_injective
  have hdigit (x : Fin (2 ^ s)) :
      ((sylvesterEquiv s).symm x k).val = (x : ℕ) / 2 ^ (k : ℕ) % 2 :=
    finFunctionFinEquiv_symm_apply_val x k
  have ha : (a k).val = (sylvesterEquiv s a : ℕ) / 2 ^ (k : ℕ) % 2 := by
    rw [← hdigit, Equiv.symm_apply_apply]
  have hb : (b k).val = (sylvesterEquiv s b : ℕ) / 2 ^ (k : ℕ) % 2 := by
    rw [← hdigit, Equiv.symm_apply_apply]
  rw [Pi.add_apply, ZMod.val_add, ha, hb, hdigit, Fin.xor_val_of_two_pow, Nat.xor_div_two_pow,
    xor_mod_two]

private theorem fin_xor_xor_cancel_left {s : ℕ} (i j : Fin (2 ^ s)) : i ^^^ (i ^^^ j) = j := by
  apply Fin.ext
  rw [Fin.xor_val_of_two_pow, Fin.xor_val_of_two_pow, ← Nat.xor_assoc, Nat.xor_self,
    Nat.zero_xor]

private theorem fin_xor_xor_cancel_right {s : ℕ} (i j : Fin (2 ^ s)) : i ^^^ j ^^^ j = i := by
  apply Fin.ext
  rw [Fin.xor_val_of_two_pow, Fin.xor_val_of_two_pow, Nat.xor_assoc, Nat.xor_self,
    Nat.xor_zero]

private theorem fin_zero_xor {s : ℕ} (i : Fin (2 ^ s)) : 0 ^^^ i = i := by
  apply Fin.ext
  rw [Fin.xor_val_of_two_pow, Fin.val_zero, Nat.zero_xor]

private theorem fin_xor_eq_zero_iff {s : ℕ} (i j : Fin (2 ^ s)) : i ^^^ j = 0 ↔ i = j := by
  constructor
  · intro h
    have h' := fin_xor_xor_cancel_left i j
    rw [h] at h'
    rw [← h']
    apply Fin.ext
    rw [Fin.xor_val_of_two_pow, Fin.val_zero, Nat.xor_zero]
  · rintro rfl
    apply Fin.ext
    rw [Fin.xor_val_of_two_pow, Fin.val_zero, Nat.xor_self]

private theorem fin_xor_eq_iff {s : ℕ} (i j c : Fin (2 ^ s)) : i ^^^ j = c ↔ j = i ^^^ c := by
  constructor
  · rintro rfl
    exact (fin_xor_xor_cancel_left i j).symm
  · rintro rfl
    exact fin_xor_xor_cancel_left i c

/-! ### The row products -/

/-- [CGSS], Section 6, p. 326: the product of rows `a` and `b` of the Sylvester matrix is row
`a + b`, in the indexing by `(ZMod 2)^s`. -/
theorem hadamardRowProduct_sylvester_sylvesterEquiv (s : ℕ) (a b : Fin s → ZMod 2) :
    (sylvester s).hadamardRowProduct (sylvesterEquiv s a) (sylvesterEquiv s b) =
      sylvesterRow s (sylvesterEquiv s (a + b)) := by
  ext c
  simp only [hadamardRowProduct, sylvesterRow, sylvester_apply, Equiv.symm_apply_apply]
  exact_mod_cast sylvesterZMod_mul_sylvesterZMod s a b _

/-- [CGSS], Section 6, p. 326: the product of rows `i` and `j` of the Sylvester matrix is row
`i ^^^ j`, the bitwise exclusive or of the indices. -/
theorem hadamardRowProduct_sylvester (s : ℕ) (i j : Fin (2 ^ s)) :
    (sylvester s).hadamardRowProduct i j = sylvesterRow s (i ^^^ j) := by
  have h := hadamardRowProduct_sylvester_sylvesterEquiv s ((sylvesterEquiv s).symm i)
    ((sylvesterEquiv s).symm j)
  rwa [sylvesterEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

/-! ### Hypothesis 6.1 -/

/-- [CGSS], Section 6, p. 326: the Sylvester matrix of order `n = 2 ^ s` satisfies
Hypothesis 6.1 with `x = n`: any four distinct rows agree in `n / 8` or `n / 4 = (n + x) / 8`
places. -/
theorem sylvester_fourRowAgreement (s : ℕ) :
    (isHadamard_sylvester s).FourRowAgreement (2 ^ s) := by
  intro i j k l hij hik hil hjk hjl hkl
  have h := (isHadamard_sylvester s).inner_hadamardPairs_of_disjoint i j k l hij hik hil hjk hjl
    hkl
  rw [hadamardRowProduct_sylvester, hadamardRowProduct_sylvester, inner_sylvesterRow] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  push_cast at h ⊢
  split_ifs at h
  · refine Or.inr (Or.inr ?_)
    exact_mod_cast (by linarith :
      (8 * ((sylvester s).fourRowAgreeCount i j k l : ℝ)) = 2 ^ s + 2 ^ s)
  · refine Or.inl ?_
    exact_mod_cast (by linarith : (8 * ((sylvester s).fourRowAgreeCount i j k l : ℝ)) = 2 ^ s)

/-! ### The lines of the Sylvester case -/

private theorem two_mul_card_filter_lt_of_involutive {n : ℕ} (σ : Fin n → Fin n)
    (hσ : Function.Involutive σ) (hne : ∀ i, σ i ≠ i) :
    2 * (Finset.univ.filter fun i ↦ i < σ i).card = n := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    fun i : Fin n ↦ i < σ i
  have hswap : (Finset.univ.filter fun i : Fin n ↦ ¬ i < σ i).card =
      (Finset.univ.filter fun i : Fin n ↦ i < σ i).card := by
    refine Finset.card_equiv (hσ.toPerm σ) fun i ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Involutive.coe_toPerm,
      hσ i]
    exact ⟨fun h ↦ lt_of_le_of_ne (not_lt.mp h) (hne i), fun h ↦ not_lt.mpr h.le⟩
  rw [Finset.card_univ, Fintype.card_fin, hswap] at hsplit
  omega

private theorem card_filter_hadamardPair_eq {n : ℕ} (σ : Fin n → Fin n) :
    (Finset.univ.filter fun p : HadamardPair n ↦ p.1.2 = σ p.1.1).card =
      (Finset.univ.filter fun i : Fin n ↦ i < σ i).card := by
  refine Finset.card_bij' (fun p _ ↦ p.1.1)
    (fun i hi ↦ ⟨(i, σ i), (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [← hp]
    exact p.2
  · intro i _
    simp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Subtype.ext (Prod.ext rfl hp.symm)
  · intro i _
    rfl

/-- [CGSS], Section 6, p. 326: each row `c ≠ 0` of the Sylvester matrix of order
`n = 2 ^ s` is the product of exactly `½n` pairs of rows, the pairs `{i, i ^^^ c}`. -/
theorem two_mul_card_filter_hadamardRowProduct_sylvester (s : ℕ) {c : Fin (2 ^ s)}
    (hc : c ≠ 0) :
    2 * (Finset.univ.filter fun p : HadamardPair (2 ^ s) ↦
      (sylvester s).hadamardRowProduct p.1.1 p.1.2 = sylvesterRow s c).card = 2 ^ s := by
  have hfilter : (Finset.univ.filter fun p : HadamardPair (2 ^ s) ↦
      (sylvester s).hadamardRowProduct p.1.1 p.1.2 = sylvesterRow s c) =
      Finset.univ.filter fun p : HadamardPair (2 ^ s) ↦ p.1.2 = p.1.1 ^^^ c := by
    refine Finset.filter_congr fun p _ ↦ ?_
    rw [hadamardRowProduct_sylvester, (sylvesterRow_injective s).eq_iff]
    exact fin_xor_eq_iff _ _ _
  rw [hfilter, card_filter_hadamardPair_eq (· ^^^ c)]
  refine two_mul_card_filter_lt_of_involutive _ (fun i ↦ fin_xor_xor_cancel_right i c)
    fun i h ↦ hc ?_
  have h' := fin_xor_xor_cancel_left i c
  rw [h, (fin_xor_eq_zero_iff i i).mpr rfl] at h'
  exact h'.symm

/-- [CGSS], Section 6, p. 326: every row of `P` for the Sylvester matrix is a row `c ≠ 0` of
the Sylvester matrix, namely `c = i ^^^ j` for the pair of rows `{i, j}`. -/
theorem exists_hadamardRowProduct_sylvester_eq (s : ℕ) (p : HadamardPair (2 ^ s)) :
    ∃ c ≠ 0, (sylvester s).hadamardRowProduct p.1.1 p.1.2 = sylvesterRow s c :=
  ⟨p.1.1 ^^^ p.1.2, fun h ↦ p.2.ne ((fin_xor_eq_zero_iff _ _).mp h),
    hadamardRowProduct_sylvester s _ _⟩

/-- [CGSS], Section 6, p. 326: the rows of `P` for the Sylvester matrix of order
`n = 2 ^ s` are the rows `c ≠ 0` of the Sylvester matrix, that is, all rows but the all-ones
row `0`. -/
theorem image_hadamardRowProduct_sylvester (s : ℕ) :
    (Finset.univ.image fun p : HadamardPair (2 ^ s) ↦
      (sylvester s).hadamardRowProduct p.1.1 p.1.2) =
      (Finset.univ.erase 0).image (sylvesterRow s) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, and_true]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.1 ^^^ p.1.2, fun h ↦ p.2.ne ((fin_xor_eq_zero_iff _ _).mp h),
      (hadamardRowProduct_sylvester s _ _).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨(0, c), Fin.pos_iff_ne_zero.mpr hc⟩,
      by rw [hadamardRowProduct_sylvester, fin_zero_xor]⟩

/-- [CGSS], Section 6, p. 326: the `½n(n − 1)` rows of `P` for the Sylvester matrix of
order `n = 2 ^ s` are `n − 1` distinct vectors. -/
theorem card_image_hadamardRowProduct_sylvester (s : ℕ) :
    (Finset.univ.image fun p : HadamardPair (2 ^ s) ↦
      (sylvester s).hadamardRowProduct p.1.1 p.1.2).card = 2 ^ s - 1 := by
  rw [image_hadamardRowProduct_sylvester, Finset.card_image_of_injective _
    (sylvesterRow_injective s), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]

/-- [CGSS], Section 6, p. 326: distinct rows of `P` for the Sylvester matrix are
orthogonal. -/
theorem inner_hadamardRowProduct_sylvester_of_ne (s : ℕ) (p q : HadamardPair (2 ^ s))
    (hpq : (sylvester s).hadamardRowProduct p.1.1 p.1.2 ≠
      (sylvester s).hadamardRowProduct q.1.1 q.1.2) :
    ⟪(sylvester s).hadamardRowProduct p.1.1 p.1.2,
      (sylvester s).hadamardRowProduct q.1.1 q.1.2⟫ = 0 := by
  rw [hadamardRowProduct_sylvester, hadamardRowProduct_sylvester] at hpq ⊢
  rw [inner_sylvesterRow, ite_eq_right fun h ↦ hpq (by rw [h])]

/-- [CGSS], Section 6, p. 326: "The Sylvester case corresponds to `d = 1` and yields
`n − 1` mutually orthogonal lines, each line occurring `½n` times." For the Sylvester matrix of
order `n = 2 ^ s`, the lines `ℝ ∙ P_p` spanned by the `½n(n − 1)` rows of `P` (one for each pair
`p` of rows) are `n − 1` distinct lines; any two distinct ones are orthogonal; and each of them
is spanned by exactly `½n` rows of `P`. Here `d = n / x = 1`, since `x = n`
(`sylvester_fourRowAgreement`). -/
theorem sylvester_lines (s : ℕ) :
    (Set.range fun p : HadamardPair (2 ^ s) ↦
        ℝ ∙ (sylvester s).hadamardRowProduct p.1.1 p.1.2).ncard = 2 ^ s - 1 ∧
      (∀ p q : HadamardPair (2 ^ s),
        ℝ ∙ (sylvester s).hadamardRowProduct p.1.1 p.1.2 ≠
          ℝ ∙ (sylvester s).hadamardRowProduct q.1.1 q.1.2 →
        ℝ ∙ (sylvester s).hadamardRowProduct p.1.1 p.1.2 ⟂
          ℝ ∙ (sylvester s).hadamardRowProduct q.1.1 q.1.2) ∧
      ∀ p : HadamardPair (2 ^ s), 2 * (Finset.univ.filter fun q : HadamardPair (2 ^ s) ↦
        ℝ ∙ (sylvester s).hadamardRowProduct q.1.1 q.1.2 =
          ℝ ∙ (sylvester s).hadamardRowProduct p.1.1 p.1.2).card = 2 ^ s := by
  refine ⟨?_, ?_, ?_⟩
  · have hrange : (Set.range fun p : HadamardPair (2 ^ s) ↦
        ℝ ∙ (sylvester s).hadamardRowProduct p.1.1 p.1.2) =
        (fun c ↦ ℝ ∙ sylvesterRow s c) '' {c | c ≠ 0} := by
      ext L
      simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.1.1 ^^^ p.1.2, fun h ↦ p.2.ne ((fin_xor_eq_zero_iff _ _).mp h),
          by rw [hadamardRowProduct_sylvester]⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨(0, c), Fin.pos_iff_ne_zero.mpr hc⟩,
          by rw [hadamardRowProduct_sylvester, fin_zero_xor]⟩
    have hne : {c : Fin (2 ^ s) | c ≠ 0} = ↑(Finset.univ.erase (0 : Fin (2 ^ s))) := by
      ext
      simp
    rw [hrange, Set.ncard_image_of_injective _ (span_sylvesterRow_injective s), hne,
      Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  · intro p q hpq
    rw [Submodule.isOrtho_span]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact inner_hadamardRowProduct_sylvester_of_ne s p q fun h ↦ hpq (by rw [h])
  · intro p
    have hfilter : (Finset.univ.filter fun q : HadamardPair (2 ^ s) ↦
        ℝ ∙ (sylvester s).hadamardRowProduct q.1.1 q.1.2 =
          ℝ ∙ (sylvester s).hadamardRowProduct p.1.1 p.1.2) =
        Finset.univ.filter fun q : HadamardPair (2 ^ s) ↦
          (sylvester s).hadamardRowProduct q.1.1 q.1.2 = sylvesterRow s (p.1.1 ^^^ p.1.2) := by
      refine Finset.filter_congr fun q _ ↦ ?_
      rw [hadamardRowProduct_sylvester, hadamardRowProduct_sylvester,
        (sylvesterRow_injective s).eq_iff]
      exact (span_sylvesterRow_injective s).eq_iff
    rw [hfilter]
    exact two_mul_card_filter_hadamardRowProduct_sylvester s
      fun h ↦ p.2.ne ((fin_xor_eq_zero_iff _ _).mp h)

end Matrix

/-! ### The Sylvester matrices of computation C16 -/

namespace Computations.C16

open Matrix

/-- The order-2 matrix of computation C16 is the Sylvester matrix of order 2. -/
theorem h2_eq_sylvester : h2 = sylvester 1 := by
  have h : ∀ ij : Fin 2 × Fin 2, h2 ij.1 ij.2 = sylvester 1 ij.1 ij.2 := by
    decide +kernel
  ext i j
  exact h (i, j)

/-- The order-4 matrix of computation C16 is the Sylvester matrix of order 4. -/
theorem h4_eq_sylvester : h4 = sylvester 2 := by
  have h : ∀ ij : Fin 4 × Fin 4, h4 ij.1 ij.2 = sylvester 2 ij.1 ij.2 := by
    decide +kernel
  ext i j
  exact h (i, j)

/-- The order-8 matrix of computation C16 is the Sylvester matrix of order 8. -/
theorem h8_eq_sylvester : h8 = sylvester 3 := by
  have h : ∀ ij : Fin 8 × Fin 8, h8 ij.1 ij.2 = sylvester 3 ij.1 ij.2 := by
    decide +kernel
  ext i j
  exact h (i, j)

/-- The order-16 matrix of computation C16 is the Sylvester matrix of order 16. -/
theorem h16_eq_sylvester : h16 = sylvester 4 := by
  have h : ∀ ij : Fin 16 × Fin 16, h16 ij.1 ij.2 = sylvester 4 ij.1 ij.2 := by
    decide +kernel
  ext i j
  exact h (i, j)

end Computations.C16
