/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.ListData
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
# List certificates for the computations of [CGSS]

The executable layer uses lists and integers only. Missing entries are interpreted as zero;
`checkShape` rejects malformed certificates at the public matrix-checker boundary.
Polynomial coefficients are in increasing order, including the constant coefficient.
-/

namespace Computations

/-- Interpretation in any ring, in particular `ℤ` and `ℝ`. -/
def toMatrix {R : Type*} [Ring R] (n : ℕ) (A : IntMatrix) :
    Matrix (Fin n) (Fin n) R := fun i j => (entry A i j : R)

/-- The polynomial with the supplied integer coefficients in ascending degree. -/
noncomputable def polynomialOfCoeffs (cs : List ℤ) : Polynomial ℤ :=
  match cs with
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * polynomialOfCoeffs cs

theorem dot_ofFn {n : ℕ} (v w : Fin n → ℤ) :
    dot (List.ofFn v) (List.ofFn w) = v ⬝ᵥ w := by
  change _ = ∑ i, v i * w i
  induction n with
  | zero => simp [dot]
  | succ n ih => rw [List.ofFn_succ, List.ofFn_succ, dot, ih, Fin.sum_univ_succ]

theorem dot_eq_sum {n : ℕ} {v w : IntVector} (hv : v.length = n) (hw : w.length = n) :
    dot v w = ∑ i : Fin n, v[i.val] * w[i.val] := by
  have ev : (List.ofFn fun i : Fin n => v[i.val]) = v := by
    apply List.ext_getElem <;> simp [hv]
  have ew : (List.ofFn fun i : Fin n => w[i.val]) = w := by
    apply List.ext_getElem <;> simp [hw]
  simpa only [ev, ew, dotProduct] using (dot_ofFn (fun i : Fin n => v[i.val]) (fun i => w[i.val]))

@[simp] theorem toMatrix_tabulate {R : Type*} [Ring R] (n : ℕ) (f : Fin n → Fin n → ℤ) :
    toMatrix (R := R) n (tabulate n f) = fun i j => (f i j : R) := by
  ext i j
  simp [toMatrix, tabulate, entry]

@[simp] theorem toMatrix_add {R : Type*} [Ring R] (n : ℕ) (A B : IntMatrix) :
    toMatrix (R := R) n (matrixAdd n A B) = toMatrix n A + toMatrix n B := by
  unfold matrixAdd
  rw [toMatrix_tabulate]
  ext i j
  simp [toMatrix]

@[simp] theorem toMatrix_scalar {R : Type*} [Ring R] (n : ℕ) (c : ℤ) :
    toMatrix (R := R) n (scalarMatrix n c) = (c : R) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  simp [scalarMatrix, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

@[simp] theorem toMatrix_mul {R : Type*} [Ring R] (n : ℕ) (A B : IntMatrix) :
    toMatrix (R := R) n (matrixMul n A B) = toMatrix n A * toMatrix n B := by
  ext i j
  simp [matrixMul, toMatrix, entry, List.map_ofFn, dot_ofFn, dotProduct, Matrix.mul_apply,
    Int.cast_sum, Int.cast_mul]

@[simp] theorem toMatrix_pow {R : Type*} [Ring R] (n : ℕ) (A : IntMatrix) (k : ℕ) :
    toMatrix (R := R) n (matrixPow n A k) = toMatrix n A ^ k := by
  induction k with
  | zero => simp [matrixPow]
  | succ k ih => simp [matrixPow, ih, pow_succ]

theorem trace_eq {R : Type*} [Ring R] (n : ℕ) (A : IntMatrix) :
    (trace n A : R) = Matrix.trace (toMatrix n A : Matrix (Fin n) (Fin n) R) := by
  simp [trace, Matrix.trace, toMatrix, List.sum_ofFn, Int.cast_sum]

@[simp] theorem toMatrix_eval {R : Type*} [CommRing R] (n : ℕ) (A : IntMatrix) (cs : List ℤ) :
    toMatrix (R := R) n (matrixEval n A cs) =
      Polynomial.aeval (toMatrix (R := R) n A) (polynomialOfCoeffs cs) := by
  induction cs with
  | nil => simp [matrixEval, polynomialOfCoeffs]
  | cons c cs ih =>
    simp only [matrixEval, toMatrix_add, toMatrix_scalar, toMatrix_mul, ih,
      polynomialOfCoeffs, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.intCast_apply, h]


theorem checkShape_sound {n : ℕ} {A : IntMatrix} (h : checkShape n A = true) :
    A.length = n ∧ ∀ r ∈ A, r.length = n := by
  simpa [checkShape] using h

theorem checkZero_sound {A : IntMatrix} (h : checkZero A = true) (n : ℕ) :
    toMatrix (R := ℤ) n A = 0 := by
  have hz : ∀ r ∈ A, ∀ x ∈ r, x = 0 := by simpa [checkZero] using h
  ext i j
  simp only [toMatrix, Int.cast_id, entry, Matrix.zero_apply]
  cases hr : A[i.val]? with
  | none => simp
  | some r =>
    have hm := List.mem_of_getElem? hr
    cases hx : r[j.val]? with
    | none => simp [hx]
    | some x => simpa [hx] using hz r hm x (List.mem_of_getElem? hx)

theorem checkPolynomial_sound {n : ℕ} {A : IntMatrix} {cs : List ℤ}
    (h : checkPolynomial n A cs = true) :
    Polynomial.aeval (toMatrix (R := ℤ) n A) (polynomialOfCoeffs cs) = 0 := by
  rw [← toMatrix_eval]
  exact checkZero_sound (Bool.and_eq_true_iff.mp h).2 n

theorem checkTraces_sound {R : Type*} [Ring R] {n : ℕ} {A : IntMatrix}
    {ts : List (ℕ × ℤ)} (h : checkTraces n A ts = true) {k : ℕ} {t : ℤ}
    (ht : (k, t) ∈ ts) : Matrix.trace (toMatrix (R := R) n A ^ k) = (t : R) := by
  have he : trace n (matrixPow n A k) = t := by
    simpa using (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) (k, t) ht
  rw [← toMatrix_pow, ← trace_eq, he]

theorem checkDotsRow_sound {allowed : List ℤ} {vs : List IntVector} {v w : IntVector}
    (h : checkDotsRow allowed vs v = true) (hw : w ∈ vs) : dot v w ∈ allowed := by
  simpa using List.all_eq_true.mp h w hw

theorem checkDots_sound {n : ℕ} {allowed : List ℤ} {vs : List IntVector}
    (h : checkDots n allowed vs = true) {v w : IntVector} (hv : v ∈ vs) (hw : w ∈ vs) :
    dot v w ∈ allowed :=
  checkDotsRow_sound (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 v hv) hw

theorem checkStarRow_sound {target : ℤ} {mem : IntVector → Bool} {vs : List IntVector}
    {v w : IntVector} (h : checkStarRow target mem vs v = true) (hw : w ∈ vs)
    (hd : dot v w = target) : mem (vectorAdd v w) = true := by
  have := List.all_eq_true.mp h w hw
  simpa [hd] using this

theorem checkStar_sound {n : ℕ} {target : ℤ} {mem : IntVector → Bool} {vs : List IntVector}
    (h : checkStar n target mem vs = true) {v w : IntVector} (hv : v ∈ vs) (hw : w ∈ vs)
    (hd : dot v w = target) : mem (vectorAdd v w) = true :=
  checkStarRow_sound (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 v hv) hw hd

theorem checkNoSolution_sound {α : Type*} {domain : List α} {test : α → Bool}
    (h : checkNoSolution domain test = true) {x : α} (hx : x ∈ domain) : test x = false := by
  simpa using List.all_eq_true.mp h x hx

theorem checkNoSolution_complete_domain {α : Type*} {P : α → Prop}
    {domain : List α} {test : α → Bool} (h : checkNoSolution domain test = true)
    (complete : ∀ x, P x → x ∈ domain) (reflect : ∀ x, P x → test x = true) : ¬ ∃ x, P x := by
  rintro ⟨x, hx⟩
  have := checkNoSolution_sound h (complete x hx)
  simp [reflect x hx] at this

theorem checkPolynomial_sound_real {n : ℕ} {A : IntMatrix} {cs : List ℤ}
    (h : checkPolynomial n A cs = true) :
    Polynomial.aeval (toMatrix (R := ℝ) n A) (polynomialOfCoeffs cs) = 0 := by
  rw [← toMatrix_eval]
  have hz := checkZero_sound (Bool.and_eq_true_iff.mp h).2 n
  ext i j
  have hij := congrFun (congrFun hz i) j
  change (entry (matrixEval n A cs) i j : ℝ) = 0
  change entry (matrixEval n A cs) i j = 0 at hij
  simp [hij]

theorem checkGram_sound {d : ℕ} {vs : List IntVector} {G : IntMatrix}
    (h : checkGram d vs G = true) (i j : Fin vs.length) :
    dot vs[i.val] vs[j.val] = toMatrix (R := ℤ) vs.length G i j := by
  have hh := (Bool.and_eq_true_iff.mp h).2
  have hi := List.all_eq_true.mp hh i.val (List.mem_range.mpr i.isLt)
  have hij := List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt)
  simpa [toMatrix, i.isLt, j.isLt] using hij

theorem checkGram_lengths {d : ℕ} {vs : List IntVector} {G : IntMatrix}
    (h : checkGram d vs G = true) {v : IntVector} (hv : v ∈ vs) : v.length = d := by
  simpa using List.all_eq_true.mp (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp h).1).1 v hv

/-- A successful dot certificate includes the common vector dimension. -/
theorem checkDots_lengths {n : ℕ} {allowed : List ℤ} {vs : List IntVector}
    (h : checkDots n allowed vs = true) {v : IntVector} (hv : v ∈ vs) : v.length = n := by
  simpa using List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 v hv

/-- A successful star certificate includes the common vector dimension. -/
theorem checkStar_lengths {n : ℕ} {target : ℤ} {mem : IntVector → Bool}
    {vs : List IntVector} (h : checkStar n target mem vs = true)
    {v : IntVector} (hv : v ∈ vs) : v.length = n := by
  simpa using List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 v hv

/-- The streaming box visits exactly the tuples with the prescribed strict bounds. -/
theorem allBox_eq_true (bounds : List ℕ) (p : List ℕ → Bool) :
    allBox bounds p = true ↔ ∀ xs, List.Forall₂ (· < ·) xs bounds → p xs = true := by
  induction bounds generalizing p with
  | nil => simp [allBox]
  | cons b bs ih =>
    simp only [allBox, List.all_eq_true, List.mem_range, ih]
    constructor
    · intro h xs hx
      cases hx with
      | cons hx hxs => exact h _ hx _ hxs
    · intro h x hx xs hxs
      exact h _ (.cons hx hxs)

/-- Combine independently checked chunks, without unfolding their elements in the proof. -/
theorem all_eq_true_of_chunks {α : Type*} {xs : List α} {m : ℕ}
    {chunk : ℕ → List α} {p : α → Bool}
    (he : xs = (List.range m).flatMap chunk)
    (h : ∀ k ∈ List.range m, (chunk k).all p = true) : xs.all p = true := by
  rw [he, List.all_flatMap]
  exact List.all_eq_true.mpr h

theorem checkPermutation_sound {n : ℕ} {p : List ℕ} (h : checkPermutation n p = true) :
    ∃ e : Fin n ≃ Fin n, ∀ i, (e i).val = p[i.val]?.getD n := by
  obtain ⟨⟨_, hb⟩, hd⟩ := Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp
  have hb' (i : Fin n) : p[i.val]?.getD n < n := by
    simpa using List.all_eq_true.mp hb i.val (List.mem_range.mpr i.isLt)
  let f : Fin n → Fin n := fun i => ⟨_, hb' i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he := List.all_eq_true.mp (List.all_eq_true.mp hd i.val
      (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt)
    have hv : p[i.val]?.getD n = p[j.val]?.getD n := congrArg Fin.val hij
    have : i.val = j.val := by simpa [hv] using he
    exact Fin.ext this
  exact ⟨Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩, fun _ => rfl⟩

/-- Soundness as a simultaneous permutation of rows and columns. -/
theorem checkGraphIso_sound {n : ℕ} {A B : IntMatrix} {p : List ℕ}
    (h : checkGraphIso n A B p = true) :
    ∃ e : Fin n ≃ Fin n, (∀ i, (e i).val = p[i.val]?.getD n) ∧
      ∀ i j, toMatrix (R := ℤ) n A i j = toMatrix (R := ℤ) n B (e i) (e j) := by
  obtain ⟨hp, he⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨e, heq⟩ := checkPermutation_sound (Bool.and_eq_true_iff.mp hp).2
  refine ⟨e, heq, fun i j => ?_⟩
  have hij := List.all_eq_true.mp (List.all_eq_true.mp he i.val
    (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt)
  simpa [toMatrix, heq] using hij

/-- Transfer to existing `SimpleGraph`s, with their adjacency-matrix identifications explicit. -/
theorem nonempty_iso_of_checkGraphIso {n : ℕ} {A B : IntMatrix} {p : List ℕ}
    (G H : SimpleGraph (Fin n))
    (hG : ∀ i j, G.Adj i j ↔ entry A i j = 1)
    (hH : ∀ i j, H.Adj i j ↔ entry B i j = 1)
    (h : checkGraphIso n A B p = true) : Nonempty (G ≃g H) := by
  obtain ⟨e, _, he⟩ := checkGraphIso_sound h
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro i j
  rw [hH, hG]
  exact congrArg (· = 1) (he i j) |>.symm |> Iff.of_eq

/-- Bounded searches need both the box bounds and a reflection of the mathematical predicate. -/
theorem no_bounded_solution_of_check {bounds : List ℕ} {test : List ℕ → Bool}
    {P : List ℕ → Prop} (h : allBox bounds (fun xs => !test xs) = true)
    (reflect : ∀ xs, List.Forall₂ (· < ·) xs bounds → P xs → test xs = true) :
    ¬ ∃ xs, List.Forall₂ (· < ·) xs bounds ∧ P xs := by
  rintro ⟨xs, hb, hp⟩
  have he := (allBox_eq_true bounds _).mp h xs hb
  rw [reflect xs hb hp] at he
  contradiction

end Computations
