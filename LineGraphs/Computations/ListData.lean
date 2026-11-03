/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.Int.Basic

/-!
# ListData

The executable certificate format. There are no `Matrix`, `Finset`, or real-vector
operations in this module. Every public checker returns `Bool` and consumes list data. -/

namespace Computations

/-- Integer coordinates in the executable certificate format. -/
abbrev IntVector := List ℤ
/-- Integer matrices stored as row lists. -/
abbrev IntMatrix := List IntVector

/-- Truncated dot product. Equal lengths are required by the vector bridge. -/
def dot : IntVector → IntVector → ℤ
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- Coordinatewise sum. -/
def vectorAdd (v w : IntVector) : IntVector := List.zipWith (· + ·) v w

/-- Zero-padded lookup, used only after checking the intended dimensions. -/
def entry (A : IntMatrix) (i j : ℕ) : ℤ := (A[i]?.getD [])[j]?.getD 0

/-- Tabulation is executable, unlike `Matrix` arithmetic. -/
def tabulate (n : ℕ) (f : Fin n → Fin n → ℤ) : IntMatrix :=
  List.ofFn fun i => List.ofFn (f i)

/-- Dimensions are checked, so that no surplus data can silently be ignored. -/
def checkShape (n : ℕ) (A : IntMatrix) : Bool :=
  A.length == n && A.all (fun r => r.length == n)

/-- Entrywise addition, tabulated at the checked dimension. -/
def matrixAdd (n : ℕ) (A B : IntMatrix) : IntMatrix :=
  tabulate n fun i j => entry A i j + entry B i j

/-- The integer scalar multiple of the identity matrix. -/
def scalarMatrix (n : ℕ) (c : ℤ) : IntMatrix :=
  tabulate n fun i j => if i = j then c else 0

/-- Columns are materialized once; each dot product traverses two lists. -/
def matrixMul (n : ℕ) (A B : IntMatrix) : IntMatrix :=
  let cols := List.ofFn fun j : Fin n => List.ofFn fun k : Fin n => entry B k j
  List.ofFn fun i : Fin n =>
    let row := List.ofFn fun k : Fin n => entry A i k
    cols.map (dot row)

/-- Powers computed by repeated list matrix multiplication. -/
def matrixPow (n : ℕ) (A : IntMatrix) : ℕ → IntMatrix
  | 0 => scalarMatrix n 1
  | k + 1 => matrixMul n (matrixPow n A k) A

/-- The integer sum of the diagonal entries. -/
def trace (n : ℕ) (A : IntMatrix) : ℤ :=
  (List.ofFn fun i : Fin n => entry A i i).sum

/-- Evaluate ascending polynomial coefficients by Horner recursion. -/
def matrixEval (n : ℕ) (A : IntMatrix) : List ℤ → IntMatrix
  | [] => scalarMatrix n 0
  | c :: cs => matrixAdd n (scalarMatrix n c) (matrixMul n A (matrixEval n A cs))

/-- Check that every stored entry is zero. -/
def checkZero (A : IntMatrix) : Bool := A.all (fun r => r.all (· == 0))

/-- Check the matrix shape and the vanishing of a polynomial. -/
def checkPolynomial (n : ℕ) (A : IntMatrix) (cs : List ℤ) : Bool :=
  checkShape n A && checkZero (matrixEval n A cs)

/-- Explicit `(exponent, trace)` pairs; include exponent zero when the order matters. -/
def checkTraces (n : ℕ) (A : IntMatrix) (ts : List (ℕ × ℤ)) : Bool :=
  checkShape n A && ts.all (fun t => trace n (matrixPow n A t.1) == t.2)

/-- A row checker can be evaluated in a separate lemma to limit kernel memory. -/
def checkDotsRow (allowed : List ℤ) (vs : List IntVector) (v : IntVector) : Bool :=
  vs.all (fun w => allowed.contains (dot v w))

/-- Check the common dimension and every prescribed dot-product bound. -/
def checkDots (n : ℕ) (allowed : List ℤ) (vs : List IntVector) : Bool :=
  vs.all (fun v => v.length == n) && vs.all (checkDotsRow allowed vs)

/-- Prescribed Gram matrix, including every diagonal entry and all dimensions. -/
def checkGram (d : ℕ) (vs : List IntVector) (G : IntMatrix) : Bool :=
  vs.all (fun v => v.length == d) && checkShape vs.length G &&
    (List.range vs.length).all (fun i => (List.range vs.length).all (fun j =>
      dot (vs[i]?.getD []) (vs[j]?.getD []) == entry G i j))

/-- The membership predicate must have its own soundness lemma. This avoids a linear scan
through the root list at every star. `target = -scale²` in doubled integer coordinates. -/
def checkStarRow (target : ℤ) (mem : IntVector → Bool)
    (vs : List IntVector) (v : IntVector) : Bool :=
  vs.all (fun w => if dot v w == target then mem (vectorAdd v w) else true)

/-- Check the common dimension and membership of every required star sum. -/
def checkStar (n : ℕ) (target : ℤ) (mem : IntVector → Bool) (vs : List IntVector) : Bool :=
  vs.all (fun v => v.length == n) && vs.all (checkStarRow target mem vs)

/-- Exhaustive bounded search. The domain is explicit, allowing tuples and pruned domains. -/
def checkNoSolution {α : Type*} (domain : List α) (test : α → Bool) : Bool :=
  domain.all (fun x => !test x)

/-- Stream a half-open parameter box, without materializing its Cartesian product. -/
def allBox : List ℕ → (List ℕ → Bool) → Bool
  | [], p => p []
  | b :: bs, p => (List.range b).all fun x => allBox bs (fun xs => p (x :: xs))

/-- Bijection certificate: bounded images and pairwise distinctness, all on lists. -/
def checkPermutation (n : ℕ) (p : List ℕ) : Bool :=
  p.length == n &&
  (List.range n).all (fun i => decide (p[i]?.getD n < n)) &&
  (List.range n).all (fun i => (List.range n).all (fun j =>
    i == j || !(p[i]?.getD n == p[j]?.getD n)))

/-- The same checker works for integer adjacency and Seidel matrices. -/
def checkGraphIso (n : ℕ) (A B : IntMatrix) (p : List ℕ) : Bool :=
  checkShape n A && checkShape n B && checkPermutation n p &&
  (List.range n).all (fun i => (List.range n).all (fun j =>
    entry A i j == entry B (p[i]?.getD n) (p[j]?.getD n)))


end Computations
