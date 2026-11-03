/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.BoundedSearch

/-!
# C18: the fifteen strongly regular parameter tuples

Computation C18 of the blueprint for Remark 4.14 of [CGSS]. The pruned Boolean
search visits `1 ≤ k ≤ 16`, `0 ≤ a < k`, and `1 ≤ c ≤ k`; the parameter
equation determines `n`. It then checks all nine possible ranks. The
soundness theorem uses exactly the integer bounds of `comp:C18`.
-/

namespace Computations.C18

/-- The fifteen tuples of Computation C18, Remark 4.14 of [CGSS], in the
blueprint's order. The first six are the cocktail party parameters for `2 ≤ m ≤ 7`. -/
def parameters : List (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [(4, 2, 0, 2, 3), (6, 4, 2, 4, 4), (8, 6, 4, 6, 5),
   (10, 8, 6, 8, 6), (12, 10, 8, 10, 7), (14, 12, 10, 12, 8),
   (9, 4, 1, 2, 5), (10, 6, 3, 4, 5), (10, 3, 0, 1, 6),
   (15, 8, 4, 4, 6), (16, 10, 6, 6, 6), (16, 6, 2, 2, 7),
   (21, 10, 5, 4, 7), (27, 16, 10, 8, 7), (28, 12, 6, 4, 8)]

/-- The Boolean search for C18, Remark 4.14 of [CGSS]. The nonedge bound is
essential: it excludes the otherwise surviving tuple `(21,16,12,12,7)`. -/
def checkParameters : Bool :=
  allSRGParameters 37 1 16 fun n k a c ↦
    (List.range 9).all fun ρ ↦ decide
      (((k : ℤ) - 2 * a + c = 4 ∧ 2 * (k : ℤ) - c ≤ n - 2 ∧
        ((a : ℤ) - c + 4) * ((ρ : ℤ) - 1) = 2 * n - k - 2) →
        ((n : ℤ), (k : ℤ), (a : ℤ), (c : ℤ), (ρ : ℤ)) ∈ parameters)

/-- Soundness of the Boolean search for C18, Remark 4.14 of [CGSS], over
the blueprint's integer ranges. No graph or spectral assumptions are implicit. -/
theorem checkParameters_sound (hcheck : checkParameters = true) {n k a c ρ : ℤ}
    (hk : 1 ≤ k) (hkn : k ≤ n - 2) (hn : n ≤ 36) (hk16 : k ≤ 16)
    (ha : 0 ≤ a) (hak : a ≤ k - 1) (hc : 1 ≤ c) (hck : c ≤ k)
    (hρ : 0 ≤ ρ) (hρ8 : ρ ≤ 8)
    (hparam : k * (k - a - 1) = c * (n - k - 1))
    (hlin : k - 2 * a + c = 4) (hbound : 2 * k - c ≤ n - 2)
    (hrank : (a - c + 4) * (ρ - 1) = 2 * n - k - 2) :
    (n, k, a, c, ρ) ∈ parameters := by
  lift n to ℕ using (show 0 ≤ n by omega)
  lift k to ℕ using (show 0 ≤ k by omega)
  lift a to ℕ using ha
  lift c to ℕ using (show 0 ≤ c by omega)
  lift ρ to ℕ using hρ
  have he : k * (k - a - 1) = (n - k - 1) * c := by
    have hka : a ≤ k := by omega
    have hka1 : 1 ≤ k - a := by omega
    have hnk : k ≤ n := by omega
    have hnk1 : 1 ≤ n - k := by omega
    zify [hka, hka1, hnk, hnk1]
    nlinarith only [hparam]
  have ht := allSRGParameters_sound (p := fun n k a c ↦
      (List.range 9).all fun ρ ↦ decide
        (((k : ℤ) - 2 * a + c = 4 ∧ 2 * (k : ℤ) - c ≤ n - 2 ∧
          ((a : ℤ) - c + 4) * ((ρ : ℤ) - 1) = 2 * n - k - 2) →
          ((n : ℤ), (k : ℤ), (a : ℤ), (c : ℤ), (ρ : ℤ)) ∈ parameters))
    hcheck (show n < 37 by omega)
    (show k ∈ List.range' 1 16 by simp only [List.mem_range'_1]; omega)
    (show a < k by omega) (show 0 < c by omega) (show c ≤ k by omega)
    (show k + 1 ≤ n by omega) he
  have htρ := List.all_eq_true.mp ht ρ (List.mem_range.mpr (by omega))
  exact of_decide_eq_true htρ ⟨hlin, hbound, hrank⟩

set_option maxRecDepth 100000 in
/-- Kernel verification of the Boolean search for C18, Remark 4.14 of [CGSS]. -/
theorem checkParameters_eq_true : checkParameters = true := by decide +kernel

-- Computation C18
/-- Computation C18, Remark 4.14 of [CGSS]: every solution is one of the fifteen listed
tuples, under the stated bounds and four arithmetic conditions (`comp:C18`). -/
theorem srg_parameters {n k a c ρ : ℤ}
    (hk : 1 ≤ k) (hkn : k ≤ n - 2) (hn : n ≤ 36) (hk16 : k ≤ 16)
    (ha : 0 ≤ a) (hak : a ≤ k - 1) (hc : 1 ≤ c) (hck : c ≤ k)
    (hρ : 0 ≤ ρ) (hρ8 : ρ ≤ 8)
    (hparam : k * (k - a - 1) = c * (n - k - 1))
    (hlin : k - 2 * a + c = 4) (hbound : 2 * k - c ≤ n - 2)
    (hrank : (a - c + 4) * (ρ - 1) = 2 * n - k - 2) :
    (n, k, a, c, ρ) ∈ parameters :=
  checkParameters_sound checkParameters_eq_true hk hkn hn hk16 ha hak hc hck hρ hρ8
    hparam hlin hbound hrank

end Computations.C18
