/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.ResolutionSpectrum

/-!
# Example 5.13 as the third case of Theorem 5.8

The explicit substitution in step `s5exspec58` of Example 5.13 (`ex:5.13`)
of [CGSS]: `s = 2k - 1`, `t = k - 1`, and the square-root parameter is `k`.
-/

namespace Design

-- Example 5.13
/-- The resolution family's design parameters satisfy `NonbipartiteParameters` with
`s = 2k - 1`, `t = k - 1` and the required parity: step `s5exspec58`, Example 5.13 of [CGSS]. -/
theorem nonbipartiteParameters_and_even_resolution_family {k : ℕ} (hk : 2 ≤ k) :
    NonbipartiteParameters (k * (2 * k - 1)) ((k - 1) * (2 * k - 1))
      (k * (2 * k + 1)) ((k - 1) * (2 * k + 1)) (k * (2 * k - 3))
      (2 * k - 1) (k - 1) ∧ Even ((k - 1) * ((2 * k - 1) + 1)) := by
  have h₁ : 1 ≤ k := by omega
  have h₂ : 1 ≤ 2 * k := by omega
  have h₃ : 3 ≤ 2 * k := by omega
  constructor
  · constructor
    · omega
    · omega
    · zify [h₂]; ring
    · exact Nat.mul_comm _ _
    · zify [h₂]; ring
    · zify [h₁, h₂]; ring
    · push_cast [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃]
      ring
    · omega
    · refine ⟨(k : ℤ) - 2, ?_⟩
      push_cast [Nat.cast_sub h₁, Nat.cast_sub h₂]
      ring
  · refine ⟨k * (k - 1), ?_⟩
    zify [h₁, h₂]
    ring

namespace Resolution

attribute [local instance] Classical.propDecidable

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {k : ℕ} {D : Design P B (k * (2 * k - 1)) k (4 * k ^ 2 - 1) (2 * k + 1) 1}
  (R : D.Resolution (2 * k + 1))

-- Example 5.13
/-- The spectrum is exactly that of Theorem 5.8(iii), step `s5exspec58` of
Example 5.13 (`ex:5.13`) of [CGSS]. -/
theorem spectrumMultiset_graph_nonbipartite_form :
    let s := 2 * k - 1
    let t := k - 1
    R.graph.spectrumMultiset =
      {((s : ℝ) + 1) * t} + Multiset.replicate (s + 1) (-(t : ℝ)) +
      Multiset.replicate ((s - 1) * (s + 2) / 2)
        (Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) +
      Multiset.replicate ((s - 1) * (s + 2) / 2)
        (-Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) := by
  dsimp only
  have hk := D.one_lt_k
  have h₁ : 1 ≤ k := by omega
  have h₂ : 1 ≤ 2 * k := by omega
  have hs : 1 ≤ 2 * k - 1 := by omega
  have hcount : (2 * k - 1 - 1) * (2 * k - 1 + 2) =
      2 * ((k - 1) * (2 * k + 1)) := by
    zify [h₁, h₂, hs]
    ring
  have hmult : (2 * k - 1 - 1) * (2 * k - 1 + 2) / 2 =
      (k - 1) * (2 * k + 1) := by omega
  have hroot : Real.sqrt
      (((k : ℝ) - 1) * (2 * k - 1 + 1) * (2 * k - 1 - (k - 1)) /
        (2 * k - 1 - 1)) = k := by
    have he : ((k : ℝ) - 1) * (2 * k - 1 + 1) * (2 * k - 1 - (k - 1)) /
        (2 * k - 1 - 1) = (k : ℝ) ^ 2 := by
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
      field_simp (disch := nlinarith)
      ring
    rw [he, Real.sqrt_sq (Nat.cast_nonneg k)]
  rw [hmult, show 2 * k - 1 + 1 = 2 * k by omega]
  simp only [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  have hroot' : Real.sqrt
      (((k : ℝ) - 1) * (2 * k - 1 + 1) * (2 * k - 1 - (k - 1)) /
        (2 * k - 1 - 1)) = k := hroot
  rw [hroot', R.spectrumMultiset_graph]
  rw [show (2 * (k : ℝ) - 1 + 1) * (k - 1) = 2 * k * (k - 1) by ring]

end Resolution
end Design
