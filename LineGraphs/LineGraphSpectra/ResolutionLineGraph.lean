/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.ResolutionSpectrum
import LineGraphs.LineGraphSpectra.DesignSignless

/-!
# The cospectral mate in Example 5.13

Example 5.13 (`ex:5.13`) of [CGSS], steps `s5exCH`–`s5exline`.
The incidence graph has exactly one extra zero in its signless spectrum.
Handshaking supplies equal edge counts before transferring to the line graphs.
-/

open Matrix
open scoped BigOperators

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {k : ℕ}

-- Example 5.13
/-- The incidence graph's signless spectrum for the resolution family's design parameters:
the substitution in `s5exC1`, Example 5.13 of [CGSS]. -/
theorem spectrumMultiset_signlessLapMatrix_incidenceGraph_resolution_family (hk : 2 ≤ k)
    (D : Design P B (k * (2 * k - 1)) ((k - 1) * (2 * k - 1)) (k * (2 * k + 1))
      ((k - 1) * (2 * k + 1)) (k * (2 * k - 3))) :
    (D.incidenceGraph.signlessLapMatrix ℝ).spectrumMultiset =
      {0} + {4 * (k : ℝ) * (k - 1)} +
      Multiset.replicate (2 * k) (2 * (k : ℝ) * (k - 1) - k + 1) +
      Multiset.replicate ((k - 1) * (2 * k + 1)) (2 * (k : ℝ) * (k - 1) + k) +
      Multiset.replicate ((k - 1) * (2 * k + 1)) (2 * (k : ℝ) * (k - 1) - k) := by
  have hk1 : 1 ≤ k := by omega
  have htwo : 1 ≤ 2 * k := by omega
  have hthree : 3 ≤ 2 * k := by omega
  have hprod : 1 ≤ k * (2 * k - 1) := by
    have hsmall : 1 ≤ 2 * k - 1 := by omega
    exact Nat.mul_pos hk1 hsmall
  have hl : k * (2 * k - 3) < (k - 1) * (2 * k + 1) := by
    zify [hk1, hthree]
    nlinarith
  have hrk : (k - 1) * (2 * k + 1) ≠ (k - 1) * (2 * k - 1) := by
    zify [hk1, htwo]
    nlinarith
  have hv : k * (2 * k - 1) - 1 = (k - 1) * (2 * k + 1) := by
    zify [hk1, htwo, hprod]
    ring
  have hb : k * (2 * k + 1) - k * (2 * k - 1) = 2 * k := by
    have hle : k * (2 * k - 1) ≤ k * (2 * k + 1) := Nat.mul_le_mul_left k (by omega)
    zify [htwo, hle]
    ring
  have hsqrt : Real.sqrt
      ((((k : ℝ) - 1) * (2 * k + 1) - (k - 1) * (2 * k - 1)) ^ 2 +
        4 * ((k - 1) * (2 * k + 1) - k * (2 * k - 3))) = 2 * k := by
    rw [show (((k : ℝ) - 1) * (2 * k + 1) - (k - 1) * (2 * k - 1)) ^ 2 +
        4 * ((k - 1) * (2 * k + 1) - k * (2 * k - 3)) = (2 * k) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [D.spectrumMultiset_signlessLapMatrix_incidenceGraph hl hrk, hv, hb]
  simp only [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_sub htwo, Nat.cast_sub hthree,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, hsqrt]
  have htop : ((k : ℝ) - 1) * (2 * k + 1) + (k - 1) * (2 * k - 1) =
      4 * k * (k - 1) := by ring
  have hplus : (((k : ℝ) - 1) * (2 * k + 1) + (k - 1) * (2 * k - 1) + 2 * k) / 2 =
      2 * k * (k - 1) + k := by ring
  have hminus : (((k : ℝ) - 1) * (2 * k + 1) + (k - 1) * (2 * k - 1) - 2 * k) / 2 =
      2 * k * (k - 1) - k := by ring
  have hlast : ((k : ℝ) - 1) * (2 * k - 1) = 2 * k * (k - 1) - k + 1 := by ring
  rw [hplus, hminus, htop, hlast]
  abel

namespace Resolution

variable {D : Design P B (k * (2 * k - 1)) k (4 * k ^ 2 - 1) (2 * k + 1) 1}
  (R : D.Resolution (2 * k + 1))

/-- The shifted spectrum in `s5exCH`, Example 5.13 of [CGSS]. -/
theorem spectrumMultiset_signlessLapMatrix_graph :
    (R.graph.signlessLapMatrix ℝ).spectrumMultiset =
      {4 * (k : ℝ) * (k - 1)} +
      Multiset.replicate (2 * k) (2 * (k : ℝ) * (k - 1) - k + 1) +
      Multiset.replicate ((k - 1) * (2 * k + 1)) (2 * (k : ℝ) * (k - 1) + k) +
      Multiset.replicate ((k - 1) * (2 * k + 1)) (2 * (k : ℝ) * (k - 1) - k) := by
  rw [R.graph_isRegularOfDegree.spectrumMultiset_signlessLapMatrix, R.spectrumMultiset_graph]
  have hk1 : 1 ≤ k := by have := D.one_lt_k; omega
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_replicate,
    Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_ofNat, Nat.cast_one]
  rw [show 2 * (k : ℝ) * (k - 1) + 2 * k * (k - 1) = 4 * k * (k - 1) by ring,
    show 2 * (k : ℝ) * (k - 1) + -(k - 1) = 2 * k * (k - 1) - k + 1 by ring]
  simp only [sub_eq_add_neg]

/-- Positivity of every signless eigenvalue in `s5exCH`, Example 5.13 of [CGSS]. -/
theorem signless_spectrum_pos {μ : ℝ}
    (hμ : μ ∈ (R.graph.signlessLapMatrix ℝ).spectrumMultiset) : 0 < μ := by
  rw [R.spectrumMultiset_signlessLapMatrix_graph] at hμ
  simp only [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate, or_assoc] at hμ
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast D.one_lt_k
  rcases hμ with hμ | ⟨_, hμ⟩ | ⟨_, hμ⟩ | ⟨_, hμ⟩ <;> rw [hμ] <;> nlinarith

/-- The edge count in `s5exedges`, Example 5.13 of [CGSS]. -/
theorem card_edges_graph :
    R.graph.edgeFinset.card = (k * (2 * k - 1)) * ((k - 1) * (2 * k + 1)) := by
  have he := R.graph.sum_degrees_eq_twice_card_edges
  simp only [R.graph_isRegularOfDegree.degree_eq, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, D.card_blocks] at he
  have hk := D.one_lt_k
  have hk1 : 1 ≤ k := by omega
  have htwo : 1 ≤ 2 * k := by omega
  have hfour : 1 ≤ 4 * k ^ 2 := by nlinarith
  have hcount : (4 * k ^ 2 - 1) * (2 * k * (k - 1)) =
      2 * ((k * (2 * k - 1)) * ((k - 1) * (2 * k + 1))) := by
    zify [hk1, htwo, hfour]
    ring
  omega

/-- Assertion 2 of `ex:5.13`, Example 5.13 of [CGSS], completing `s5exline`. -/
theorem flagGraph_cospectral_lineGraph
    {P₁ B₁ : Type*} [Fintype P₁] [Fintype B₁] [DecidableEq P₁] [DecidableEq B₁]
    (D₁ : Design P₁ B₁ (k * (2 * k - 1)) ((k - 1) * (2 * k - 1)) (k * (2 * k + 1))
      ((k - 1) * (2 * k + 1)) (k * (2 * k - 3))) :
    D₁.flagGraph.Cospectral R.graph.lineGraph := by
  apply D₁.incidenceGraph.lineGraph_cospectral_of_signless_spectrum_add_zero R.graph
  · rw [R.card_edges_graph]
    have he := D₁.card_flagGraph
    rwa [D₁.incidenceGraph.card_edgeSet] at he
  · rw [D₁.spectrumMultiset_signlessLapMatrix_incidenceGraph_resolution_family D.one_lt_k,
      R.spectrumMultiset_signlessLapMatrix_graph]
    abel

end Resolution
end Design
