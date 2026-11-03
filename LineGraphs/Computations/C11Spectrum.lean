import LineGraphs.Computations.C11
import LineGraphs.Spectral.Basic

/-!
# C11: spectral parameter substitution for [CGSS], Theorem 5.8

This is the algebra in `s558nbc` and `s558nbspec`: the spectrum delivered by Remark 5.7 is
rewritten in terms of `s,t`, including the natural-number multiplicities.
-/

namespace Computations.C11

/-- C11, [CGSS] Theorem 5.8, `s558nbspec`: substitute the design parameters in the spectrum. -/
theorem spectrum_of_parameters {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v b k r s t lam : ℕ) (hs : 2 ≤ s)
    (hv : 2 * v = s * (s + 1)) (hb : 2 * b = (s + 1) * (s + 2))
    (hk : k = s * t) (hr : r = (s + 2) * t)
    (hl : (lam : ℝ) * (s - 1) = 2 * t * (s * t - 1))
    (hsp : G.spectrumMultiset =
      {((r : ℝ) + k) / 2} + Multiset.replicate (b - v) (-(((r : ℝ) - k) / 2)) +
      Multiset.replicate (v - 1) (Real.sqrt (r - lam + (((r : ℝ) - k) / 2) ^ 2)) +
      Multiset.replicate (v - 1) (-Real.sqrt (r - lam + (((r : ℝ) - k) / 2) ^ 2))) :
    G.spectrumMultiset =
      {((s : ℝ) + 1) * t} + Multiset.replicate (s + 1) (-(t : ℝ)) +
      Multiset.replicate ((s - 1) * (s + 2) / 2)
        (Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) +
      Multiset.replicate ((s - 1) * (s + 2) / 2)
        (-Real.sqrt (t * (s + 1) * ((s : ℝ) - t) / (s - 1))) := by
  have hvpos : 1 ≤ v := by nlinarith
  have hsm : s - 1 + 1 = s := by omega
  have hvm : v - 1 + 1 = v := by omega
  have hm : 2 * (v - 1) = (s - 1) * (s + 2) := by nlinarith
  have hmult : v - 1 = (s - 1) * (s + 2) / 2 := by omega
  have hbv : b - v = s + 1 := by
    have : b = v + s + 1 := by nlinarith
    omega
  have hsreal : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hsne : (s : ℝ) ≠ 1 := by linarith
  have hlam : (lam : ℝ) = 2 * t * (s * t - 1) / (s - 1) :=
    (eq_div_iff (sub_ne_zero.mpr hsne)).mpr hl
  have hhalf : ((r : ℝ) - k) / 2 = t := by rw [hr, hk]; push_cast; ring
  have hdegree : ((r : ℝ) + k) / 2 = ((s : ℝ) + 1) * t := by
    rw [hr, hk]
    push_cast
    ring
  have hc : (r : ℝ) - lam + (t : ℝ) ^ 2 =
      t * (s + 1) * ((s : ℝ) - t) / (s - 1) := by
    rw [hr, hlam]
    push_cast
    exact nonprincipal_square s t hsne
  rw [hsp, hhalf, hdegree, hc, hmult, hbv]

end Computations.C11
