/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.Checkers

/-!
# Pruned searches over strongly regular parameters

For the connected, noncomplete case used by C18, `0 < μ ≤ k`, `λ < k` and `k + 1 ≤ n`.
The parameter equation determines `n`. A range of valencies makes each kernel proof small.
The case `μ = 0` is deliberately excluded and must be handled separately by an application.
-/

namespace Computations

/-- Stream a valency interval, determine the order from the parameter equation, and skip
nonintegral or out-of-range orders. -/
def allSRGParameters (nBound kStart kCount : ℕ) (p : ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range' kStart kCount).all fun k =>
    (List.range k).all fun lam => (List.range k).all fun mu0 =>
      let mu := mu0 + 1
      let t := k * (k - lam - 1)
      let n := k + 1 + t / mu
      if t % mu == 0 && decide (n < nBound) then p n k lam mu else true

/-- Every tuple satisfying the stated mathematical restrictions is visited by the pruned search. -/
theorem allSRGParameters_sound {nBound kStart kCount : ℕ} {p : ℕ → ℕ → ℕ → ℕ → Bool}
    (h : allSRGParameters nBound kStart kCount p = true) {n k lam mu : ℕ}
    (hn : n < nBound) (hk : k ∈ List.range' kStart kCount) (hlam : lam < k)
    (hmu : 0 < mu) (hmuk : mu ≤ k) (hkn : k + 1 ≤ n)
    (he : k * (k - lam - 1) = (n - k - 1) * mu) : p n k lam mu = true := by
  have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h k hk)
    lam (List.mem_range.mpr hlam)) (mu - 1) (List.mem_range.mpr (by omega))
  have hm : mu - 1 + 1 = mu := by omega
  have hd : k * (k - lam - 1) / mu = n - k - 1 := by
    rw [he, Nat.mul_div_cancel _ hmu]
  have ht : k * (k - lam - 1) % mu = 0 := by rw [he, Nat.mul_mod_left]
  have ho : k + 1 + k * (k - lam - 1) / mu = n := by omega
  simpa only [hm, ht, ho, beq_self_eq_true, hn, decide_true, Bool.and_self, ite_true] using hc

/-- Reflection for a pruned valency chunk, with all pruning hypotheses explicit. -/
theorem no_srg_solution_of_check {nBound kStart kCount : ℕ}
    {test : ℕ → ℕ → ℕ → ℕ → Bool} {P : ℕ → ℕ → ℕ → ℕ → Prop}
    (h : allSRGParameters nBound kStart kCount (fun n k lam mu => !test n k lam mu) = true)
    (reflect : ∀ n k lam mu, P n k lam mu → test n k lam mu = true) :
    ¬ ∃ n k lam mu, n < nBound ∧ k ∈ List.range' kStart kCount ∧ lam < k ∧
      0 < mu ∧ mu ≤ k ∧ k + 1 ≤ n ∧
      k * (k - lam - 1) = (n - k - 1) * mu ∧ P n k lam mu := by
  rintro ⟨n, k, lam, mu, hn, hk, hl, hm, hmk, hkn, he, hp⟩
  have hc := allSRGParameters_sound h hn hk hl hm hmk hkn he
  simp [reflect n k lam mu hp] at hc

end Computations
