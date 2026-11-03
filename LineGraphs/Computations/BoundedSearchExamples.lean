/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.BoundedSearch

/-!
# C18 search-domain benchmark

Four valency chunks exercise the actual bounds and parameter pruning used by C18.
These check domain traversal, not the additional spectral feasibility conditions of C18.
-/

namespace Computations.Examples

/-- A cheap consistency check on each visited tuple, evaluated entirely over naturals. -/
def srgDomainCheck (n k lam mu : ℕ) : Bool :=
  decide (n ≤ 36 ∧ k ≤ 16 ∧ lam < k ∧ 0 < mu ∧ mu ≤ k ∧
    k * (k - lam - 1) = (n - k - 1) * mu)

theorem srg_domain_chunk_0 : allSRGParameters 37 0 5 srgDomainCheck = true := by decide +kernel
theorem srg_domain_chunk_1 : allSRGParameters 37 5 4 srgDomainCheck = true := by decide +kernel
theorem srg_domain_chunk_2 : allSRGParameters 37 9 4 srgDomainCheck = true := by decide +kernel
theorem srg_domain_chunk_3 : allSRGParameters 37 13 4 srgDomainCheck = true := by decide +kernel

/-- Every valency below seventeen belongs to one of the independently checked chunks. -/
theorem srg_domain_chunks_cover {k : ℕ} (hk : k < 17) :
    k ∈ List.range' 0 5 ∨ k ∈ List.range' 5 4 ∨
      k ∈ List.range' 9 4 ∨ k ∈ List.range' 13 4 := by
  simp only [List.mem_range'_1]
  omega

example : allSRGParameters 37 0 17 (fun _ _ _ _ => false) = false := by decide +kernel
example : allSRGParameters 37 0 0 (fun _ _ _ _ => false) = true := by decide +kernel

end Computations.Examples
