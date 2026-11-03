/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LengthCounts

/-!
# Lines in the coordinate root sets

Step `rctlines` of `lem:counts` in the blueprint for Remark 3.11 of [CGSS].
Every root line contains exactly the root and its negative. The count convention
is the same as `LineSystem.numLines`: half the number of oriented roots.
-/

open scoped RealInnerProductSpace
open Submodule

namespace IsRootSet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Φ : Set V}

/-- Step `rctlines` of Remark 3.11: the roots on a root line are exactly one sign pair. -/
theorem roots_on_line (hΦ : IsRootSet Φ) {r : V} (hr : r ∈ Φ) :
    {s ∈ Φ | s ∈ ℝ ∙ r} = {r, -r} := by
  ext s
  constructor
  · rintro ⟨hs, hline⟩
    obtain ⟨a, ha⟩ := mem_span_singleton.mp hline
    rcases hΦ.reduced r hr a (ha ▸ hs) with h | h
    · rw [h, one_smul] at ha
      exact Or.inl ha.symm
    · rw [h, neg_one_smul] at ha
      exact Or.inr ha.symm
  · intro hs
    rcases hs with hs | hs
    · rw [show s = r from hs]
      exact ⟨hr, mem_span_singleton_self r⟩
    · rw [show s = -r from hs]
      exact ⟨hΦ.neg_mem hr, (ℝ ∙ r).neg_mem (mem_span_singleton_self r)⟩

/-- Step `rctlines`: a root line contains precisely two distinct roots. -/
theorem ncard_roots_on_line (hΦ : IsRootSet Φ) {r : V} (hr : r ∈ Φ) :
    {s ∈ Φ | s ∈ ℝ ∙ r}.ncard = 2 := by
  rw [hΦ.roots_on_line hr]
  apply Set.ncard_pair
  intro h
  have he : (2 : ℝ) • r = 0 := by
    simpa only [two_smul] using (add_eq_zero_iff_eq_neg.mpr h)
  exact hΦ.ne_zero hr ((smul_eq_zero.mp he).resolve_left (by norm_num))

/-- The line count in Remark 3.11, with the convention of `LineSystem.numLines`.
Reducedness and negation closure give two roots on each line (`roots_on_line`). -/
noncomputable def numLines (_hΦ : IsRootSet Φ) : ℕ := Φ.ncard / 2

end IsRootSet

namespace RootSetModel

/-- The line-count column of `tab:roots` in Remark 3.11. -/
def lineCount {n : ℕ} : CartanMatrix.FiniteType n → ℕ
  | .a n _ => n * (n + 1) / 2
  | .b n _ | .c n _ => n ^ 2
  | .d n _ => n * (n - 1)
  | .e₆ => 36
  | .e₇ => 63
  | .e₈ => 120
  | .f₄ => 24
  | .g₂ => 6

-- Remark 3.11, lem:counts
/-- The line-count assertions of `lem:counts` in Remark 3.11 of [CGSS]. -/
theorem numLines {n : ℕ} (t : CartanMatrix.FiniteType n) :
    (isRootSet t).numLines = lineCount t := by
  rw [IsRootSet.numLines, root_counts]
  cases t <;> simp [rootCount, lineCount, Nat.mul_assoc]

end RootSetModel
