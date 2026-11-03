/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Theorem44
import LineGraphs.LineSystem.ClassificationMaximal

/-!
# Unconditional bounds for regular graphs represented in E₈

Theorem 4.4 of [CGSS] and assertion 1 of the following remark (`rem:4-after44`).
Theorem 3.6, `LineSystem.IsMaximal.exists_iso_rootType`, supplies the classification
hypothesis of the results in `Representation/Theorem44.lean`.

This file uses the classification-dependent bounds directly, without invoking the separate
unconditional EQ2 (`lem:4-EQ2`), `InnerProductSpace.card_le_fourteen_of_finrank_eq_eight`.
That theorem is checked in `Representation/Audit.lean`; its statement agrees with
`InnerProductSpace.card_le_fourteen_of_finrank_eq_eight_of_classification` after removing
`hclass`: both concern a finite family of unit vectors spanning an eight-dimensional real
inner product space, with distinct-index inner products `±1/3`, and conclude cardinality
at most fourteen. Theorem 3.6 supplies that hypothesis for `WithLp 2 (E × ℝ)` for any such
ambient space `E`.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {X : SimpleGraph V} [DecidableRel X.Adj] {d : ℕ}

-- Theorem 4.4
omit [Nonempty V] in
/-- Theorem 4.4 of [CGSS], order bound: a regular graph represented in E₈ has at most
28 vertices, including the empty case. Theorem 3.6 discharges the classification hypothesis. -/
theorem IsRepresentedIn.card_le_28_of_regular
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d) :
    Fintype.card V ≤ 28 := by
  cases isEmpty_or_nonempty V with
  | inl hV => simp
  | inr hV =>
    exact hX.card_le_28_of_regular_of_classification h
      fun _ hne hmax hI ↦ hmax.exists_iso_rootType hne hI

-- Theorem 4.4
/-- Theorem 4.4 of [CGSS], degree bound: a nonempty regular graph represented in E₈ has
degree at most 16. Theorem 3.6 discharges the classification hypothesis used by EQ2. -/
theorem IsRepresentedIn.degree_le_16_of_regular
    (hX : X.IsRepresentedIn LineSystem.E₈) (h : X.IsRegularOfDegree d) : d ≤ 16 :=
  hX.degree_le_16_of_regular_of_classification h
    fun _ hne hmax hI ↦ hmax.exists_iso_rootType hne hI

-- Remark after Theorem 4.4
omit [Nonempty V] in
/-- Remark after Theorem 4.4 of [CGSS], blueprint assertion 1 (`rem:4-after44`): a regular graph
on 28 vertices of degree 16 cannot be represented in E₈. Theorem 3.6 discharges the
classification hypothesis used by EQ2. -/
theorem not_regular_28_16_isRepresentedIn_E₈
    (h : X.IsRegularOfDegree 16) (hn : Fintype.card V = 28) :
    ¬ X.IsRepresentedIn LineSystem.E₈ := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact not_regular_28_16_isRepresentedIn_E₈_of_classification h hn
    fun _ hne hmax hI ↦ hmax.exists_iso_rootType hne hI

end SimpleGraph
