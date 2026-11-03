/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.RootType
import LineGraphs.LineSystem.ClassificationMaximal

/-!
# A root system containing the lines, unconditionally

Lemma `lem:4-rootsystem` of `blueprint/sec4-leasteigenvalue.tex`, assertion 1, used in
Section 4 of [CGSS]: the classification hypothesis of
`IsRepresentation.exists_isRepresentedIn_rootType_of_classification` is Theorem 3.6
(`LineSystem.IsMaximal.exists_iso_rootType`).
-/

open Submodule Module

namespace SimpleGraph

variable {V E : Type*} [Finite V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : SimpleGraph V} [DecidableRel X.Adj] {x : V → E}

/-- Lemma `lem:4-rootsystem`, assertion 1 (Section 4 of [CGSS], "such a set of lines is
contained in a root system"): a connected graph with a representation `x` is represented in the
model of a `RootType` whose rank is the dimension of the span of `x`. Step `s4rstype` is
Theorem 3.6 of [CGSS], `LineSystem.IsMaximal.exists_iso_rootType`. The ambient space need not
be finite-dimensional. -/
theorem IsRepresentation.exists_isRepresentedIn_rootType (hx : X.IsRepresentation x)
    (hX : X.Connected) :
    ∃ t : LineSystem.RootType, X.IsRepresentedIn t.model ∧
      t.rank = finrank ℝ (span ℝ (Set.range x)) :=
  hx.exists_isRepresentedIn_rootType_of_classification hX
    fun _ hne hmax hI ↦ hmax.exists_iso_rootType hne hI

end SimpleGraph
