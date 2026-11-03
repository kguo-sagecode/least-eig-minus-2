/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Basic

/-!
# Seidel switching equivalence

The witness combines vertex relabelling and a diagonal matrix of signs.
-/

namespace Matrix

/-- Simultaneous relabelling and sign conjugation of two real matrices. -/
def IsSwitchingEquivalent {V W : Type*} (S : Matrix V V ℝ) (T : Matrix W W ℝ) : Prop :=
  ∃ e : V ≃ W, ∃ d : V → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
    ∀ i j, S i j = d i * d j * T (e i) (e j)

end Matrix

namespace SimpleGraph

/-- Seidel switching equivalence includes graph isomorphism as the all-positive signing. -/
def IsSwitchingEquivalent {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop :=
  G.seidelMatrix.IsSwitchingEquivalent H.seidelMatrix

end SimpleGraph
