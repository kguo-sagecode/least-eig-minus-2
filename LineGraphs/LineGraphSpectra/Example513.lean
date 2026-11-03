/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.ResolutionLineGraph
import LineGraphs.LineGraphSpectra.LineGraphCliques
import LineGraphs.LineGraphSpectra.Example513Parameters
import LineGraphs.LineGraphSpectra.ResolutionSpaces
import LineGraphs.Computations.C15Result

/-!
# A flag-graph family not characterized by its spectrum

Example 5.13 (`ex:5.13`) of [CGSS]. `Resolution.graph` is the graph on blocks
specified by the blueprint, and its spectrum and connectedness are derived in
`ResolutionSpectrum`. `ResolutionSpaces` identifies the blueprint's spaces and
proves the kernel-complement description; `Example513Parameters` makes the
substitution into Theorem 5.8 explicit. `ResolutionLineGraph` proves cospectrality.

For step `s5exnoiso`, a clique bound supplies the needed instance of the deferred
EX4 input: a flag graph has a clique of size `r₁`, whereas the line graph of the
regular root has every clique of size at most `κ < r₁`. No general Whitney
theorem or extra non-isomorphism assumption is used.

The C15 conclusions below use the same Hall–Connor design and its flag graph.
Our incidence graph is definitionally equal to the one used in C13 and C15.
-/

namespace SimpleGraph

/-- Change finite enumerations and adjacency decisions without changing cospectrality.
This transfers the C15 certificate in Example 5.13 (`ex:5.13`) of [CGSS]. -/
theorem Cospectral.change_instances {V W : Type*} {fV fV' : Fintype V}
    {dV dV' : DecidableEq V} {fW fW' : Fintype W} {dW dW' : DecidableEq W}
    {X : SimpleGraph V} {Y : SimpleGraph W} {dX dX' : DecidableRel X.Adj}
    {dY dY' : DecidableRel Y.Adj}
    (h : @Cospectral V W fV dV fW dW X Y dX dY) :
    @Cospectral V W fV' dV' fW' dW' X Y dX' dY' := by
  cases Subsingleton.elim fV fV'
  cases Subsingleton.elim dV dV'
  cases Subsingleton.elim fW fW'
  cases Subsingleton.elim dW dW'
  cases Subsingleton.elim dX dX'
  cases Subsingleton.elim dY dY'
  exact h

end SimpleGraph

namespace Design

attribute [local instance] Classical.propDecidable

variable {P B P' B' : Type} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  [Fintype P'] [Fintype B'] [DecidableEq P'] [DecidableEq B'] {k : ℕ}

-- Example 5.13
attribute [-instance] Computations.C13.lineGraphDecidable in
/-- Assertion 3 of Example 5.13 of [CGSS], `ex:5.13`. A resolution of the
auxiliary design constructs a cospectral graph outside the entire flag-graph
family (Implicit hypothesis 6). The assumption `k ≥ 2` follows from `D'.one_lt_k`. -/
theorem not_flagGraphCharacterized_of_resolvable
    (D : Design P B (k * (2 * k - 1)) ((k - 1) * (2 * k - 1)) (k * (2 * k + 1))
      ((k - 1) * (2 * k + 1)) (k * (2 * k - 3)))
    (D' : Design P' B' (k * (2 * k - 1)) k (4 * k ^ 2 - 1) (2 * k + 1) 1)
    (R : D'.Resolution (2 * k + 1)) : ¬ D.FlagGraphCharacterized := by
  intro h
  -- Steps `s5exspec` and `s5exline` construct this particular cospectral mate.
  obtain ⟨P₂, B₂, _, _, _, _, D₂, ⟨e⟩⟩ := h _ R.graph.lineGraph
    (R.flagGraph_cospectral_lineGraph D)
  -- Step `s5exnoiso`: the point stars of any proposed D₂ are too large.
  have hk := D'.one_lt_k
  have hk1 : 1 ≤ k := by omega
  have hd : 3 ≤ 2 * k * (k - 1) := by
    have hk' : 1 ≤ k - 1 := by omega
    nlinarith
  have hdr : 2 * k * (k - 1) < (k - 1) * (2 * k + 1) := by
    zify [hk1]
    nlinarith
  exact D₂.not_nonempty_iso_flagGraph_lineGraph_of_degree R.graph hd
    (fun a ↦ le_of_eq (R.graph_isRegularOfDegree a)) hdr ⟨e.symm⟩

end Design

namespace Computations.C15

attribute [local instance] Classical.propDecidable

/-- Compatibility of the two incidence definitions (`def:flag`, Example 5.13 of [CGSS]).
The proof is generic so no concrete incidence certificate needs to reduce. -/
theorem incidenceGraph_eq_shared {P B : Type*} [Fintype P] [Fintype B]
    [DecidableEq P] [DecidableEq B] {v k b r lam : ℕ} (D : Design P B v k b r lam) :
    D.incidenceGraph = C13.incidenceGraph D.block := by
  ext u w
  cases u <;> cases w <;> rfl

/-- The common flag graph in C15 and `def:flag`, Example 5.13 of [CGSS]. -/
noncomputable def sharedFlagGraphIso {P B : Type*} [Fintype P] [Fintype B]
    [DecidableEq P] [DecidableEq B] {v k b r lam : ℕ} (D : Design P B v k b r lam) :
    D.flagGraph ≃g (C13.incidenceGraph D.block).lineGraph :=
  (show D.incidenceGraph ≃g C13.incidenceGraph D.block from
    { toEquiv := Equiv.refl _
      map_rel_iff' := by rintro (p | a) (q | b) <;> rfl }).lineGraph

attribute [-instance] C13.lineGraphDecidable in
/-- The C15 cospectrality in the shared `Design.flagGraph` interface,
the final remark of Example 5.13 (`ex:5.13`) of [CGSS]. -/
theorem design_flagGraph_cospectral_petersen :
    design.flagGraph.Cospectral SimpleGraph.petersen.lineGraph.lineGraph := by
  have h : (C13.incidenceGraph design.block).lineGraph.Cospectral
      SimpleGraph.petersen.lineGraph.lineGraph :=
    flagGraph_cospectral_double_lineGraph.change_instances
  exact (sharedFlagGraphIso design).cospectral.trans h

attribute [-instance] C13.lineGraphDecidable in
/-- The C15 non-isomorphism in the shared `Design.flagGraph` interface,
the final remark of Example 5.13 (`ex:5.13`) of [CGSS]. -/
theorem design_flagGraph_not_nonempty_iso_petersen :
    ¬ Nonempty (design.flagGraph ≃g SimpleGraph.petersen.lineGraph.lineGraph) := by
  rintro ⟨e⟩
  exact flagGraph_not_nonempty_iso_double_lineGraph
    ⟨(sharedFlagGraphIso design).symm.trans e⟩

attribute [-instance] C13.lineGraphDecidable in
/-- The concrete family non-characterization in the final remark of
Example 5.13 (`ex:5.13`) of [CGSS]. C15 gives the mate; its regular root
has degree four, excluding every flag graph of replication five. -/
theorem not_flagGraphCharacterized : ¬ design.FlagGraphCharacterized := by
  intro h
  obtain ⟨P, B, _, _, _, _, D, ⟨e⟩⟩ := h _ SimpleGraph.petersen.lineGraph.lineGraph
    design_flagGraph_cospectral_petersen
  have hr : SimpleGraph.petersen.lineGraph.IsRegularOfDegree 4 :=
    SimpleGraph.petersen_isSRGWith.regular.lineGraph_isRegularOfDegree
  exact D.not_nonempty_iso_flagGraph_lineGraph_of_degree SimpleGraph.petersen.lineGraph
    (by decide : 3 ≤ 4) (fun a ↦ le_of_eq (hr a)) (by decide) ⟨e.symm⟩

end Computations.C15
