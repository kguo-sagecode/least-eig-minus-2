/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Theorem312.Main

/-!
# Audit of Theorem 3.12 of [CGSS]

All 28 Lean tags of `blueprint/sec3-thm312.tex`, in blueprint order.
The statements retain the settled names and allow empty sets and empty colour fibres.
The final theorem assumes finite dimension, one-dimensional members and allowed angles.

Proof map:
* `Defs`: `def:312-angles`, `def:312-root-lines`, `def:312-integral-roots`,
  `lem:312-representatives`, `lem:312-squared-cosine`, `lem:312-coordinates`.
* `Finite`: all cases and the finite signature argument of `lem:312-finite`.
* `IntegerSpan`: `lem:312-integer-span`, with finite sums encoded by span induction.
* `RootSet`: `lem:312-reflection`, `lem:312-proportional`, `prop:312-rootset`;
  all six root-set conditions, the seed inclusion and both squared lengths.
* `Completion`: all old/new pairing cases and orthogonal spanning of `lem:312-completion`.
* `Seeds`: all four ordered Boolean pairs, the diagonal and spans in `lem:312-seeds`.
* `Containment`: both ambient and subspace constructions in `cor:312-containment`.
* `Lengths`: `lem:312-lengths`, proving its pairwise input directly from the
  crystallographic coefficients, as in the ordinary proof. This replaces the appeal
  to the geometric root-angle lemma (not available in `RootSystems`); it changes no
  statement and uses no classification.
* `Necessary`: both logarithm shifts in `lem:312-log`, and the length/parity colouring
  in `lem:312-necessary`, including orthogonal pairs and either empty fibre.
* `Main`: both implications of `thm:3.12` and the constant-colour `lem:312-bridge`.

Interface generalizations: integer-span integrality/evenness do not need finite or
normalized seeds. A finite generating set suffices for bounded-span finiteness and,
when spanning, the root-set construction, without an ambient finite-dimension instance.
Root-length, necessary-colouring and Section 2 bridge lemmas likewise need no explicit
finite-dimension instance. The two logarithm lemmas are public for this named audit.
No mathematical conclusion has been weakened.

The declarations below print their types and transitive axiom dependencies. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. The private arithmetic
helpers are included transitively in these dependency checks.
-/

#check LineSystem.HasSquaredCosine
#print axioms LineSystem.HasSquaredCosine

#check LineSystem.HasAllowedAngles
#print axioms LineSystem.HasAllowedAngles

#check LineSystem.HasBipartition
#print axioms LineSystem.HasBipartition

#check LineSystem.rootLines
#print axioms LineSystem.rootLines

#check LineSystem.integralSpanRoots
#print axioms LineSystem.integralSpanRoots

#check LineSystem.exists_mem_line_sqNorm_eq
#print axioms LineSystem.exists_mem_line_sqNorm_eq

#check LineSystem.hasSquaredCosine_iff
#print axioms LineSystem.hasSquaredCosine_iff

#check LineSystem.HasSquaredCosine.unique
#print axioms LineSystem.HasSquaredCosine.unique

#check LineSystem.inner_coordinates_injective
#print axioms LineSystem.inner_coordinates_injective

#check LineSystem.finite_of_hasAllowedAngles
#print axioms LineSystem.finite_of_hasAllowedAngles

#check LineSystem.inner_int_of_mem_intSpan
#print axioms LineSystem.inner_int_of_mem_intSpan

#check LineSystem.inner_even_of_mem_intSpan
#print axioms LineSystem.inner_even_of_mem_intSpan

#check LineSystem.finite_bounded_intSpan
#print axioms LineSystem.finite_bounded_intSpan

#check IsRootSet.reflection_self_adjoint
#print axioms IsRootSet.reflection_self_adjoint

#check LineSystem.eq_one_or_neg_one_of_integral_proportional
#print axioms LineSystem.eq_one_or_neg_one_of_integral_proportional

#check LineSystem.isRootSet_integralSpanRoots
#print axioms LineSystem.isRootSet_integralSpanRoots

#check LineSystem.exists_spanning_integral_seed_extension
#print axioms LineSystem.exists_spanning_integral_seed_extension

#check LineSystem.exists_integral_seeds_of_hasBipartition
#print axioms LineSystem.exists_integral_seeds_of_hasBipartition

#check LineSystem.exists_rootSet_of_hasBipartition
#print axioms LineSystem.exists_rootSet_of_hasBipartition

#check LineSystem.exists_rootSet_in_span_of_hasBipartition
#print axioms LineSystem.exists_rootSet_in_span_of_hasBipartition

#check IsRootSet.sqNorm_eq_of_four_mul_inner_sq_eq
#print axioms IsRootSet.sqNorm_eq_of_four_mul_inner_sq_eq

#check IsRootSet.sqNorm_eq_two_mul_or_of_two_mul_inner_sq_eq
#print axioms IsRootSet.sqNorm_eq_two_mul_or_of_two_mul_inner_sq_eq

#check Int.log_two_mul
#print axioms Int.log_two_mul

#check Int.log_two_div
#print axioms Int.log_two_div

#check LineSystem.hasBipartition_of_subset_rootLines
#print axioms LineSystem.hasBipartition_of_subset_rootLines

#check LineSystem.subset_rootSet_iff_bipartition
#print axioms LineSystem.subset_rootSet_iff_bipartition

#check LineSystem.hasAllowedAngles_rootLines
#print axioms LineSystem.hasAllowedAngles_rootLines

#check LineSystem.hasBipartition_rootLines
#print axioms LineSystem.hasBipartition_rootLines

-- Additional public supporting declarations, all for Theorem 3.12 of [CGSS].
#print axioms LineSystem.exists_ne_zero_mem_line
#print axioms LineSystem.HasBipartition.hasAllowedAngles
#print axioms LineSystem.finite_of_inner_mem_finite
#print axioms LineSystem.mem_realSpan_of_mem_intSpan
#print axioms LineSystem.sqNorm_mem_integralSpanRoots
#print axioms LineSystem.subset_integralSpanRoots
#print axioms LineSystem.rootLines_mono
