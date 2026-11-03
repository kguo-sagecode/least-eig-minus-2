/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.SpanExtension
import Batteries.Tactic.OpenPrivate

/-!
# Axiom audit for the Section 3 span lemmas

Every declaration of `lem:sec3-transport`, `lem:sec3-restrict`, and
`lem:sec3-extension`; only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The C6 corollary is included in `Computations/C5C6Audit.lean`.
-/

#print axioms LineSystem.Γa
#print axioms LineSystem.Δ
#print axioms LineSystem.Iso.symm
#print axioms LineSystem.Iso.exists_spanIsometry
#print axioms LineSystem.Iso.spanIsometry
#print axioms LineSystem.Iso.spanIsometry_apply
#print axioms LineSystem.Iso.spanIsometry_unique
#print axioms LineSystem.Iso.spanIsometry_symm
#print axioms LineSystem.Iso.finrank_span_eq
#print axioms LineSystem.Iso.numLines_eq
#print axioms LineSystem.Iso.nonempty_iff
#print axioms LineSystem.Iso.inner_spanIsometry
#print axioms LineSystem.Iso.spanIsometry_mem_iff
#print axioms LineSystem.Iso.isStarClosed
#print axioms LineSystem.Iso.isStarClosed_iff
#print axioms LineSystem.Iso.isIndecomposable
#print axioms LineSystem.Iso.isIndecomposable_iff
#print axioms LineSystem.Iso.isMaximal
#print axioms LineSystem.Iso.isMaximal_iff
#print axioms LineSystem.Iso.toIsometricInclusion
#print axioms LineSystem.Iso.mem_Γa_iff'
#print axioms LineSystem.Iso.image_Γa'
#print axioms LineSystem.Iso.mem_Δ_iff'
#print axioms LineSystem.Iso.image_Δ'
#print axioms LineSystem.Iso.inner_eq_zero_iff
#print axioms LineSystem.Iso.mem_Γa_iff
#print axioms LineSystem.Iso.image_Γa
#print axioms LineSystem.Iso.mem_Δ_iff
#print axioms LineSystem.Iso.image_Δ
#print axioms LineSystem.Iso.orthGraphIso
#print axioms LineSystem.Iso.orthGraphIso_apply
#print axioms LineSystem.restrictSpan
#print axioms LineSystem.Iso.restrictSpan
#print axioms LineSystem.restrictSpan_span_eq_top
#print axioms LineSystem.restrictSpan_image_eq_iff
#print axioms LineSystem.Iso.ofRestrictSpanImage
#print axioms LineSystem.ofRestrictSpanImage_apply
#print axioms LineSystem.Iso.ofSpanIsometry
#print axioms LineSystem.ofSpanIsometry_apply
#print axioms LineSystem.spanCandidates
#print axioms LineSystem.finite_spanCandidates
open private LineSystem.neg_mem_allowed from LineGraphs.LineSystem.SpanExtension
#print axioms LineSystem.neg_mem_allowed
#print axioms LineSystem.adjoinRoot
#print axioms LineSystem.IsIndecomposable.of_span_eq
#print axioms LineSystem.exists_maximal_extension_span
