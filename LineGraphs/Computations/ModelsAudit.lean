/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.E8

/-!
# ModelsAudit

Axiom audit for the integer root models. The main theorems transitively check their helpers
and the materialized table certificates. No evaluation oracle is part of these proofs. -/

#print axioms LineSystem.IntegerModel.inner_self
#print axioms LineSystem.IntegerModel.numLines_eq
#print axioms LineSystem.IntegerModel.sum_Φ
#print axioms LineSystem.IntegerModel.mem_iff_decode
#print axioms LineSystem.IntegerModel.isStarClosed_of
#print axioms LineSystem.IntegerModel.isStarClosed_of_decoder
#print axioms LineSystem.IntegerModel.isStarClosed_of_checkStar
#print axioms LineSystem.IntegerModel.isIndecomposable_of_parent
#print axioms LineSystem.Iso.ofIntegerModels
#print axioms LineSystem.IsStarClosed.orthogonalTo
#print axioms LineSystem.numLines_An
#print axioms LineSystem.numLines_Dn
#print axioms LineSystem.numLines_E₈
#print axioms LineSystem.numLines_E₈viaA₈
#print axioms LineSystem.numLines_E₈viaSteiner
#print axioms LineSystem.numLines_E₇
#print axioms LineSystem.numLines_E₆
#print axioms LineSystem.finrank_span_An
#print axioms LineSystem.finrank_span_Dn
#print axioms LineSystem.finrank_span_E₈
#print axioms LineSystem.finrank_span_E₈viaA₈
#print axioms LineSystem.finrank_span_E₈viaSteiner
#print axioms LineSystem.finrank_span_E₇
#print axioms LineSystem.finrank_span_E₆
#print axioms LineSystem.integerVector_mem_An_iff
#print axioms LineSystem.integerVector_mem_Dn_iff
#print axioms LineSystem.integerVector_mem_E₈_iff
#print axioms LineSystem.integerVector_mem_E₈viaA₈_iff
#print axioms LineSystem.integerVector_mem_E₈viaSteiner_iff
#print axioms LineSystem.integerVector_mem_E₇_iff
#print axioms LineSystem.integerVector_mem_E₆_iff
#print axioms Computations.e₈ARoots_eq_map
#print axioms Computations.e₈SteinerRoots_eq_map
#print axioms LineSystem.isStarClosed_An
#print axioms LineSystem.isStarClosed_Dn
#print axioms LineSystem.isStarClosed_E₈
#print axioms LineSystem.isStarClosed_E₇
#print axioms LineSystem.isStarClosed_E₆
