/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.ClawsClassification
import LineGraphs.Representation.Seidel413

/-!
# Axiom audit for Theorems 4.10--4.13

Theorems 4.10, 4.11 and 4.13 and Remark 4.12 of [CGSS], including all public
supporting declarations and the existing degree formulas C10. This companion
to `Representation/Audit.lean` imports the new modules without changing the
imports of that existing file.
-/

#print axioms SimpleGraph.hoffman
#print axioms SimpleGraph.hoffman_of_large
#print axioms SimpleGraph.generalizedLineGraphZeroIso
#print axioms SimpleGraph.Connected.forall_of_adj_closed
#print axioms SimpleGraph.nonempty_iso_cocktailParty_of_isolated
#print axioms SimpleGraph.IsGeneralizedLineGraph.lineGraph_or_cocktailParty
#print axioms SimpleGraph.hoffman_rayChaudhuri
#print axioms SimpleGraph.hoffman_rayChaudhuri_of_large
#print axioms SimpleGraph.IsClawOfSize
#print axioms SimpleGraph.IsClaw
#print axioms SimpleGraph.IsFourClaw
#print axioms SimpleGraph.ClawFree
#print axioms SimpleGraph.FourClawFree
#print axioms SimpleGraph.starGraph_isIndContained_iff
#print axioms SimpleGraph.clawFree_iff_forall_not_isClaw
#print axioms SimpleGraph.fourClawFree_iff_forall_not_isFourClaw
#print axioms SimpleGraph.Iso.clawFree_iff
#print axioms SimpleGraph.Iso.fourClawFree_iff
#print axioms SimpleGraph.IsClawOfSize.exists_subset
#print axioms SimpleGraph.generalizedLineGraphAt
#print axioms SimpleGraph.generalizedLineGraph_independent_at_card_le
#print axioms SimpleGraph.generalizedLineGraph_not_isClaw_petal
#print axioms SimpleGraph.generalizedLineGraph_isClaw_edge_iff
#print axioms SimpleGraph.generalizedLineGraph_isFourClaw_edge_iff
#print axioms SimpleGraph.generalizedLineGraph_clawFree_iff
#print axioms SimpleGraph.generalizedLineGraph_fourClawFree_iff
#print axioms SimpleGraph.lineGraph_clawFree
#print axioms SimpleGraph.cocktailPartyGeneralizedIso
#print axioms SimpleGraph.cocktailParty_clawFree
#print axioms SimpleGraph.generalizedLineGraph_star_adj_description
#print axioms SimpleGraph.generalizedLineGraph_star_clawFree
#print axioms SimpleGraph.IsGeneralizedLineGraph.clawFree_iff
#print axioms SimpleGraph.hoffman_of_clawFree
#print axioms SimpleGraph.generalizedLineGraph_degree_petal
#print axioms SimpleGraph.generalizedLineGraph_degree_edge
#print axioms SimpleGraph.seidel
#print axioms SimpleGraph.seidel_of_large
