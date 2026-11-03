/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4
import LineGraphs.Computations.C20Apex

/-!
# Axiom audit for the star isometries of C4 and the apex pairs of C20

Each declaration should use only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LineSystem.rootReflection_mem_isometryGroup
#print axioms LineSystem.Hyp24.orthGraphIsoOfIsometry
#print axioms LineSystem.IntegerModel.exists_isometry_of_tree
#print axioms LineSystem.IntegerModel.exists_isometry_of_star
#print axioms LineSystem.E₆.exists_isometry_star
#print axioms LineSystem.E₇.exists_isometry_star
#print axioms LineSystem.E₈.exists_isometry_star
#print axioms LineSystem.Hyp24.orthGraph_isSRGWith_of_S_eq_E₆
#print axioms LineSystem.Hyp24.orthGraph_isSRGWith_of_S_eq_E₇
#print axioms LineSystem.Hyp24.orthGraph_isSRGWith_of_S_eq_E₈
#print axioms LineSystem.Hyp24.card_Γa_of_S_eq_E₈
#print axioms LineSystem.Hyp24.card_Δ_of_S_eq_E₈
#print axioms LineSystem.E₆.hyp24Simple_a
#print axioms LineSystem.E₈.hyp24Simple_b
#print axioms LineSystem.E₆.latticeGraphIso
#print axioms LineSystem.E₇.triangularGraphComplIso
#print axioms LineSystem.Hyp24.nonempty_latticeGraph_iso_of_S_eq_E₆
#print axioms LineSystem.Hyp24.nonempty_triangularGraph_compl_iso_of_S_eq_E₇
#print axioms LineSystem.Dn.orthGraphIso
#print axioms LineSystem.Dn.hyp24_a
#print axioms LineSystem.An.hyp24_b
#print axioms LineSystem.E₈.card_Δ
#print axioms Computations.C4.model_data
#print axioms Computations.C4.marked_star_data
#print axioms Computations.C4.exceptional_star_data
#print axioms LineSystem.E₈.N_c
#print axioms LineSystem.E₇.N_c
#print axioms LineSystem.E₆.N_c
#print axioms LineSystem.E₈.cPairs_true
#print axioms LineSystem.E₇.pairInv_cPairs
#print axioms LineSystem.E₆.card_N_c
