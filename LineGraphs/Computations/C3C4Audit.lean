/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C3
import LineGraphs.Computations.C4
import LineGraphs.Computations.C20
import LineGraphs.Computations.C21
import LineGraphs.Computations.RootMapCertificates

/-!
# Axiom audit for C3, C4, C20, and C21

The public conclusions audit their certificate checks transitively. The checker soundness
lemmas are included explicitly. `LineGraphs/scripts/verify_c3_c4.py` checks that it prints only
standard axioms.
-/

#print axioms Computations.checkScaledGram_sound
#print axioms Computations.checkRootImages_sound
#print axioms Computations.checkSRG_sound
#print axioms Computations.checkScaledLDL_sound
#print axioms Computations.checkRootCoordinates_sound
#print axioms LineSystem.IntegerModel.ofTable
#print axioms LineSystem.IntegerModel.subsetEquiv
#print axioms LineSystem.IntegerModel.isIndecomposable_of_two_steps
#print axioms LineSystem.IntegerModel.card_N_of_check
#print axioms LineSystem.Iso.isIndecomposable
#print axioms LineSystem.Iso.isStarClosed
#print axioms LineSystem.E₈viaA₈.isoE₈
#print axioms LineSystem.E₈viaA₈.nonempty_iso_E₈
#print axioms LineSystem.E₈viaSteiner.isoE₈
#print axioms LineSystem.E₈viaSteiner.nonempty_iso_E₈
#print axioms LineSystem.isIndecomposable_An
#print axioms LineSystem.isStarClosed_An
#print axioms LineSystem.isIndecomposable_Dn
#print axioms LineSystem.isStarClosed_Dn
#print axioms LineSystem.isIndecomposable_E₆
#print axioms LineSystem.isStarClosed_E₆
#print axioms LineSystem.isIndecomposable_E₇
#print axioms LineSystem.isStarClosed_E₇
#print axioms LineSystem.isIndecomposable_E₈
#print axioms LineSystem.isStarClosed_E₈
#print axioms LineSystem.isIndecomposable_E₈viaA₈
#print axioms LineSystem.isStarClosed_E₈viaA₈
#print axioms LineSystem.isIndecomposable_E₈viaSteiner
#print axioms LineSystem.isStarClosed_E₈viaSteiner
#print axioms LineSystem.An.hyp24
#print axioms LineSystem.An.gammaEquiv
#print axioms LineSystem.An.orthGraphIso
#print axioms LineSystem.An.card_Γa
#print axioms LineSystem.Dn.hyp24
#print axioms LineSystem.Dn.gammaEquiv
#print axioms LineSystem.Dn.orthGraphIso
#print axioms LineSystem.Dn.card_Γa
#print axioms LineSystem.E₆.hyp24
#print axioms LineSystem.E₆.gammaEquiv
#print axioms LineSystem.E₆.orthGraphIso
#print axioms LineSystem.E₆.card_Γa
#print axioms LineSystem.E₆.hyp24_a
#print axioms LineSystem.E₆.hyp24_b
#print axioms LineSystem.E₆.hyp24_c
#print axioms LineSystem.E₆.deltaEquiv
#print axioms LineSystem.E₆.orthGraph_isSRGWith
#print axioms LineSystem.E₆.card_Δ_div_two
#print axioms LineSystem.E₇.hyp24
#print axioms LineSystem.E₇.gammaEquiv
#print axioms LineSystem.E₇.orthGraphIso
#print axioms LineSystem.E₇.card_Γa
#print axioms LineSystem.E₇.hyp24_a
#print axioms LineSystem.E₇.hyp24_b
#print axioms LineSystem.E₇.hyp24_c
#print axioms LineSystem.E₇.deltaEquiv
#print axioms LineSystem.E₇.orthGraph_isSRGWith
#print axioms LineSystem.E₇.card_Δ_div_two
#print axioms LineSystem.E₈.hyp24
#print axioms LineSystem.E₈.gammaEquiv
#print axioms LineSystem.E₈.orthGraphIso
#print axioms LineSystem.E₈.card_Γa
#print axioms LineSystem.E₈.hyp24_a
#print axioms LineSystem.E₈.hyp24_b
#print axioms LineSystem.E₈.hyp24_c
#print axioms LineSystem.E₈.deltaEquiv
#print axioms LineSystem.E₈.orthGraph_isSRGWith
#print axioms LineSystem.E₈.card_Δ_div_two
#print axioms LineSystem.finite_N
#print axioms LineSystem.pairInv
#print axioms LineSystem.pairInv_add
#print axioms LineSystem.pairInv_ne
#print axioms LineSystem.An.neighborEquiv
#print axioms LineSystem.An.card_N
#print axioms LineSystem.An.card_N_nine
#print axioms LineSystem.Dn.neighborEquiv
#print axioms LineSystem.Dn.card_N
#print axioms LineSystem.Dn.card_N_nine
#print axioms LineSystem.E₆.card_N
#print axioms LineSystem.E₆.neighborPairs
#print axioms LineSystem.E₆.neighborPairs_add
#print axioms LineSystem.E₆.simpleRoot_mem
#print axioms LineSystem.E₆.gram_simpleRoot
#print axioms LineSystem.E₆.det_gram_simpleRoot
#print axioms LineSystem.E₆.simpleBasis
#print axioms LineSystem.E₆.simpleBasis_apply
#print axioms LineSystem.E₆.exists_simpleRoot_coordinates
#print axioms LineSystem.E₇.card_N
#print axioms LineSystem.E₇.neighborPairs
#print axioms LineSystem.E₇.neighborPairs_add
#print axioms LineSystem.E₇.simpleRoot_mem
#print axioms LineSystem.E₇.gram_simpleRoot
#print axioms LineSystem.E₇.det_gram_simpleRoot
#print axioms LineSystem.E₇.simpleBasis
#print axioms LineSystem.E₇.simpleBasis_apply
#print axioms LineSystem.E₇.exists_simpleRoot_coordinates
#print axioms LineSystem.E₈.card_N
#print axioms LineSystem.E₈.neighborPairs
#print axioms LineSystem.E₈.neighborPairs_add
#print axioms LineSystem.E₈.simpleRoot_mem
#print axioms LineSystem.E₈.gram_simpleRoot
#print axioms LineSystem.E₈.det_gram_simpleRoot
#print axioms LineSystem.E₈.simpleBasis
#print axioms LineSystem.E₈.simpleBasis_apply
#print axioms LineSystem.E₈.exists_simpleRoot_coordinates
#print axioms Computations.C21.e6_gram_eq_cartan
#print axioms LineSystem.E₆.gram_simpleRoot_eq_cartan
#print axioms Computations.C21.e7_gram_eq_cartan
#print axioms LineSystem.E₇.gram_simpleRoot_eq_cartan
#print axioms Computations.C21.e8_gram_eq_cartan
#print axioms LineSystem.E₈.gram_simpleRoot_eq_cartan
