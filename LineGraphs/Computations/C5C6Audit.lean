/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C5
import LineGraphs.Computations.C6

/-!
# Axiom audit for computations C5 and C6 and Theorem 3.7

Each declaration should use only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- C5: isometric inclusions and the marked-graph lemma
#print axioms LineSystem.IsometricInclusion.isProper_of_ncard_lt
#print axioms LineSystem.IsometricInclusion.orthGraphEmbedding
#print axioms LineSystem.Hyp24.orthGraph_embedding_of_subset
#print axioms LineSystem.not_isMaximal_of_proper_isometric_inclusion
-- C5: every ordered star of Dₙ
#print axioms Computations.C5.exists_perm_three
#print axioms LineSystem.signedPerm_mem_isometryGroup
#print axioms LineSystem.Dn.exists_pair_of_inner_eq_neg_one
#print axioms LineSystem.Dn.exists_isometry_star
#print axioms LineSystem.Hyp24.nonempty_orthGraph_iso_of_S_eq_Dn
#print axioms LineSystem.Hyp24.card_Γa_of_S_eq_Dn
-- C5: the inclusions
#print axioms Computations.C5.a₈_rows_gram
#print axioms Computations.C5.a₈_rows_mem
#print axioms Computations.C5.a₇_rows_gram
#print axioms Computations.C5.a₇_rows_mem
#print axioms LineSystem.An.inclusionE₈
#print axioms LineSystem.An.inclusionE₇
#print axioms LineSystem.Dn.inclusionE₈
#print axioms LineSystem.An.inclusionE₈_isProper
#print axioms LineSystem.An.inclusionE₇_isProper
#print axioms LineSystem.Dn.inclusionE₈_isProper
#print axioms LineSystem.An.inclusionE₈viaA₈_isProper
#print axioms LineSystem.An.not_isMaximal_seven
#print axioms LineSystem.An.not_isMaximal_eight
#print axioms LineSystem.Dn.not_isMaximal_eight
-- C5: the obstructions
#print axioms SimpleGraph.friendship_card_le_of_embedding_bot
#print axioms SimpleGraph.lineGraph_completeBipartite_three_card_le_of_embedding_bot
#print axioms LineSystem.not_embeds_An_Dn
#print axioms LineSystem.not_embeds_An_E₆
#print axioms LineSystem.not_embeds_Dn_E₆
#print axioms LineSystem.not_embeds_Dn_E₇
#print axioms Computations.C5.inclusions_and_obstructions
-- C6: the coordinate frame matrices
#print axioms Computations.C6.an_frame_matrix
#print axioms Computations.C6.dn_frame_matrix
#print axioms Computations.C6.e₈viaA₈_frame_matrix
#print axioms Computations.C6.e₈_frame_matrix
#print axioms Computations.C6.e₈viaSteiner_frame_matrix
#print axioms Computations.C6.e₇_frame_matrix
#print axioms Computations.C6.e₆_frame_matrix
#print axioms Computations.C6.coordinate_frame_matrices
-- C6: frames within the span
#print axioms LineSystem.isFrame_iff_gram
#print axioms LineSystem.Iso.isFrame
#print axioms LineSystem.Signing.frameSum_eq
#print axioms LineSystem.IntegerModel.frameSum_apply
#print axioms LineSystem.isFrame_An
#print axioms LineSystem.isFrame_Dn
#print axioms LineSystem.isFrame_E₈
#print axioms LineSystem.isFrame_E₈viaA₈
#print axioms LineSystem.isFrame_E₈viaSteiner
#print axioms LineSystem.isFrame_E₇
#print axioms LineSystem.isFrame_E₆
#print axioms LineSystem.RootType.finrank_span_model
#print axioms LineSystem.RootType.numLines_model
#print axioms LineSystem.RootType.isFrame_model
#print axioms LineSystem.frame_identity
#print axioms LineSystem.frame_identity_span
#print axioms LineSystem.frame_identity_signing
-- Theorem 3.7
#print axioms LineSystem.gram_mul_self_of_frame
#print axioms LineSystem.signedAdj_quadratic_of_frame
#print axioms LineSystem.signedAdj_quadratic
#print axioms LineSystem.signedAdj_quadratic_An
#print axioms LineSystem.signedAdj_quadratic_Dn
#print axioms LineSystem.signedAdj_quadratic_E₈
#print axioms LineSystem.signedAdj_quadratic_E₇
#print axioms LineSystem.signedAdj_quadratic_E₆
#print axioms LineSystem.signedAdj_quadratic_E₈viaA₈
#print axioms LineSystem.signedAdj_quadratic_E₈viaSteiner

#print axioms LineSystem.nonempty_signing
