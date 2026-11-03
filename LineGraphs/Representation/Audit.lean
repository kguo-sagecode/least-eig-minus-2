/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.Lines
import LineGraphs.Representation.TypeA
import LineGraphs.Representation.GeneralizedRepresentation
import LineGraphs.Representation.TypeDPairs
import LineGraphs.Representation.TypeDNormalForm
import LineGraphs.Representation.RootType
import LineGraphs.Representation.SymmetricSquare
import LineGraphs.Representation.Valency
import LineGraphs.Representation.Integer
import LineGraphs.Representation.Switching
import LineGraphs.Representation.Switch
import LineGraphs.Computations.C7
import LineGraphs.Computations.C8
import LineGraphs.Computations.C9
import LineGraphs.Computations.C10
import LineGraphs.Computations.C24
import LineGraphs.Representation.Theorem44
import LineGraphs.Representation.Theorem44Unconditional
import LineGraphs.Spectral.RelativeBoundFourteen
import LineGraphs.Representation.Remarks

/-!
# Axiom audit for the Section 4 representation modules

Every theorem added in these modules is checked below, along with the definitions carrying
proofs and the local adjacency instances. The coverage includes the representation interface,
Theorems 4.1--4.4, the classification adapters, EQ1 and EQ2, the remarks after Theorems 4.1,
4.2 and 4.4, and computations C7--C10 and C24. Theorems 3.5 and 3.6 supply classification
for the unconditional root-type transport, EQ2 and Theorem 4.4 bounds.
-/

#print axioms SimpleGraph.innerGraph
#print axioms SimpleGraph.representedGraph
#print axioms SimpleGraph.IsRepresentedIn
#print axioms SimpleGraph.IsRepresentation.lineSystem
#print axioms SimpleGraph.lineGraphVector
#print axioms SimpleGraph.cocktailParty
#print axioms SimpleGraph.generalizedLineGraph
#print axioms SimpleGraph.IsGeneralizedLineGraph
#print axioms SimpleGraph.generalizedLineGraphCenter
#print axioms SimpleGraph.generalizedLineGraphPetal
#print axioms SimpleGraph.generalizedLineGraphVector
#print axioms SimpleGraph.representationPairs

#print axioms SimpleGraph.isRepresentation_iff
#print axioms SimpleGraph.IsRepresentation.inner_self
#print axioms SimpleGraph.IsRepresentation.inner_of_adj
#print axioms SimpleGraph.IsRepresentation.inner_of_not_adj
#print axioms SimpleGraph.IsRepresentation.inner_eq_zero_or_one
#print axioms SimpleGraph.IsRepresentation.inner_nonneg
#print axioms SimpleGraph.IsRepresentation.injective
#print axioms SimpleGraph.IsRepresentation.ne_neg
#print axioms SimpleGraph.IsRepresentation.adj_iff
#print axioms SimpleGraph.IsRepresentation.representedGraph_eq
#print axioms SimpleGraph.isRepresentation_representedGraph
#print axioms SimpleGraph.IsRepresentation.induce
#print axioms SimpleGraph.IsRepresentation.comp_iso
#print axioms SimpleGraph.IsRepresentation.of_isometricInclusion
#print axioms SimpleGraph.IsRepresentedIn.of_isometricInclusion
#print axioms SimpleGraph.IsRepresentedIn.mono
#print axioms SimpleGraph.IsRepresentedIn.of_iso
#print axioms SimpleGraph.IsRepresentedIn.induce
#print axioms SimpleGraph.IsRepresentedIn.comp_iso
#print axioms SimpleGraph.IsRepresentation.numLines_lineSystem
#print axioms SimpleGraph.IsRepresentation.span_lineSystem
#print axioms SimpleGraph.IsRepresentation.isRepresentedIn_lineSystem
#print axioms SimpleGraph.IsRepresentation.isIndecomposable_of_connected
#print axioms SimpleGraph.lineGraphVector_mk
#print axioms SimpleGraph.lineGraph_isRepresentation
#print axioms EuclideanSpace.inner_sub_single_sub_single
#print axioms LineSystem.An.mem_iff_exists_sub_single
#print axioms SimpleGraph.IsRepresentedIn.nonempty_iso_lineGraph_of_An
#print axioms SimpleGraph.IsBipartite.lineGraph_isRepresentedIn_An
#print axioms SimpleGraph.isRepresentedIn_An_iff
#print axioms SimpleGraph.generalizedLineGraphCenter_injective
#print axioms SimpleGraph.generalizedLineGraphCenter_ne_petal
#print axioms SimpleGraph.generalizedLineGraphPetal_injective
#print axioms SimpleGraph.inner_generalizedLineGraphVector_edges
#print axioms SimpleGraph.generalizedLineGraph_isRepresentation
#print axioms SimpleGraph.generalizedLineGraph_isRepresentedIn_Dn
#print axioms SimpleGraph.IsGeneralizedLineGraph.exists_isRepresentedIn_Dn
#print axioms LineSystem.Dn.mem_iff_exists_signed_single
#print axioms LineSystem.Dn.apply_eq_zero_or_one_or_neg_one
#print axioms LineSystem.Dn.exists_signed_single_of_apply_ne_zero
#print axioms SimpleGraph.IsRepresentation.exists_pair_of_opposite_coordinates
#print axioms SimpleGraph.IsRepresentation.eq_or_eq_of_petal_ne_zero
#print axioms SimpleGraph.IsRepresentation.apply_ne_zero_iff_of_pair
#print axioms SimpleGraph.IsRepresentation.pair_eq_of_common_petal
#print axioms SimpleGraph.IsRepresentation.eq_or_eq_of_support_eq
#print axioms SimpleGraph.IsRepresentation.existsUnique_partner_of_support_eq
#print axioms SimpleGraph.IsRepresentation.pairwise_disjoint_representationPairs
#print axioms SimpleGraph.IsRepresentation.existsUnique_maximal_representationPairs

#print axioms EuclideanSpace.signChange
#print axioms EuclideanSpace.signChange_apply
#print axioms EuclideanSpace.signChange_mem_Dn
#print axioms SimpleGraph.representationPetals
#print axioms SimpleGraph.IsRepresentation.not_mem_representationPetals_of_pair
#print axioms SimpleGraph.IsRepresentation.exists_signChange_nonneg
#print axioms SimpleGraph.representationPetals_signChange
#print axioms SimpleGraph.IsRepresentation.exists_center_map
#print axioms SimpleGraph.generalizedLineGraphCoordinateEquiv
#print axioms SimpleGraph.exists_coordinate_partition
#print axioms SimpleGraph.IsRepresentation.exists_iso_of_range_eq
#print axioms SimpleGraph.IsRepresentation.exists_generalizedLineGraph_normal_form
#print axioms SimpleGraph.IsRepresentation.exists_normal_form_Dn
#print axioms SimpleGraph.isRepresentedIn_Dn_iff
#print axioms SimpleGraph.IsRepresentedIn.isGeneralizedLineGraph_of_Dn
#print axioms SimpleGraph.IsRepresentation.exists_isRepresentedIn_rootType_of_classification
#print axioms EuclideanSpace.SymSqIndex
#print axioms EuclideanSpace.symSq
#print axioms EuclideanSpace.inner_symSq
#print axioms SimpleGraph.IsRepresentation.linearIndependent_symSq
#print axioms SimpleGraph.IsRepresentedIn.card_le_36
#print axioms SimpleGraph.IsRepresentedIn.degree_le_of_card_N_le
#print axioms SimpleGraph.IsRepresentedIn.degree_le_28
#print axioms Computations.tableVector
#print axioms SimpleGraph.integerGraph
#print axioms SimpleGraph.integerGraph_isRepresentation
#print axioms SimpleGraph.integerGraph_isSRGWith_of_check
#print axioms SimpleGraph.isSwitchingEquivalent_of_integer_certificate
#print axioms Computations.C7.graph
#print axioms Computations.C7.norms_checked
#print axioms Computations.C7.products_checked
#print axioms Computations.C7.roots_checked
#print axioms Computations.C7.isRepresentedIn_E₈viaA₈
#print axioms Computations.C7.isRepresentedIn_E₈
#print axioms Computations.C7.degree_zero
#print axioms SimpleGraph.exists_isRepresentedIn_E₈_card_36
#print axioms Computations.C7.roots
#print axioms Computations.C7.vectors
#print axioms Computations.C8.quadratic_checked
#print axioms Computations.C8.quadratic_bound
#print axioms SimpleGraph.changI
#print axioms SimpleGraph.changI_norms_checked
#print axioms SimpleGraph.changI_products_checked
#print axioms SimpleGraph.changI_roots_checked
#print axioms SimpleGraph.changI_isRepresentedIn_E₈
#print axioms SimpleGraph.changI_isSRGWith
#print axioms SimpleGraph.changII
#print axioms SimpleGraph.changII_norms_checked
#print axioms SimpleGraph.changII_products_checked
#print axioms SimpleGraph.changII_roots_checked
#print axioms SimpleGraph.changII_isRepresentedIn_E₈
#print axioms SimpleGraph.changII_isSRGWith
#print axioms SimpleGraph.changIII
#print axioms SimpleGraph.changIII_norms_checked
#print axioms SimpleGraph.changIII_products_checked
#print axioms SimpleGraph.changIII_roots_checked
#print axioms SimpleGraph.changIII_isRepresentedIn_E₈
#print axioms SimpleGraph.changIII_isSRGWith
#print axioms SimpleGraph.clebsch
#print axioms SimpleGraph.clebsch_norms_checked
#print axioms SimpleGraph.clebsch_products_checked
#print axioms SimpleGraph.clebsch_roots_checked
#print axioms SimpleGraph.clebsch_isRepresentedIn_E₈
#print axioms SimpleGraph.clebsch_isSRGWith
#print axioms Computations.C9.changIRoots
#print axioms Computations.C9.changIVectors
#print axioms Computations.C9.changIAdj
#print axioms Computations.C9.changIIRoots
#print axioms Computations.C9.changIIVectors
#print axioms Computations.C9.changIIAdj
#print axioms Computations.C9.changIIIRoots
#print axioms Computations.C9.changIIIVectors
#print axioms Computations.C9.changIIIAdj
#print axioms Computations.C9.schlafliRoots
#print axioms Computations.C9.schlafliVectors
#print axioms Computations.C9.schlafliAdj
#print axioms Computations.C9.shrikhandeRoots
#print axioms Computations.C9.shrikhandeVectors
#print axioms Computations.C9.shrikhandeAdj
#print axioms Computations.C9.clebschRoots
#print axioms Computations.C9.clebschVectors
#print axioms Computations.C9.clebschAdj
#print axioms Computations.C9.petersenRoots
#print axioms Computations.C9.petersenVectors
#print axioms Computations.C9.petersenAdj
#print axioms SimpleGraph.clebsch.subsetLabel
#print axioms SimpleGraph.clebsch.even_subsetLabel
#print axioms SimpleGraph.clebsch.foldedFiveCubeLabel
#print axioms SimpleGraph.clebsch.foldedFiveCubeComplIso
#print axioms SimpleGraph.foldedFiveCube_isSRGWith
#print axioms SimpleGraph.schlafli.gq24Label
#print axioms SimpleGraph.schlafli.gq24ComplIso
#print axioms SimpleGraph.gq24_isSRGWith
#print axioms SimpleGraph.foldedFiveCube
#print axioms SimpleGraph.gq24
#print axioms SimpleGraph.compl_foldedFiveCube_adj_iff
#print axioms SimpleGraph.compl_gq24_adj_iff
#print axioms SimpleGraph.petersen
#print axioms SimpleGraph.petersen_norms_checked
#print axioms SimpleGraph.petersen_products_checked
#print axioms SimpleGraph.petersen_roots_checked
#print axioms SimpleGraph.petersen_isRepresentedIn_E₈
#print axioms SimpleGraph.petersen_isSRGWith
#print axioms SimpleGraph.petersen.kneserGraph
#print axioms SimpleGraph.petersen.kneserLabel
#print axioms SimpleGraph.petersen.kneserIso
#print axioms SimpleGraph.schlafli
#print axioms SimpleGraph.schlafli_norms_checked
#print axioms SimpleGraph.schlafli_products_checked
#print axioms SimpleGraph.schlafli_roots_checked
#print axioms SimpleGraph.schlafli_isRepresentedIn_E₈
#print axioms SimpleGraph.schlafli_isSRGWith
#print axioms SimpleGraph.shrikhande
#print axioms SimpleGraph.shrikhande_norms_checked
#print axioms SimpleGraph.shrikhande_products_checked
#print axioms SimpleGraph.shrikhande_roots_checked
#print axioms SimpleGraph.shrikhande_isRepresentedIn_E₈
#print axioms SimpleGraph.shrikhande_isSRGWith
#print axioms SimpleGraph.clebsch.shrikhandeSigns
#print axioms SimpleGraph.clebsch_isSwitchingEquivalent_shrikhande
#print axioms SimpleGraph.clebsch.bipartiteSigns
#print axioms SimpleGraph.clebsch.bipartiteEdgeEquiv
#print axioms SimpleGraph.clebsch_isSwitchingEquivalent_lineGraph_completeBipartite
#print axioms SimpleGraph.degree_eq_sum_indicator
#print axioms SimpleGraph.card_incident_edge_subtype
#print axioms SimpleGraph.lineGraph_degree_mk
#print axioms SimpleGraph.generalizedLineGraph_degree_petal
#print axioms SimpleGraph.generalizedLineGraph_degree_edge

-- Theorem 4.4, C24, and the remarks after Theorems 4.1, 4.2 and 4.4
#print axioms Computations.C24.sum_sq_row
#print axioms Computations.C24.trace_sq_gt
#print axioms Matrix.IsHermitian.trace_le_rank_mul_of_eigenvalues_le
#print axioms Matrix.IsHermitian.trace_sq_le_rank_mul_sum_entry_sq
#print axioms Matrix.PosSemidef.rank_add_allOnes_of_pos
#print axioms SimpleGraph.centeredMatrix
#print axioms SimpleGraph.equiangularMatrix
#print axioms SimpleGraph.IsRegularOfDegree.gram_mulVec_one
open private SimpleGraph.centered_eq_smul SimpleGraph.equiangular_psd_rank from
  LineGraphs.Representation.Theorem44
#print axioms SimpleGraph.centered_eq_smul
#print axioms SimpleGraph.equiangular_psd_rank
#print axioms SimpleGraph.IsRegularOfDegree.posSemidef_centered
#print axioms SimpleGraph.IsRegularOfDegree.rank_centered
#print axioms SimpleGraph.IsRegularOfDegree.posSemidef_equiangular
#print axioms SimpleGraph.IsRegularOfDegree.rank_equiangular
#print axioms InnerProductSpace.card_le_relativeBound
#print axioms InnerProductSpace.card_le_fourteen_of_finrank_eq_eight_of_classification
#print axioms SimpleGraph.IsRepresentedIn.posSemidef_two_add_adjMatrix_and_rank_le_eight
#print axioms SimpleGraph.IsRepresentedIn.exists_gram_centered
#print axioms SimpleGraph.gram_symSq_centered
#print axioms SimpleGraph.IsRepresentedIn.card_le_28_of_regular_of_two_mul_degree_add_four_le
#print axioms SimpleGraph.norm_eq_one_and_inner_eq_of_gram_eq_equiangularMatrix
#print axioms SimpleGraph.IsRepresentedIn.rank_le_seven_of_regular_of_classification
#print axioms SimpleGraph.IsRepresentedIn.card_le_28_of_regular_of_classification
#print axioms SimpleGraph.IsRegularOfDegree.centered_mulVec_one
#print axioms SimpleGraph.trace_centered
#print axioms SimpleGraph.IsRepresentedIn.centered_trace_bound_of_regular
#print axioms SimpleGraph.not_regular_28_17_of_rank_le_seven
#print axioms SimpleGraph.IsRepresentedIn.degree_le_16_of_regular_of_classification
#print axioms SimpleGraph.not_regular_28_16_isRepresentedIn_E₈_of_classification
#print axioms SimpleGraph.decidableAdjExamples
#print axioms SimpleGraph.regular_28_12_and_27_16_isRepresentedIn_E₈
#print axioms LineSystem.decidableAdjNonnegSubset
#print axioms LineSystem.IsNonnegSubset
#print axioms LineSystem.IsNonnegSubset.isRepresentation
#print axioms LineSystem.mem_of_maximal_nonnegSubset
#print axioms LineSystem.An.sigmaP
#print axioms LineSystem.An.inner_sigmaP
#print axioms LineSystem.An.isNonnegSubset_sigmaP
#print axioms LineSystem.An.exists_subset_sigmaP
#print axioms LineSystem.An.sigmaP_injective
#print axioms LineSystem.An.card_sigmaP
#print axioms LineSystem.An.card_nonneg_subset_le
#print axioms LineSystem.An.maximal_sigmaP
#print axioms LineSystem.An.nonneg_subset_maximal_iff
#print axioms LineSystem.An.exists_nonneg_subset_card_eq
#print axioms LineSystem.An.isRepresentation_lineGraph_completeBipartite_sigmaP
open private LineSystem.Dn.inner_centers_nonneg from LineGraphs.Representation.Remarks
#print axioms LineSystem.Dn.inner_centers_nonneg
#print axioms LineSystem.Dn.exists_isRepresentation_generalizedLineGraph_top_of_maximal
#print axioms LineSystem.Dn.card_nonneg_subset_le
#print axioms LineSystem.Dn.exists_nonneg_subset_card_eq

#print axioms SimpleGraph.IsRepresentedIn.card_le_28_of_regular
#print axioms SimpleGraph.IsRepresentedIn.degree_le_16_of_regular
#print axioms SimpleGraph.not_regular_28_16_isRepresentedIn_E₈
#print axioms InnerProductSpace.card_le_fourteen_of_finrank_eq_eight

-- lem:4-switch (Section 4) and lem:cycle (Section 5)
#print axioms SimpleGraph.IsRepresentation.switch
#print axioms SimpleGraph.nonempty_iso_cycleGraph
