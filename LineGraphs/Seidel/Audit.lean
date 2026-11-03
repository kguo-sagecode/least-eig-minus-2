/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.Switching
import LineGraphs.Seidel.Parameters
import LineGraphs.Seidel.CocktailParty
import LineGraphs.Seidel.Schlafli
import LineGraphs.Seidel.Clebsch
import LineGraphs.Seidel.LineGraph
import LineGraphs.Seidel.SwitchingDegrees
import LineGraphs.Seidel.TwoRegular
import LineGraphs.Seidel.EightRegular
import LineGraphs.Seidel.CubicEight
import LineGraphs.Seidel.EightInvariants
import LineGraphs.Computations.C18
import LineGraphs.Seidel.Classification

/-!
# Axiom audit for Remark 4.14

The results in `LineGraphs/Seidel/`, C18 and C22 are listed below, including the
classification and its supporting definitions. Only the standard Lean axioms are used.
-/

#print axioms SimpleGraph.switch
#print axioms SimpleGraph.decidableAdjSwitch
#print axioms SimpleGraph.switch_adj
#print axioms SimpleGraph.switch_compl
#print axioms SimpleGraph.Iso.switch
#print axioms SimpleGraph.Iso.lineGraphSwitch
#print axioms SimpleGraph.Iso.compl
#print axioms SimpleGraph.IsSRGWith.of_iso
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_of_injective_hom
#print axioms Matrix.mul_rank_sub_one_eq_of_quadratic
#print axioms SimpleGraph.IsSRGWith.exists_adjMatrix_mulVec_eq_neg_two
#print axioms SimpleGraph.IsSRGWith.linear_relation_of_det_two_add_adjMatrix_eq_zero
#print axioms SimpleGraph.IsSRGWith.ne_bot_and_ne_top_of_det_two_add_adjMatrix_eq_zero
#print axioms SimpleGraph.IsSRGWith.pos_of_connected_of_ne_top
#print axioms SimpleGraph.IsSRGWith.params_of_det_two_add_adjMatrix_eq_zero
#print axioms SimpleGraph.IsSRGWith.rank_two_add_adjMatrix_of_det_eq_zero
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_cocktailParty
#print axioms Computations.C18.parameters
#print axioms Computations.C18.checkParameters
#print axioms Computations.C18.checkParameters_sound
#print axioms Computations.C18.checkParameters_eq_true
#print axioms Computations.C18.srg_parameters
#print axioms SimpleGraph.IsSRGWith.hasTriangleProperty
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_gq24
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_schlafli
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_foldedFiveCube
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_clebsch
#print axioms SimpleGraph.foldedFiveCube_isSRGWith
#print axioms SimpleGraph.gq24_isSRGWith

#print axioms SimpleGraph.lineGraph_adj_mk_iff
#print axioms SimpleGraph.lineGraphCountsDecidableAdj
#print axioms SimpleGraph.lineGraphCasesDecidableAdj
#print axioms SimpleGraph.lineGraphClassificationDecidableAdj
#print axioms SimpleGraph.switchingDegreesDecidableAdj
#print axioms SimpleGraph.card_commonNeighbors_lineGraph_of_adj
#print axioms SimpleGraph.card_commonNeighbors_lineGraph_of_disjoint
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_of_injective_hom_of_connected
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_cycle
#print axioms SimpleGraph.Connected.eq_top_of_adj_of_common_neighbor
#print axioms SimpleGraph.nonempty_iso_completeBipartite_of_adj_iff
#print axioms SimpleGraph.Connected.nonempty_iso_completeBipartite_of_neighbor_degree_one
#print axioms SimpleGraph.IsSRGWith.degree_sub_two_add_eq_of_lineGraph
#print axioms SimpleGraph.IsSRGWith.eq_top_of_lineGraph_of_triangle
#print axioms SimpleGraph.IsSRGWith.nonadjacent_param_le_two_of_lineGraph
#print axioms SimpleGraph.IsRegularOfDegree.exists_disjoint_edge_of_triangle_free
#print axioms SimpleGraph.IsSRGWith.nonadjacent_param_eq_two_of_lineGraph
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_completeBipartite_of_lineGraph
#print axioms SimpleGraph.lineGraph_isSRGWith_cases
#print axioms SimpleGraph.lineGraphInduceSupportIso
#print axioms SimpleGraph.lineGraph_completeBipartiteGraph_eq_top
#print axioms
  SimpleGraph.IsSRGWith.nonempty_iso_lineGraph_complete_or_completeBipartite_of_connected
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_lineGraph_complete_or_completeBipartite
#print axioms SimpleGraph.edgeFinsetWithin
#print axioms SimpleGraph.mem_edgeFinsetWithin
#print axioms SimpleGraph.card_edgeFinsetWithin_of_isClique
#print axioms SimpleGraph.card_filter_edgeFinsetWithin_mem_of_isClique
#print axioms SimpleGraph.card_adj_switch
#print axioms SimpleGraph.card_filter_adj_lineGraph
#print axioms SimpleGraph.card_adj_lineGraph_switch_of_complete
#print axioms Finset.two_mul_eq_of_forall_add_eq
#print axioms SimpleGraph.IsRegularOfDegree.connected_of_card_lt_two_mul
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_cycle_of_card_lt_six
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_cycle_of_two_of_card_eq_five
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_sum_cycles_of_not_connected
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_of_two_of_card_eq_six
#print axioms SimpleGraph.decidableAdjSum
#print axioms SimpleGraph.fourK2
#print axioms SimpleGraph.cycleThreeFive
#print axioms SimpleGraph.twoC4
#print axioms SimpleGraph.twoK4
#print axioms SimpleGraph.cycleWithChords
#print axioms SimpleGraph.cubeGraph
#print axioms SimpleGraph.wagnerGraph
#print axioms SimpleGraph.truncatedK33Graph
#print axioms SimpleGraph.twiceTruncatedK4Graph
#print axioms SimpleGraph.twoDiamondsGraph
#print axioms SimpleGraph.fourK2.cocktailPartyComplIso
#print axioms SimpleGraph.cycleThreeFive.sumIso
#print axioms SimpleGraph.twoC4.sumIso
#print axioms SimpleGraph.fourK2_isRegularOfDegree
#print axioms SimpleGraph.cycleThreeFive_isRegularOfDegree
#print axioms SimpleGraph.twoC4_isRegularOfDegree
#print axioms SimpleGraph.twoK4_isRegularOfDegree
#print axioms SimpleGraph.cubeGraph_isRegularOfDegree
#print axioms SimpleGraph.wagnerGraph_isRegularOfDegree
#print axioms SimpleGraph.truncatedK33Graph_isRegularOfDegree
#print axioms SimpleGraph.twiceTruncatedK4Graph_isRegularOfDegree
#print axioms SimpleGraph.twoDiamondsGraph_isRegularOfDegree
#print axioms SimpleGraph.IsRegularOfDegree.eq_bot_of_zero
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_fourK2
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_of_two_of_card_eq_eight

-- The cubic classification and separating invariants of SE4.
#print axioms SimpleGraph.CubicEight.Rows
#print axioms SimpleGraph.CubicEight.model
#print axioms SimpleGraph.CubicEight.lowerNeighbors
#print axioms SimpleGraph.CubicEight.rowChoices
#print axioms SimpleGraph.CubicEight.neighborFinset_mem_rowChoices
#print axioms SimpleGraph.CubicEight.compatible
#print axioms SimpleGraph.CubicEight.checkCompletions
#print axioms SimpleGraph.CubicEight.checkCompletions_sound
#print axioms SimpleGraph.CubicEight.initialRows
#print axioms SimpleGraph.CubicEight.checkCompletions_initial_sound
#print axioms SimpleGraph.CubicEight.certificate
#print axioms SimpleGraph.CubicEight.modelMask
#print axioms SimpleGraph.CubicEight.modelMask_adj
#print axioms SimpleGraph.CubicEight.rowKey
#print axioms SimpleGraph.CubicEight.checkCertificate
#print axioms SimpleGraph.CubicEight.nonempty_iso_of_checkCertificate
#print axioms SimpleGraph.CubicEight.check_completions_023
#print axioms SimpleGraph.CubicEight.check_completions_024
#print axioms SimpleGraph.CubicEight.check_completions_025
#print axioms SimpleGraph.CubicEight.check_completions_026
#print axioms SimpleGraph.CubicEight.check_completions_027
#print axioms SimpleGraph.CubicEight.check_completions_034
#print axioms SimpleGraph.CubicEight.check_completions_035
#print axioms SimpleGraph.CubicEight.check_completions_036
#print axioms SimpleGraph.CubicEight.check_completions_037
#print axioms SimpleGraph.CubicEight.check_completions_045
#print axioms SimpleGraph.CubicEight.check_completions_046
#print axioms SimpleGraph.CubicEight.check_completions_047
#print axioms SimpleGraph.CubicEight.check_completions_056
#print axioms SimpleGraph.CubicEight.check_completions_057
#print axioms SimpleGraph.CubicEight.check_completions_067
#print axioms SimpleGraph.CubicEight.checkCompletions_eq_true
#print axioms SimpleGraph.CubicEight.nonempty_iso_of_neighborFinset_zero
#print axioms SimpleGraph.CubicEight.exists_iso_neighborFinset_zero
#print axioms SimpleGraph.IsRegularOfDegree.nonempty_iso_of_three_of_card_eq_eight
#print axioms SimpleGraph.numFourCycles
#print axioms SimpleGraph.Iso.numFourCycles_eq
#print axioms SimpleGraph.Iso.card_cliqueFinset_eq
#print axioms SimpleGraph.two_regular_eight_invariants
#print axioms SimpleGraph.cubic_eight_invariants
#print axioms SimpleGraph.cubic_eight_pairwise_not_iso
#print axioms SimpleGraph.two_regular_eight_pairwise_not_iso


-- LineGraphs/Seidel/AddOneRegular.lean
#print axioms SimpleGraph.addOneRegularDecidableAdj
#print axioms SimpleGraph.switchTriangularAddOne_adj_inl
#print axioms SimpleGraph.switchTriangularAddOne_adj_inr
#print axioms SimpleGraph.degree_switchTriangularAddOne_inl
#print axioms SimpleGraph.degree_switchTriangularAddOne_inr
#print axioms SimpleGraph.isRegularOfDegree_two_of_switchTriangularAddOne_six

-- LineGraphs/Seidel/AddOneSwitching.lean
#print axioms SimpleGraph.Iso.switchTriangularAddOne
#print axioms SimpleGraph.switchTriangularAddOne_triangularSwitchingGraph
#print axioms
  SimpleGraph.nonempty_iso_shrikhande_or_lineGraph_completeBipartite_of_switch_triangular6AddOne

-- LineGraphs/Seidel/Apex.lean
#print axioms SimpleGraph.IsRepresentation.apex
#print axioms SimpleGraph.IsRepresentation.sum_inner_eq_degree_add_two
#print axioms SimpleGraph.IsRepresentation.inner_apex
#print axioms SimpleGraph.IsRepresentation.inner_apex_self
#print axioms SimpleGraph.IsRepresentation.inner_apex_mem_int
#print axioms SimpleGraph.IsRepresentation.apex_mem_span

-- LineGraphs/Seidel/ApexGraphs.lean
#print axioms SimpleGraph.apexGraph6
#print axioms SimpleGraph.apexGraph6DecidableAdj
#print axioms SimpleGraph.apexGraph7
#print axioms SimpleGraph.apexGraph7DecidableAdj
#print axioms SimpleGraph.apexGraph6Edge
#print axioms SimpleGraph.apexGraph6Edge_bijective
#print axioms SimpleGraph.apexGraph6EdgeEquiv
#print axioms SimpleGraph.apexGraph7Edge
#print axioms SimpleGraph.apexGraph7Edge_bijective
#print axioms SimpleGraph.apexGraph7EdgeEquiv
#print axioms SimpleGraph.apexPair5
#print axioms SimpleGraph.apexPair5_bijective
#print axioms SimpleGraph.apexSumPair6
#print axioms SimpleGraph.apexSumPair6_bijective
#print axioms SimpleGraph.triangularAddOne_adj_sumPair
#print axioms SimpleGraph.apexGraph6LineIso
#print axioms SimpleGraph.apexGraph7LineIso

-- LineGraphs/Seidel/Classification.lean
#print axioms SimpleGraph.IsSRGWith.nonempty_iso_seidelSeven
#print axioms SimpleGraph.seidel_seven_classification
#print axioms SimpleGraph.seidel_seven

-- LineGraphs/Seidel/ClassificationParameters.lean
#print axioms SimpleGraph.IsSRGWith.parameters_mem_small_list
#print axioms SimpleGraph.IsRepresentation.nonempty_iso_exceptional_of_latticeRoots

-- LineGraphs/Seidel/ExceptionalSwitching.lean
#print axioms SimpleGraph.inner_c_lineGraphVector
#print axioms SimpleGraph.E₆_apex_pairs
#print axioms SimpleGraph.E₇_apex_pairs
#print axioms SimpleGraph.E₈_apex_pairs
#print axioms SimpleGraph.IsRepresentation.nonempty_iso_petersen_of_latticeRoots
#print axioms SimpleGraph.IsRepresentation.nonempty_iso_shrikhande_or_lattice_of_latticeRoots
#print axioms SimpleGraph.IsRepresentation.nonempty_iso_triangular_or_chang_of_latticeRoots

-- LineGraphs/Seidel/FamilyParameters.lean
#print axioms SimpleGraph.card_completeGraph_edgeSet
#print axioms SimpleGraph.card_completeBipartiteGraph_edgeSet
#print axioms SimpleGraph.lineGraph_completeGraph_isRegularOfDegree
#print axioms SimpleGraph.completeBipartiteGraph_isRegularOfDegree
#print axioms SimpleGraph.lineGraph_completeBipartiteGraph_isRegularOfDegree
#print axioms SimpleGraph.cocktailParty_isRegularOfDegree
#print axioms SimpleGraph.Iso.regular_degree_eq

-- LineGraphs/Seidel/Integrality.lean
#print axioms InnerProductSpace.det_gram_mul_inner_self_mem_int

-- LineGraphs/Seidel/LatticeIntegrality.lean
#print axioms LineSystem.inner_mem_int
#print axioms SimpleGraph.IsRepresentation.det_gram_mul_apex_mem_int
#print axioms SimpleGraph.IsRepresentation.three_mul_apex_mem_int_of_E₆
#print axioms SimpleGraph.IsRepresentation.two_mul_apex_mem_int_of_E₇

-- LineGraphs/Seidel/LatticeRoots.lean
#print axioms SimpleGraph.IsRepresentation.inner_mem_int
#print axioms SimpleGraph.IsRepresentation.inner_mem_int_of_mem_span_int
#print axioms SimpleGraph.mem_span_real_of_mem_span_int
#print axioms SimpleGraph.inner_mem_five_of_mem_int
#print axioms SimpleGraph.IsRepresentation.finite_latticeRoots
#print axioms SimpleGraph.IsRepresentation.latticeRoots
#print axioms SimpleGraph.IsRepresentation.mem_latticeRoots
#print axioms SimpleGraph.IsRepresentation.isStarClosed_latticeRoots
#print axioms SimpleGraph.IsRepresentation.span_latticeRoots
#print axioms SimpleGraph.IsRepresentation.isIndecomposable_latticeRoots
#print axioms SimpleGraph.IsRepresentation.latticeRoots_nonempty
#print axioms SimpleGraph.IsRepresentation.isRepresentedIn_latticeRoots

-- LineGraphs/Seidel/RootTransitivity.lean
#print axioms LineSystem.IsIndecomposable.exists_inner_eq_neg_one
#print axioms LineSystem.exists_isometry_apply_eq_of_star_transitivity
#print axioms LineSystem.E₆.exists_isometry_apply_eq_c
#print axioms LineSystem.E₇.exists_isometry_apply_eq_c
#print axioms LineSystem.E₈.exists_isometry_apply_eq_c

-- LineGraphs/Seidel/Seven.lean
#print axioms SimpleGraph.seidelSeven_not_iso_lineGraph_complete
#print axioms SimpleGraph.seidelSeven_not_iso_lineGraph_completeBipartite
#print axioms SimpleGraph.seidelSeven_not_iso_cocktailParty
#print axioms SimpleGraph.seidel_seven_properties

-- LineGraphs/Seidel/SevenDistinct.lean
#print axioms SimpleGraph.changI_not_iso_triangular8
#print axioms SimpleGraph.changII_not_iso_triangular8
#print axioms SimpleGraph.changIII_not_iso_triangular8
#print axioms SimpleGraph.changI_not_iso_changII
#print axioms SimpleGraph.changI_not_iso_changIII
#print axioms SimpleGraph.changII_not_iso_changIII
#print axioms SimpleGraph.shrikhande_not_iso_lineGraph_completeBipartite_four
#print axioms SimpleGraph.seidel_seven_pairwise_not_iso

-- LineGraphs/Seidel/SevenModels.lean
#print axioms SimpleGraph.seidelSeven
#print axioms SimpleGraph.seidelSevenParameters
#print axioms SimpleGraph.seidelSevenDecidableAdj
#print axioms SimpleGraph.seidelSevenNonempty
#print axioms SimpleGraph.seidelSeven_isSRGWith
#print axioms SimpleGraph.seidelSeven_isRepresentedIn_E₈
#print axioms SimpleGraph.IsSRGWith.connected_of_pos
#print axioms SimpleGraph.seidelSeven_connected
#print axioms SimpleGraph.seidelSeven_leastEigenvalue

-- LineGraphs/Seidel/SwitchingModels.lean
#print axioms SimpleGraph.switchTriangular
#print axioms SimpleGraph.triangularAddOne
#print axioms SimpleGraph.switchTriangularAddOne
#print axioms SimpleGraph.twoC3
#print axioms SimpleGraph.twoC3.sumIso
#print axioms SimpleGraph.switchTriangular_adj
#print axioms SimpleGraph.switchTriangular_bot

-- LineGraphs/Seidel/SwitchingRegular.lean
#print axioms SimpleGraph.switchingRegularDecidableAdj
#print axioms SimpleGraph.card_filter_top_edges
#print axioms SimpleGraph.card_filter_top_edges_incident
#print axioms SimpleGraph.degree_switchTriangular
#print axioms SimpleGraph.isRegularOfDegree_two_of_switchTriangular_five
#print axioms SimpleGraph.exists_isRegularOfDegree_of_switchTriangular_eight

-- LineGraphs/Seidel/SwitchingTransport.lean
#print axioms SimpleGraph.Iso.switchTriangular
#print axioms SimpleGraph.switchTriangular_compl
#print axioms SimpleGraph.triangularSwitchingGraph
#print axioms SimpleGraph.mem_edgeSet_triangularSwitchingGraph
#print axioms SimpleGraph.switchTriangular_triangularSwitchingGraph

-- LineGraphs/Seidel/Transversal.lean
#print axioms SimpleGraph.IsRepresentation.apex_mem_latticeRoots
#print axioms SimpleGraph.IsRepresentation.nonempty_iso_switch_of_pairs
#print axioms SimpleGraph.IsRepresentation.nonempty_iso_lineGraph_switch

-- LineGraphs/Seidel/TriangularSwitching.lean
#print axioms SimpleGraph.nonempty_iso_petersen_of_switch_triangular5
#print axioms SimpleGraph.nonempty_iso_triangular8_or_chang_of_degree_le_three
#print axioms SimpleGraph.nonempty_iso_triangular8_or_chang_of_regular_switchTriangular
#print axioms SimpleGraph.nonempty_iso_triangular8_or_chang_of_switch_triangular8

-- LineGraphs/Computations/C22BipartiteModel.lean
#print axioms Computations.C22.lattice44_adjacency
#print axioms Computations.C22.lattice44TableIso
#print axioms Computations.C22.cliqueCount_lineGraph_completeBipartite

-- LineGraphs/Computations/C22ChangIIIModel.lean
#print axioms Computations.C22.changIII_adj
#print axioms Computations.C22.changIIITableIso
#print axioms Computations.C22.cliqueProfile_changIII

-- LineGraphs/Computations/C22ChangIIModel.lean
#print axioms Computations.C22.changII_adj
#print axioms Computations.C22.changIITableIso
#print axioms Computations.C22.cliqueProfile_changII

-- LineGraphs/Computations/C22ChangIModel.lean
#print axioms Computations.C22.changI_adj
#print axioms Computations.C22.changITableIso
#print axioms Computations.C22.cliqueProfile_changI

-- LineGraphs/Computations/C22Data.lean
#print axioms Computations.C22.e6Cycle5Adj
#print axioms Computations.C22.e6Cycle5Permutation
#print axioms Computations.C22.e7Cycle6Adj
#print axioms Computations.C22.e7Cycle6Permutation
#print axioms Computations.C22.e7TwoC3Adj
#print axioms Computations.C22.e7TwoC3Permutation
#print axioms Computations.C22.e8FourK2Adj
#print axioms Computations.C22.e8FourK2Permutation
#print axioms Computations.C22.e8TwoC4Adj
#print axioms Computations.C22.e8TwoC4Permutation
#print axioms Computations.C22.e8CubeAdj
#print axioms Computations.C22.e8CubePermutation
#print axioms Computations.C22.e8TwoDiamondsAdj
#print axioms Computations.C22.e8TwoDiamondsPermutation
#print axioms Computations.C22.e8Cycle8Adj
#print axioms Computations.C22.e8Cycle8Permutation
#print axioms Computations.C22.e8WagnerAdj
#print axioms Computations.C22.e8WagnerPermutation
#print axioms Computations.C22.e8TwiceTruncatedK4Adj
#print axioms Computations.C22.e8TwiceTruncatedK4Permutation
#print axioms Computations.C22.e8CycleThreeFiveAdj
#print axioms Computations.C22.e8CycleThreeFivePermutation
#print axioms Computations.C22.e8TruncatedK33Adj
#print axioms Computations.C22.e8TruncatedK33Permutation
#print axioms Computations.C22.e8TwoK4Adj
#print axioms Computations.C22.e8TwoK4Permutation
#print axioms Computations.C22.lattice44Adj

-- LineGraphs/Computations/C22E6Cycle5.lean
#print axioms Computations.C22.e6_switch_cycle5

-- LineGraphs/Computations/C22E7Cycle6.lean
#print axioms Computations.C22.e7_switch_cycle6

-- LineGraphs/Computations/C22E7TwoC3.lean
#print axioms Computations.C22.e7_switch_twoC3

-- LineGraphs/Computations/C22E8Cube.lean
#print axioms Computations.C22.e8_switch_cube

-- LineGraphs/Computations/C22E8Cycle8.lean
#print axioms Computations.C22.e8_switch_cycle8

-- LineGraphs/Computations/C22E8CycleThreeFive.lean
#print axioms Computations.C22.e8_switch_cycleThreeFive

-- LineGraphs/Computations/C22E8FourK2.lean
#print axioms Computations.C22.e8_switch_fourK2

-- LineGraphs/Computations/C22E8TruncatedK33.lean
#print axioms Computations.C22.e8_switch_truncatedK33

-- LineGraphs/Computations/C22E8TwiceTruncatedK4.lean
#print axioms Computations.C22.e8_switch_twiceTruncatedK4

-- LineGraphs/Computations/C22E8TwoC4.lean
#print axioms Computations.C22.e8_switch_twoC4

-- LineGraphs/Computations/C22E8TwoDiamonds.lean
#print axioms Computations.C22.e8_switch_twoDiamonds

-- LineGraphs/Computations/C22E8TwoK4.lean
#print axioms Computations.C22.e8_switch_twoK4
#print axioms Computations.C22.e8_switch_empty

-- LineGraphs/Computations/C22E8Wagner.lean
#print axioms Computations.C22.e8_switch_wagner

-- LineGraphs/Computations/C22Labels.lean
#print axioms Computations.C22.Pair
#print axioms Computations.C22.pairAdj
#print axioms Computations.C22.pairSwitchAdj
#print axioms Computations.C22.edgePairs5
#print axioms Computations.C22.edgePairs5_bijective
#print axioms Computations.C22.edgeLabel5
#print axioms Computations.C22.edgePairs6
#print axioms Computations.C22.edgePairs6_bijective
#print axioms Computations.C22.edgeLabel6
#print axioms Computations.C22.edgePairs8
#print axioms Computations.C22.edgePairs8_bijective
#print axioms Computations.C22.edgeLabel8
#print axioms Computations.C22.nonempty_iso_switchTriangular_of_check
#print axioms Computations.C22.edgeLabel8_adj
#print axioms Computations.C22.sumPairAdj
#print axioms Computations.C22.sumMarked
#print axioms Computations.C22.sumSwitchAdj
#print axioms Computations.C22.sumPairs6
#print axioms Computations.C22.sumLabel6
#print axioms Computations.C22.sumLabel6_apply
#print axioms Computations.C22.sumPair_switch_adj
#print axioms Computations.C22.nonempty_iso_switchTriangularAddOne_of_check

-- LineGraphs/Computations/C22PetersenModel.lean
#print axioms Computations.C22.petersen_adj
#print axioms Computations.C22.petersen_adjacency
#print axioms Computations.C22.petersenTableIso

-- LineGraphs/Computations/C22ShrikhandeModel.lean
#print axioms Computations.C22.shrikhande_adj
#print axioms Computations.C22.shrikhande_adjacency
#print axioms Computations.C22.shrikhandeTableIso
#print axioms Computations.C22.cliqueCount_shrikhande

-- LineGraphs/Computations/C22TriangularModel.lean
#print axioms Computations.C22.triangular8_adj
#print axioms Computations.C22.triangular8TableIso
#print axioms Computations.C22.cliqueProfile_t8

-- Decidability and finite-label instances used by SE4, C22 and Proposition prop:414-seven.
#print axioms
  Computations.C22.instFintypeElemSym2SumFinOfNatNatEdgeSetCompleteBipartiteGraph_lineGraphs
#print axioms Computations.C22.instDecidablePairAdj
#print axioms Computations.C22.instDecidablePairSwitchAdjOfDecidableRelFinAdj
#print axioms Computations.C22.instDecidableSumPairAdj
#print axioms Computations.C22.instDecidableSumMarkedOfDecidableRelFinAdj
#print axioms Computations.C22.instDecidableSumSwitchAdjOfDecidableRelFinAdj
#print axioms SimpleGraph.CubicEight.instDecidableRelFinOfNatNatAdjModel
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjFourK2
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjCycleThreeFive
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjTwoC4
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjTwoK4
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjCycleWithChords
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjCubeGraph
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjWagnerGraph
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjTruncatedK33Graph
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjTwiceTruncatedK4Graph
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjTwoDiamondsGraph
#print axioms SimpleGraph.instFintypeElemSym2SumFinOfNatNatEdgeSetCompleteBipartiteGraph_lineGraphs
#print axioms SimpleGraph.instDecidableRelFinOfNatNatAdjTwoC3

#print axioms SimpleGraph.seidelSeven_not_iso_lineGraph
