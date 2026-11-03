/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.TrivialDesignException
import LineGraphs.Computations.C13Characterization
import LineGraphs.Computations.C11Diagonal
import LineGraphs.Computations.C11Spectrum
import LineGraphs.Computations.C12
import LineGraphs.Computations.C13Vectors
import LineGraphs.Computations.C13Cube
import LineGraphs.Computations.C13Seidel
import LineGraphs.Computations.C14
import LineGraphs.Computations.C15Result

/-!
# Axiom audit for computations C11–C15 of [CGSS], Section 5

Every theorem, abbreviation, named instance, and data or construction definition in the
assigned computation modules is listed below. The expected dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`, or no axioms at all.
Every certificate is reduced by the kernel.
-/

#print axioms Computations.C11.exists_positive_half_difference
#print axioms Computations.C11.parameter_equation
#print axioms Computations.C11.points_eq
#print axioms Computations.C11.two_mul_sq_mul_points
#print axioms Computations.C11.mul_blocks_sub_points
#print axioms Computations.C11.dvd_block_size
#print axioms Computations.C11.parameters
#print axioms Computations.C11.two_le_parameter
#print axioms Computations.C11.lambda_equation
#print axioms Computations.C11.lambda_remainder
#print axioms Computations.C11.parameter_dvd
#print axioms Computations.C11.two_mul_sub_one_le
#print axioms Computations.C11.nonprincipal_square
#print axioms Computations.C11.spectral_parameters
#print axioms Computations.C11.hoffman_value
#print axioms Computations.C11.triangle_diagonal
#print axioms Computations.C11.even_mul_of_even_cube
#print axioms Computations.C11.cube_diagonal_eq
#print axioms Computations.C11.spectral_moments
#print axioms Computations.C11.matrix_identity
#print axioms Computations.C11.even_cube_diagonal
#print axioms Computations.C11.even_parameter_cube
#print axioms Computations.C11.spectrum_of_parameters
#print axioms Computations.C12.full_block_parameters
#print axioms Computations.C12.core_row_sum
#print axioms Computations.C12.core_mul
#print axioms Computations.C12.border_isHadamard
#print axioms Computations.C12.hadamard_border
#print axioms Computations.C13.spectrum_graph1
#print axioms Computations.C13.spectrum_graph2
#print axioms Computations.C13.cospectral
#print axioms Computations.C13.seidel_spectrum_graph1
#print axioms Computations.C13.seidel_spectrum_graph2
#print axioms Computations.C13.switching_equivalent
#print axioms Computations.C13.graph1_no_claw
#print axioms Computations.C13.graph2_claw
#print axioms Computations.C13.not_nonempty_iso
#print axioms Computations.C13.flag_edge_bijective
#print axioms Computations.C13.flag_adjacency_checked
#print axioms Computations.C13.nonempty_iso_flagGraph
#print axioms Computations.C13.cube_edge_bijective
#print axioms Computations.C13.cube_line_adjacency_checked
#print axioms Computations.C13.nonempty_iso_cube_lineGraph
#print axioms Computations.C13.spectrum_neg
#print axioms Computations.C13.paper_seidel_spectrum_graph1
#print axioms Computations.C13.paper_seidel_spectrum_graph2
#print axioms Computations.C13.adjacency1_checked
#print axioms Computations.C13.spectrum1_checked
#print axioms Computations.C13.seidel1_checked
#print axioms Computations.C13.adjacency2_checked
#print axioms Computations.C13.spectrum2_checked
#print axioms Computations.C13.seidel2_checked
#print axioms Computations.C13.printed_roots_checked
#print axioms Computations.C13.root_map_gram
#print axioms Computations.C13.roots_mem_E₇
#print axioms Computations.C13.gram_checked
#print axioms Computations.C13.representation_graph1
#print axioms Computations.C13.isRepresentedIn_E₇_graph1
#print axioms Computations.C13.representation_graph2
#print axioms Computations.C13.isRepresentedIn_E₇_graph2
#print axioms Computations.C14.lambda_remainder
#print axioms Computations.C14.lambda_eq_two
#print axioms Computations.C14.eq_three_or_five
#print axioms Computations.C14.lambda_ge_nineteen
#print axioms Computations.C14.nineteen_sharp
#print axioms Computations.C14.t2_parameters
#print axioms Computations.C15.spectrum_graph1
#print axioms Computations.C15.spectrum_graph2
#print axioms Computations.C15.cospectral
#print axioms Computations.C15.four_cliques_graph1
#print axioms Computations.C15.four_cliques_graph2
#print axioms Computations.C15.not_nonempty_iso
#print axioms Computations.C15.flag_edge_bijective
#print axioms Computations.C15.Table1.factor1_checked
#print axioms Computations.C15.Table1.factor2_checked
#print axioms Computations.C15.Table1.factor3_checked
#print axioms Computations.C15.Table1.factor4_checked
#print axioms Computations.C15.Table1.factor5_checked
#print axioms Computations.C15.Table2.factor1_checked
#print axioms Computations.C15.Table2.factor2_checked
#print axioms Computations.C15.Table2.factor3_checked
#print axioms Computations.C15.Table2.factor4_checked
#print axioms Computations.C15.Table2.factor5_checked
#print axioms Computations.C15.line_edge_bijective
#print axioms Computations.C15.double_line_edge_bijective
#print axioms Computations.C15.nonempty_iso_petersen
#print axioms Computations.C15.Table1.power1_checked
#print axioms Computations.C15.Table1.power2_checked
#print axioms Computations.C15.Table1.power3_checked
#print axioms Computations.C15.Table1.power4_checked
#print axioms Computations.C15.Table2.power1_checked
#print axioms Computations.C15.Table2.power2_checked
#print axioms Computations.C15.Table2.power3_checked
#print axioms Computations.C15.Table2.power4_checked
#print axioms Computations.C15.flagGraph_cospectral_double_lineGraph
#print axioms Computations.C15.flagGraph_not_nonempty_iso_double_lineGraph
#print axioms Computations.C15.adjacency1_checked
#print axioms Computations.C15.annihilator1_checked
#print axioms Computations.C15.powers1_checked
#print axioms Computations.C15.spectrum1_checked
#print axioms Computations.C15.adjacency2_checked
#print axioms Computations.C15.annihilator2_checked
#print axioms Computations.C15.powers2_checked
#print axioms Computations.C15.spectrum2_checked
#print axioms Computations.C12.core
#print axioms Computations.C12.border
#print axioms Computations.C13.graph1
#print axioms Computations.C13.graph2
#print axioms Computations.C13.adjacency1
#print axioms Computations.C13.adjacency2
#print axioms Computations.C13.spectralData
#print axioms Computations.C13.roots1
#print axioms Computations.C13.roots2
#print axioms Computations.C13.rootMap
#print axioms Computations.C13.flagAdjacency
#print axioms Computations.C13.flagPermutation
#print axioms Computations.C13.switchSigns
#print axioms Computations.C13.switchPermutation
#print axioms Computations.C13.seidelSpectralData
#print axioms Computations.C13.incidenceGraph
#print axioms Computations.C13.incidenceGraphDecidable
#print axioms Computations.C13.lineGraphDecidable
#print axioms Computations.C13.blocks
#print axioms Computations.C13.design
#print axioms Computations.C13.flagLabels
#print axioms Computations.C13.flagEdge
#print axioms Computations.C13.flagGraphIso
#print axioms Computations.C13.cube
#print axioms Computations.C13.cubeDecidable
#print axioms Computations.C13.cubeEdgeLabels
#print axioms Computations.C13.cubeEdge
#print axioms Computations.C13.cubeLineGraphIso
#print axioms Computations.C13.mappedRoot
#print axioms Computations.C13.vectors
#print axioms Computations.C15.graph1
#print axioms Computations.C15.graph2
#print axioms Computations.C15.adjacency1
#print axioms Computations.C15.adjacency2
#print axioms Computations.C15.spectralData
#print axioms Computations.C15.blocks
#print axioms Computations.C15.design
#print axioms Computations.C15.flagLabels
#print axioms Computations.C15.flagEdge
#print axioms Computations.C15.flagGraphIso
#print axioms Computations.C15.petersen
#print axioms Computations.C15.petersenDecidable
#print axioms Computations.C15.petersenEquiv
#print axioms Computations.C15.petersenIso
#print axioms Computations.C15.lineLabels
#print axioms Computations.C15.lineEdge
#print axioms Computations.C15.doubleLineLabels
#print axioms Computations.C15.doubleLineEdge
#print axioms Computations.C15.doubleLineGraphIso
#print axioms Computations.C15.Table1.power0
#print axioms Computations.C15.Table1.power1
#print axioms Computations.C15.Table1.power2
#print axioms Computations.C15.Table1.power3
#print axioms Computations.C15.Table1.power4
#print axioms Computations.C15.Table1.factor1
#print axioms Computations.C15.Table1.factor2
#print axioms Computations.C15.Table1.factor3
#print axioms Computations.C15.Table1.factor4
#print axioms Computations.C15.Table1.factor5
#print axioms Computations.C15.Table2.power0
#print axioms Computations.C15.Table2.power1
#print axioms Computations.C15.Table2.power2
#print axioms Computations.C15.Table2.power3
#print axioms Computations.C15.Table2.power4
#print axioms Computations.C15.Table2.factor1
#print axioms Computations.C15.Table2.factor2
#print axioms Computations.C15.Table2.factor3
#print axioms Computations.C15.Table2.factor4
#print axioms Computations.C15.Table2.factor5

#print axioms Computations.C13.not_flagGraphCharacterized

-- Remark 5.12 of [CGSS]: the trivial-design exception
#print axioms Computations.TrivialDesignException.design
#print axioms Computations.TrivialDesignException.incidenceSignless
#print axioms Computations.TrivialDesignException.completeAdjacency
#print axioms Computations.TrivialDesignException.incidence_spectrum_checked
#print axioms Computations.TrivialDesignException.complete_spectrum_checked
#print axioms Computations.TrivialDesignException.incidence_signless_eq
#print axioms Computations.TrivialDesignException.spectrum_incidence_signless
#print axioms Computations.TrivialDesignException.spectrum_complete
#print axioms Computations.TrivialDesignException.spectrum_triangular
#print axioms Computations.TrivialDesignException.spectrum_flagGraph
#print axioms Computations.TrivialDesignException.spectrum_double_lineGraph
#print axioms Computations.TrivialDesignException.flagGraph_cospectral_double_lineGraph
#print axioms Computations.TrivialDesignException.not_flagGraphCharacterized

#print axioms Computations.TrivialDesignException.incidenceIndex

#print axioms
  Computations.TrivialDesignException.lineGraph_completeBipartite_cospectral_double_lineGraph

#print axioms Computations.TrivialDesignException.flagGraph_not_nonempty_iso_double_lineGraph
