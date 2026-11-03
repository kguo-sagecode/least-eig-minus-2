/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C9Subgraphs
import LineGraphs.Computations.E8
import LineGraphs.Computations.Examples

import LineGraphs.Computations.BoundedSearchExamples
import LineGraphs.Computations.CliqueBenchmarks

/-!
# Checker axiom audit

The main soundness results audit every transitive dependency, including the E₈ chunks.
-/

#print axioms Computations.dot_ofFn
#print axioms Computations.dot_eq_sum
#print axioms Computations.toMatrix_mul
#print axioms Computations.toMatrix_pow
#print axioms Computations.trace_eq
#print axioms Computations.toMatrix_eval
#print axioms Computations.checkShape_sound
#print axioms Computations.checkPolynomial_sound
#print axioms Computations.checkPolynomial_sound_real
#print axioms Computations.checkTraces_sound
#print axioms Computations.checkGram_sound
#print axioms LineSystem.IntegerModel.inner_eq_of_checkGram
#print axioms Computations.checkDots_sound
#print axioms Computations.checkDots_lengths
#print axioms Computations.checkStar_sound
#print axioms Computations.checkStar_lengths
#print axioms LineSystem.IntegerModel.isStarClosed_of_checkStar
#print axioms Computations.checkPermutation_sound
#print axioms Computations.nonempty_graphOfMatrix_iso
#print axioms Computations.adjMatrix_graphOfMatrix
#print axioms Computations.nonempty_iso_of_checkGraphIso'
#print axioms LineSystem.IntegerModel.adjMatrix_eq_dotAdjacency
#print axioms Computations.allBox_eq_true
#print axioms Computations.no_bounded_solution_of_check
#print axioms Computations.allSRGParameters_sound
#print axioms Computations.no_srg_solution_of_check
#print axioms Computations.rootTable_eq_image
#print axioms Computations.all_eq_true_of_chunks
#print axioms Computations.VectorTree.lookup_sound
#print axioms Computations.checkAnnihilator_sound
#print axioms Computations.charpoly_eq_of_checks
#print axioms Matrix.IsHermitian.trace_pow_eq_multiplicities
#print axioms Matrix.eq_of_vandermonde_moments
#print axioms Matrix.IsHermitian.multiplicities_eq_of_certificate
#print axioms Matrix.IsHermitian.charpoly_eq_prod_multiplicities
#print axioms Matrix.IsHermitian.charpoly_eq_of_annihilatingPolynomial_trace
#print axioms Matrix.IsHermitian.spectrumMultiset_eq_of_annihilatingPolynomial_trace
#print axioms Computations.checkSpectrum_sound
#print axioms Computations.spectrum_graphOfMatrix_of_checkSpectrum
#print axioms Computations.checkSwitching_sound
#print axioms Computations.checkSeidelSwitching_sound
#print axioms Computations.cliquesOn_eq_filter
#print axioms Computations.matrixCliques_sound
#print axioms Computations.cliqueCount_sound
#print axioms Computations.cliqueProfile_perm_of_iso
#print axioms Computations.cliqueProfile_perm_of_checkGraphIso
#print axioms Computations.checkNonisomorphic_sound
#print axioms Computations.not_nonempty_iso_of_checkNonisomorphic
#print axioms Matrix.charpoly_eq_of_scaled_inverse_intertwiner
#print axioms Computations.checkSimilarity_sound
#print axioms Computations.cospectral_graphOfMatrix_of_checkSimilarity
#print axioms Matrix.IsHermitian.largestEigenvalue_le_of_pos_supervector
#print axioms Matrix.IsHermitian.largestEigenvalue_eq_of_pos_eigenvector
#print axioms Computations.checkPositiveEigenvector_sound
#print axioms Computations.C4.e₈_star_chunk_0
#print axioms Computations.C4.e₈_star_checked
#print axioms Computations.E₈Data.e₈Roots_eq_image
#print axioms LineSystem.isStarClosed_E₈
#print axioms Computations.Examples.triangle_graph_spectrum
#print axioms Computations.Examples.path_iso
#print axioms Computations.Examples.gram_inner
#print axioms Computations.Examples.no_bounded_solution
#print axioms Computations.Examples.triangle_switch
#print axioms Computations.Examples.path_cospectral
#print axioms Computations.Examples.triangle_largestEigenvalue
#print axioms Computations.Examples.triangle_path_nonisomorphic
#print axioms Computations.Examples.changII_not_iso_changIII
#print axioms SimpleGraph.Iso.cospectral
#print axioms Computations.spectrum_eq_of_checkSpectrum
#print axioms Computations.largestEigenvalue_graphOfMatrix_of_checkPositiveEigenvector

-- Examples 4.7 and 4.8 of [CGSS]
#print axioms SimpleGraph.shrikhande.changIIndex_checked
#print axioms SimpleGraph.shrikhande.changIEmbedding
#print axioms SimpleGraph.shrikhande.nonempty_iso_induce_changI
#print axioms SimpleGraph.clebsch.schlafliIndex_checked
#print axioms SimpleGraph.clebsch.schlafliEmbedding
#print axioms SimpleGraph.clebsch.nonempty_iso_induce_schlafli

#print axioms SimpleGraph.shrikhande.changIIndex

#print axioms SimpleGraph.clebsch.schlafliIndex
