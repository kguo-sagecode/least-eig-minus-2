/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs

/-!
# Consolidated axiom audit for [CGSS]

The main declarations of the numbered results in `dependency-diagram.md`, in
paper order, with computations C1--C22 and C24 beside the results or remarks they support.
Each part of a result with several main declarations has its own entry. The four unnumbered
Section 4 remarks listed in the diagram are included as well.

Remark 2.11 has no Lean declaration: Shult's characterization was intentionally left out.
C23 is deferred and is outside this audit. All other result rows and requested computations
are represented below. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Section 2: lines at 60 and 90 degrees.

-- Definition 2.1: star closure.
#print axioms LineSystem.IsStarClosed

-- Definition 2.2: maximality.
#print axioms LineSystem.IsMaximal

-- Lemma 2.3: maximal line systems are star closed.
#print axioms LineSystem.IsMaximal.isStarClosed

-- Hypothesis 2.4: the distinguished star and its orthogonality graph.
#print axioms LineSystem.Hyp24
#print axioms LineSystem.Hyp24.orthGraph

-- Lemma 2.5: recovery from the signed cover.
#print axioms LineSystem.Hyp24.Φ_eq_sigmaSet_union_neg

-- Lemma 2.6: the three cyclic classes and their inner products.
#print axioms LineSystem.Hyp24.ΓaEquivΓb
#print axioms LineSystem.Hyp24.ΓbEquivΓc
#print axioms LineSystem.Hyp24.ΓcEquivΓa
#print axioms LineSystem.Hyp24.inner_eq_zero_or_one
#print axioms LineSystem.Hyp24.add_c_mem_Γb
#print axioms LineSystem.Hyp24.sub_b_mem_Γc

-- Lemma 2.7: reconstruction from one class.
#print axioms LineSystem.Hyp24.Δ_eq_sub
#print axioms LineSystem.Hyp24.Φ_eq_recovery_union_neg
#print axioms LineSystem.Hyp24.Φ_eq_of_Γa_eq

-- Lemma 2.8: the triangle property.
#print axioms LineSystem.Hyp24.triangle
#print axioms LineSystem.Hyp24.orthGraph_hasTriangleProperty

-- Lemma 2.9: the friendship case.
#print axioms LineSystem.Hyp24.orthGraph_iso_friendship_of_forall_adj

-- Computation C1: the block-sum minor used in Lemma 2.10.
#print axioms Computations.C1.det_blockSumMinor

-- Lemma 2.10: the remaining orthogonality graphs.
#print axioms LineSystem.Hyp24.card_Γa_mem
#print axioms LineSystem.Hyp24.orthGraph_isSRGWith
#print axioms LineSystem.Hyp24.orthGraph_iso_of_card_Γa_eq

-- Remark 2.11: Shult's characterization is intentionally not formalized.

-- Lemma 2.12: the cases and reconstruction up to isomorphism.
#print axioms LineSystem.Hyp24.orthGraph_cases
#print axioms LineSystem.Iso.ofOrthGraphIso

-- Theorem 2.13: the five possibilities, with the Section 3 model facts discharged.
#print axioms LineSystem.five_possibilities'

-- Section 3: root systems.

-- Definition 3.1: the classical line systems.
#print axioms LineSystem.An
#print axioms LineSystem.Dn

-- Definition 3.2: the three E₈ presentations and the default model.
#print axioms LineSystem.E₈viaA₈
#print axioms LineSystem.E₈viaD₈
#print axioms LineSystem.E₈viaSteiner
#print axioms LineSystem.E₈

-- Definition 3.3: the perpendicular cuts and independence of the choices in all models.
#print axioms LineSystem.E₇
#print axioms LineSystem.E₆
#print axioms LineSystem.T₇
#print axioms LineSystem.T₆
#print axioms LineSystem.E₈.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.E₈.nonempty_iso_E₆_orthogonalTo
#print axioms LineSystem.E₈viaA₈.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.E₈viaA₈.nonempty_iso_E₆_orthogonalTo
#print axioms LineSystem.E₈viaSteiner.nonempty_iso_E₇_orthogonalTo
#print axioms LineSystem.E₈viaSteiner.nonempty_iso_E₆_orthogonalTo
#print axioms LineSystem.T₇.nonempty_iso_E₇
#print axioms LineSystem.T₆.nonempty_iso_E₆

-- Computation C2: integer presentations and the complete line-count table.
#print axioms Computations.C2.model_presentations
#print axioms Computations.C2.line_counts

-- Lemma 3.4: the numbers of lines in the classical and exceptional models.
#print axioms LineSystem.numLines_An
#print axioms LineSystem.numLines_Dn
#print axioms LineSystem.numLines_E₈
#print axioms LineSystem.numLines_E₈viaA₈
#print axioms LineSystem.numLines_E₈viaSteiner
#print axioms LineSystem.numLines_E₇
#print axioms LineSystem.numLines_E₆

-- Computation C3: isomorphisms of the E₈ coordinate presentations.
#print axioms LineSystem.E₈viaA₈.isoE₈
#print axioms LineSystem.E₈viaSteiner.isoE₈

-- Computation C4: model data and marked stars.
#print axioms Computations.C4.model_data
#print axioms Computations.C4.marked_star_data
#print axioms Computations.C4.exceptional_star_data

-- Theorem 3.5: classification of indecomposable star-closed line systems.
#print axioms LineSystem.classification
#print axioms LineSystem.exists_iso_rootType

-- Computation C5: inclusions and obstructions for maximality.
#print axioms Computations.C5.inclusions_and_obstructions

-- Theorem 3.6: classification of maximal indecomposable line systems.
#print axioms LineSystem.classification_of_isMaximal
#print axioms LineSystem.IsMaximal.exists_iso_rootType

-- Computation C6: coordinate frame matrices.
#print axioms Computations.C6.coordinate_frame_matrices

-- Theorem 3.7: the five quadratic line-matrix identities.
#print axioms LineSystem.signedAdj_quadratic_An
#print axioms LineSystem.signedAdj_quadratic_Dn
#print axioms LineSystem.signedAdj_quadratic_E₈
#print axioms LineSystem.signedAdj_quadratic_E₇
#print axioms LineSystem.signedAdj_quadratic_E₆

-- Computation C17: Gram deletion and the Smith graph spectral values for Theorem 3.8.
#print axioms SimpleGraph.smith_gram_delete_basis
#print axioms SimpleGraph.smithA_maxRayleigh
#print axioms SimpleGraph.smithD_maxRayleigh
#print axioms SimpleGraph.smithE₆_maxRayleigh
#print axioms SimpleGraph.smithE₇_maxRayleigh
#print axioms SimpleGraph.smithE₈_maxRayleigh

-- Theorem 3.8: Smith's theorem.
#print axioms SimpleGraph.smith

-- Definition 3.9: root sets.
#print axioms IsRootSet

-- Theorem 3.10: correspondence between root sets and star-closed line systems.
#print axioms LineSystem.isRootSet_tfae

-- Remark 3.11, Theorem A: classification, uniqueness and the converse.
#print axioms Matrix.IsFiniteCartan.classification
#print axioms Matrix.IsFiniteCartan.classification_type_unique
#print axioms CartanMatrix.isFiniteTypeModel_iff

-- Remark 3.11, Theorem B: coordinate models and orthogonal components, including the empty case.
#print axioms IsRootSet.classification

-- Remark 3.11, Theorem C: lengths, lines, angles and line-matrix identities.
#print axioms IsRootSet.remark_lines

-- Remark 3.11: small ranks and Gram realization.
#print axioms CartanMatrix.small_rank_identifications
#print axioms Matrix.exists_gram_realization

-- Theorem 3.12: containment in a root set and the bipartition criterion.
#print axioms LineSystem.subset_rootSet_iff_bipartition

-- Section 4: graphs with least eigenvalue minus two.

-- Theorem 4.1: representation in A.
#print axioms SimpleGraph.isRepresentedIn_An_iff

-- Remark after Theorem 4.1: the bound and the maximal nonnegative subsets of A.
#print axioms LineSystem.An.card_nonneg_subset_le
#print axioms LineSystem.An.nonneg_subset_maximal_iff
#print axioms LineSystem.An.exists_nonneg_subset_card_eq
#print axioms LineSystem.An.isRepresentation_lineGraph_completeBipartite_sigmaP

-- Theorem 4.2: representation in D.
#print axioms SimpleGraph.isRepresentedIn_Dn_iff

-- Remark after Theorem 4.2: maximal nonnegative subsets of D and attainment of the bound.
#print axioms LineSystem.Dn.card_nonneg_subset_le
#print axioms LineSystem.Dn.exists_isRepresentation_generalizedLineGraph_top_of_maximal
#print axioms LineSystem.Dn.exists_nonneg_subset_card_eq

-- Computation C7: the E₈ representation attaining order 36 in Theorem 4.3.
#print axioms Computations.C7.isRepresentedIn_E₈

-- Computation C20: inner-product counts and the apex counts, also used in Remark 4.14.
#print axioms LineSystem.An.card_N
#print axioms LineSystem.Dn.card_N
#print axioms LineSystem.E₆.card_N
#print axioms LineSystem.E₇.card_N
#print axioms LineSystem.E₈.card_N
#print axioms LineSystem.E₆.N_c
#print axioms LineSystem.E₇.N_c
#print axioms LineSystem.E₈.N_c

-- Theorem 4.3: the E₈ order and degree bounds, and sharpness of the order bound.
#print axioms SimpleGraph.IsRepresentedIn.card_le_36
#print axioms SimpleGraph.IsRepresentedIn.degree_le_28
#print axioms SimpleGraph.exists_isRepresentedIn_E₈_card_36

-- Computation C8: the quadratic bound used in Theorem 4.4.
#print axioms Computations.C8.quadratic_bound

-- Theorem 4.4: the unconditional order and degree bounds for regular graphs in E₈.
#print axioms SimpleGraph.IsRepresentedIn.card_le_28_of_regular
#print axioms SimpleGraph.IsRepresentedIn.degree_le_16_of_regular

-- Computation C24: the trace obstruction for the remark after Theorem 4.4.
#print axioms Computations.C24.trace_sq_gt

-- Remark after Theorem 4.4: exclusions and represented examples.
#print axioms SimpleGraph.not_regular_28_16_isRepresentedIn_E₈
#print axioms SimpleGraph.not_regular_28_17_of_rank_le_seven
#print axioms SimpleGraph.regular_28_12_and_27_16_isRepresentedIn_E₈

-- Computation C9: the seven parameter certificates and the two complementary model isomorphisms.
#print axioms SimpleGraph.changI_isSRGWith
#print axioms SimpleGraph.changII_isSRGWith
#print axioms SimpleGraph.changIII_isSRGWith
#print axioms SimpleGraph.schlafli_isSRGWith
#print axioms SimpleGraph.shrikhande_isSRGWith
#print axioms SimpleGraph.clebsch_isSRGWith
#print axioms SimpleGraph.petersen_isSRGWith
#print axioms SimpleGraph.clebsch.foldedFiveCubeComplIso
#print axioms SimpleGraph.schlafli.gq24ComplIso

-- Example 4.5: the three Chang graphs.
#print axioms SimpleGraph.changI_isRepresentedIn_E₈
#print axioms SimpleGraph.changII_isRepresentedIn_E₈
#print axioms SimpleGraph.changIII_isRepresentedIn_E₈

-- Example 4.6: the Schläfli graph.
#print axioms SimpleGraph.schlafli_isRepresentedIn_E₈

-- Example 4.7: the Shrikhande graph.
#print axioms SimpleGraph.shrikhande_isRepresentedIn_E₈

-- Example 4.8: the Clebsch graph.
#print axioms SimpleGraph.clebsch_isRepresentedIn_E₈

-- Example 4.9: the Petersen graph.
#print axioms SimpleGraph.petersen_isRepresentedIn_E₈

-- Theorem 4.10: Hoffman's theorem.
#print axioms SimpleGraph.hoffman

-- Computation C10: the edge and petal degrees of a generalized line graph.
#print axioms SimpleGraph.generalizedLineGraph_degree_edge
#print axioms SimpleGraph.generalizedLineGraph_degree_petal

-- Theorem 4.11: Hoffman and Ray-Chaudhuri's theorem.
#print axioms SimpleGraph.hoffman_rayChaudhuri

-- Remark 4.12: claw criteria and the claw-free classification.
#print axioms SimpleGraph.IsGeneralizedLineGraph.clawFree_iff
#print axioms SimpleGraph.generalizedLineGraph_fourClawFree_iff
#print axioms SimpleGraph.hoffman_of_clawFree

-- Theorem 4.13: Seidel's theorem.
#print axioms SimpleGraph.seidel

-- Remark after the examples: the large-order corollaries.
#print axioms SimpleGraph.hoffman_of_large
#print axioms SimpleGraph.hoffman_rayChaudhuri_of_large
#print axioms SimpleGraph.seidel_of_large

-- Computation C18: the strongly regular parameters used in Remark 4.14.
#print axioms Computations.C18.srg_parameters

-- Computation C21: exceptional Gram matrices, Cartan matrices and determinants.
#print axioms Computations.C21.e6_gram_det
#print axioms Computations.C21.e7_gram_det
#print axioms Computations.C21.e8_gram_det
#print axioms Computations.C21.e6_gram_eq_cartan
#print axioms Computations.C21.e7_gram_eq_cartan
#print axioms Computations.C21.e8_gram_eq_cartan
#print axioms LineSystem.E₆.det_gram_simpleRoot
#print axioms LineSystem.E₇.det_gram_simpleRoot
#print axioms LineSystem.E₈.det_gram_simpleRoot

-- Computation C22: the switching isomorphisms and clique invariants of Remark 4.14.
#print axioms Computations.C22.e6_switch_cycle5
#print axioms Computations.C22.e7_switch_cycle6
#print axioms Computations.C22.e7_switch_twoC3
#print axioms Computations.C22.e8_switch_fourK2
#print axioms Computations.C22.e8_switch_twoC4
#print axioms Computations.C22.e8_switch_cube
#print axioms Computations.C22.e8_switch_twoDiamonds
#print axioms Computations.C22.e8_switch_cycle8
#print axioms Computations.C22.e8_switch_wagner
#print axioms Computations.C22.e8_switch_twiceTruncatedK4
#print axioms Computations.C22.e8_switch_cycleThreeFive
#print axioms Computations.C22.e8_switch_truncatedK33
#print axioms Computations.C22.e8_switch_twoK4
#print axioms Computations.C22.e8_switch_empty
#print axioms Computations.C22.cliqueProfile_t8
#print axioms Computations.C22.cliqueProfile_changI
#print axioms Computations.C22.cliqueProfile_changII
#print axioms Computations.C22.cliqueProfile_changIII
#print axioms Computations.C22.cliqueCount_shrikhande
#print axioms Computations.C22.cliqueCount_lineGraph_completeBipartite

-- Remark 4.14: classification into seven pairwise nonisomorphic graphs.
#print axioms SimpleGraph.seidel_seven

-- Section 5: spectral characterization.

-- Lemma 5.1: multiplicity and connected components of a regular graph.
#print axioms SimpleGraph.IsRegularOfDegree.multiplicity_eq_card_components

-- Lemma 5.2: the spectral criterion for regularity.
#print axioms SimpleGraph.isRegular_iff_sum_sq_eigenvalues

-- Lemma 5.3: bipartiteness and the negative degree eigenvalue.
#print axioms SimpleGraph.IsRegularOfDegree.isBipartite_iff_neg_eigenvalue
#print axioms SimpleGraph.IsRegularOfDegree.multiplicity_neg_eq_one

-- Lemma 5.4: a regular line graph has a regular or biregular underlying graph.
#print axioms SimpleGraph.regular_or_isBiregularWith_of_lineGraph_regular

-- Lemma 5.5: recovery of cospectrality from line graphs.
#print axioms SimpleGraph.cospectral_of_lineGraph_cospectral

-- Lemma 5.6: the bipartite alternatives for line-graph cospectrality.
#print axioms SimpleGraph.lineGraph_cospectral_bipartite_forall_isBiregularWith

-- Remark 5.7: the spectrum in the nonbipartite alternative.
#print axioms SimpleGraph.lineGraph_cospectral_bipartite_spectrum_of_not_isBipartite

-- Computation C11: the parameters, corrected inequality and substituted spectrum of Theorem 5.8.
#print axioms Computations.C11.parameters
#print axioms Computations.C11.two_mul_sub_one_le
#print axioms Computations.C11.spectrum_of_parameters

-- Theorem 5.8: the flag-graph cospectral characterization.
#print axioms Design.flagGraph_cospectral

-- Computation C12: full-block parameters and the Hadamard border for Corollary 5.9.
#print axioms Computations.C12.full_block_parameters
#print axioms Computations.C12.hadamard_border

-- Corollary 5.9: the complete bipartite line-graph characterization.
#print axioms SimpleGraph.lineGraph_completeBipartite_characterized

-- Corollary 5.10: symmetric designs.
#print axioms Design.IsSymmetric.flagGraphCharacterized

-- Computation C13: the cospectral, nonisomorphic example in the remark after Corollary 5.10.
#print axioms Computations.C13.cospectral
#print axioms Computations.C13.not_nonempty_iso
#print axioms Computations.C13.nonempty_iso_flagGraph

-- Corollary 5.11: designs with lambda equal to one.
#print axioms Design.flagGraphCharacterized_of_lam_eq_one

-- Computation C19: the Hall--Connor certificates used in Remark 5.12.
#print axioms Computations.C19.claw_quadratic
#print axioms Computations.C19.not_sq_eq_49_mul_5_pow_21

-- Computation C14: the lower bound nineteen and the exceptional parameter alternatives.
#print axioms Computations.C14.lambda_ge_nineteen
#print axioms Computations.C14.eq_three_or_five

-- Remark 5.12: the characterization for lambda less than nineteen.
#print axioms Design.flagGraphCharacterized_of_lam_lt_nineteen

-- Example 5.13: resolvable designs and failure of characterization.
#print axioms Design.not_flagGraphCharacterized_of_resolvable

-- Computation C15: the Petersen double-line-graph example in the remark after Example 5.13.
#print axioms Computations.C15.flagGraph_cospectral_double_lineGraph
#print axioms Computations.C15.flagGraph_not_nonempty_iso_double_lineGraph

-- Section 6: Hadamard matrices.

-- Hypothesis 6.1: four-row agreement.
#print axioms Matrix.IsHadamard.FourRowAgreement

-- Theorem 6.2: exclusion of the sixteenths alternative.
#print axioms Matrix.IsHadamard.not_fourRow_agree_sixteenths

-- Computation C16: the agreement certificates and the H₁₂ line count in the closing remark.
#print axioms Computations.C16.fourRow_agreements
#print axioms Computations.C16.checkFourRowAgreement_sound
#print axioms Computations.C16.h12_numLines

#print axioms LineSystem.nonempty_signing

#print axioms IsRootSet.exists_rootRepresentatives

-- Examples 4.7 and 4.8 of [CGSS]
#print axioms SimpleGraph.shrikhande.changIIndex_checked
#print axioms SimpleGraph.shrikhande.changIEmbedding
#print axioms SimpleGraph.shrikhande.nonempty_iso_induce_changI
#print axioms SimpleGraph.clebsch.schlafliIndex_checked
#print axioms SimpleGraph.clebsch.schlafliEmbedding
#print axioms SimpleGraph.clebsch.nonempty_iso_induce_schlafli

#print axioms SimpleGraph.seidelSeven_not_iso_lineGraph

#print axioms LineSystem.five_possibilities_forall_hyp24

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

#print axioms SimpleGraph.spectrumMultiset_lineGraph_of_card_le

#print axioms LineSystem.Iso.exists_ambient_isometry_of_same_model

#print axioms LineSystem.Hyp24.six_lines_of_iso_friendship_zero

#print axioms LineSystem.IsIndecomposable.eq_pair_or_exists_hyp24

#print axioms SimpleGraph.IsRegularOfDegree.largestEigenvalue_eq

#print axioms Computations.TrivialDesignException.incidenceIndex

#print axioms
  Computations.TrivialDesignException.lineGraph_completeBipartite_cospectral_double_lineGraph

#print axioms Computations.TrivialDesignException.flagGraph_not_nonempty_iso_double_lineGraph

#print axioms SimpleGraph.shrikhande.changIIndex

#print axioms SimpleGraph.clebsch.schlafliIndex

-- Side claims of [CGSS]: the cuboctahedron and Hadamard matrices
-- (`LineGraphs/SideClaims/`; all their declarations are in `LineGraphs/SideClaims/Audit.lean`).
-- The remark after Definition 3.1: the six diagonals of the cuboctahedron represent `A₃`.
#print axioms LineSystem.nonempty_iso_cuboctahedron_An
#print axioms LineSystem.numLines_cuboctahedron
#print axioms LineSystem.cuboctahedron_eq_Dn
-- Section 6: the spectra of `PᵀP` and `PPᵀ`.
#print axioms Matrix.IsHadamard.spectrumMultiset_transpose_hadamardPairs_mul
#print axioms Matrix.IsHadamard.spectrumMultiset_hadamardPairs_mul_transpose
-- Section 6: the Sylvester matrices, Hypothesis 6.1 for them, and the Sylvester case.
#print axioms Matrix.isHadamard_sylvester
#print axioms Matrix.sylvester_fourRowAgreement
#print axioms Matrix.sylvester_lines

-- Claims that [CGSS] makes itself and that had no Lean statement of their own before 9 October
-- 2026 (found by the statement audit, `LineGraphs/AUDIT-statements.md`); formalized that evening
-- at the author's request, in `LineGraphs/PaperClaims/` and `LineGraphs/Computations/C23.lean`.
-- Theorem 2.13, the counts: `|Φ|` is twice the number of lines, and `|Δ|` is even.
#print axioms LineSystem.ncard_Φ_eq_two_mul_numLines
#print axioms LineSystem.Hyp24.even_ncard_Δ
#print axioms LineSystem.five_possibilities_ncard_Δ
-- Lemma 2.9: the isomorphism with the friendship graph sends `x` to the common vertex.
#print axioms LineSystem.Hyp24.exists_iso_friendship_apply_eq_none
-- Theorem 3.6, proof: the only inclusions between root systems of the same rank.
#print axioms LineSystem.RootType.nonempty_isometricInclusion_iff
-- The paragraph before Theorem 3.7: the entries of `C`, and `C` up to switching.
#print axioms LineSystem.signedAdj_apply_mem
#print axioms LineSystem.exists_signedAdj_eq_switch
#print axioms LineSystem.exists_signedAdj_submatrix
-- Theorem 3.10 (i) at any fixed length.
#print axioms IsRootSet.smul_iff
#print axioms LineSystem.isRootSet_tfae_of_inner_self_eq
-- Remark 3.11: the models of `E₇` and `E₆` of Theorem 3.10 are those of Definition 3.3.
#print axioms RootSetModel.image_val_E₇
#print axioms RootSetModel.image_val_E₆
#print axioms RootSetModel.nonempty_iso_E₇
#print axioms RootSetModel.nonempty_iso_E₆
-- The definitions of Section 4: `Kₙ = L(K_{1,n})`, `CP(a)` represented by `e₀ ± eᵢ`, and the least
-- eigenvalue of a generalized line graph with more vertices than dimensions.
#print axioms SimpleGraph.nonempty_iso_top_lineGraph_star
#print axioms SimpleGraph.cocktailParty_isRepresentation
#print axioms SimpleGraph.cocktailParty_isRepresentedIn_Dn
#print axioms SimpleGraph.generalizedLineGraph_leastEigenvalue_eq_neg_two
-- The remark after Theorem 4.1: the maximal subsets of `Aₙ` with nonnegative inner products.
#print axioms LineSystem.An.exists_isRepresentation_lineGraph_completeBipartite_of_maximal
#print axioms LineSystem.An.exists_maximal_isRepresentation_lineGraph
-- Computation C20, the other root systems (the blueprint's statement; the paper states `E₈`).
#print axioms SimpleGraph.IsRepresentedIn.degree_le_An
#print axioms SimpleGraph.IsRepresentedIn.degree_le_Dn
#print axioms SimpleGraph.IsRepresentedIn.degree_le_E₆
#print axioms SimpleGraph.IsRepresentedIn.degree_le_E₇
-- Examples 4.5 to 4.9 and C7: the tables of roots are the paper's formulas.
#print axioms Computations.C9.changIRoots_perm
#print axioms Computations.C9.changIIRoots_perm
#print axioms Computations.C9.changIIIRoots_perm
#print axioms Computations.C9.schlafliRoots_perm
#print axioms Computations.C9.shrikhandeRoots_perm
#print axioms Computations.C9.clebschRoots_perm
#print axioms Computations.C9.petersenRoots_perm
#print axioms Computations.C7.roots_perm
-- The remark after Theorem 5.8: (i) holds only if `v ≤ 4`.
#print axioms Design.v_le_four_of_add_le_nine
#print axioms Design.v_le_four_of_le_of_add_le_nine
-- Remark 5.12: for `t = 1`, `λ = 2` and `s` odd; for `t > 1`, finitely many `s`.
#print axioms Design.NonbipartiteParameters.lam_eq_two_and_odd_of_t_eq_one
#print axioms Design.NonbipartiteParameters.sub_one_le_of_one_lt
#print axioms Design.NonbipartiteParameters.finite_setOf_s
-- Computation C13: the two graphs represent the same 12 equiangular lines in `ℝ⁶`.
#print axioms Computations.C13.posSemidef_equiangularGram_graph1
#print axioms Computations.C13.posSemidef_equiangularGram_graph2
#print axioms Computations.C13.rank_equiangularGram_graph1
#print axioms Computations.C13.rank_equiangularGram_graph2
#print axioms Computations.C13.equiangularGram_isSwitchingEquivalent
#print axioms Computations.C13.same_equiangular_lines
#print axioms Computations.C13.ncard_equiangular_lines
-- Section 6: `½n(n − 1)` lines with angles `90°` and `arccos 1/d`, in a hyperplane.
#print axioms Matrix.IsHadamard.FourRowAgreement.line_angles
#print axioms Matrix.IsHadamard.FourRowAgreement.lines_mem_hyperplane
#print axioms Matrix.IsHadamard.FourRowAgreement.exists_line_angles
-- Computation C23, the remark in Example 5.13: the designs of the paper's instances, explicitly.
-- k = 2: the flag graph of the (6,3,10,5,2) design is not characterized by its spectrum, and the
-- graph H is the graph on the pairs of points and the line graph of the Petersen graph.
#print axioms Computations.C23.oneFactorization
#print axioms Computations.C23.not_flagGraphCharacterized_6_3_10_5_2
#print axioms Computations.C23.nonempty_iso_pairGraph
#print axioms Computations.C23.nonempty_iso_petersen_lineGraph
-- k = 3: the design D₁ with parameters (15,10,21,14,9) does not exist (cf. Remark 5.12).
#print axioms Computations.C23.false_of_parameters_three
-- k = 4: the flag graph of the (28,21,36,27,20) design is not characterized by its spectrum.
#print axioms Computations.C23.hyperovalResolution
#print axioms Computations.C23.biplaneDesign
#print axioms Computations.C23.complementDesign
#print axioms Computations.C23.not_flagGraphCharacterized_28_21_36_27_20
