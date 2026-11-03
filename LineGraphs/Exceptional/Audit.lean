/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.All

/-! # Axiom audit for the exceptional-graphs note

Every explicit declaration of the formalization of [Exc] is audited, including definitions,
instances and helpers. Groups follow the order of [Exc], with the main results of
each label first. Only `propext`, `Classical.choice` and `Quot.sound` may occur.

The statement about the files and the correctness of the program and of `labelg`
are not formalized; the three lists in `Main` are abstract sets of graphs.
-/

-- Section 1, sec:intro

-- LatticeBasic.lean
#print axioms SimpleGraph.IsExceptional

-- Section 2, sec:lattices

-- Lattice.lean
#print axioms SimpleGraph.latticeDet
#print axioms SimpleGraph.IsRepresentation.latticeDet_eq_det_gram

-- LatticeBasic.lean
#print axioms SimpleGraph.integralGramMatrix
#print axioms SimpleGraph.integralGramMatrix_cast

-- Lattice.lean
#print axioms Matrix.gram_sum_int_smul
#print axioms Module.Basis.toMatrix_det_sq_eq_one
#print axioms Module.Basis.det_gram_eq
#print axioms InnerProductSpace.exists_span_int_equiv_of_gram_eq
#print axioms Submodule.spanIntBasis
#print axioms Matrix.det_gram_mem_nat

-- LatticeRank.lean
#print axioms LinearIndependent.real_of_int_gram
#print axioms Module.Basis.span_real_eq_span_lattice
#print axioms SimpleGraph.IsRepresentation.linearIndependent_lattice_basis
#print axioms SimpleGraph.IsRepresentation.card_lattice_basis
#print axioms SimpleGraph.IsRepresentation.latticeDet_pos

-- Lemma 2.2, lem:rootlattice

-- RootLattice.lean
#print axioms SimpleGraph.IsRepresentation.exists_unique_root_lattice
#print axioms SimpleGraph.IsRepresentation.det_gram_lattice_basis_of_iso

-- LatticeBasic.lean
#print axioms LineSystem.RootType.latticeDet
#print axioms LineSystem.RootType.latticeDet_pos

-- RootLatticeBasis.lean
#print axioms LineSystem.span_int_eq_of_integral_coordinates
#print axioms LineSystem.intBasisOfSimpleRoots
#print axioms LineSystem.intBasisOfSimpleRoots_apply
#print axioms LineSystem.E₆.span_int_simpleRoot
#print axioms LineSystem.E₆.simpleIntBasis
#print axioms LineSystem.E₆.simpleIntBasis_apply
#print axioms LineSystem.E₇.span_int_simpleRoot
#print axioms LineSystem.E₇.simpleIntBasis
#print axioms LineSystem.E₇.simpleIntBasis_apply
#print axioms LineSystem.E₈.span_int_simpleRoot
#print axioms LineSystem.E₈.simpleIntBasis
#print axioms LineSystem.E₈.simpleIntBasis_apply

-- RootLatticeClassical.lean
#print axioms LineSystem.An.simpleRoot
#print axioms LineSystem.An.simpleRoot_mem
#print axioms LineSystem.An.gram_simpleRoot
#print axioms LineSystem.An.det_gram_simpleRoot
#print axioms LineSystem.An.sub_single_mem_span_simpleRoot
#print axioms LineSystem.An.span_int_simpleRoot
#print axioms LineSystem.An.simpleIntBasis
#print axioms LineSystem.An.simpleIntBasis_apply
#print axioms LineSystem.Dn.simpleRoot
#print axioms LineSystem.Dn.simpleRoot_mem
#print axioms LineSystem.Dn.gram_simpleRoot
#print axioms LineSystem.Dn.det_gram_simpleRoot
#print axioms LineSystem.Dn.span_int_simpleRoot
#print axioms LineSystem.Dn.simpleIntBasis
#print axioms LineSystem.Dn.simpleIntBasis_apply

-- RootLattice.lean
#print axioms LineSystem.Iso.exists_span_int_equiv
#print axioms LineSystem.RootType.exists_int_basis_det
#print axioms LineSystem.RootType.det_gram_int_basis
#print axioms SimpleGraph.IsRepresentation.span_int_latticeRoots
#print axioms SimpleGraph.IsRepresentation.exists_lattice_basis_of_iso
#print axioms SimpleGraph.IsRepresentation.latticeDet_eq_of_iso

-- Lemma 2.3, lem:snf

-- ElementaryDivisors.lean
#print axioms SimpleGraph.latticeDet_eq_prod_smithNormalForm
#print axioms SimpleGraph.prod_smith_coeffs_eq_latticeDet

-- LatticeCoordinates.lean
#print axioms SimpleGraph.IsRepresentation.latticeGramMatrix
#print axioms SimpleGraph.IsRepresentation.latticeGramMatrix_cast
#print axioms SimpleGraph.IsRepresentation.det_latticeGramMatrix
#print axioms SimpleGraph.latticeCoordinates
#print axioms SimpleGraph.sum_latticeCoordinates_smul
#print axioms SimpleGraph.latticeCoordinates_surjective
#print axioms SimpleGraph.IsRepresentation.integralGramMatrix_eq_coordinates

-- ElementaryDivisorsAlgebra.lean
#print axioms Module.Basis.SmithNormalForm.coeff_ne_zero
#print axioms Module.Basis.SmithNormalForm.prod_natAbs_eq_relIndex_of_smul_mem

-- ElementaryDivisorsMatrix.lean
#print axioms Matrix.prod_smith_coeffs_eq_natAbs_det

-- Lemma 2.4, lem:basisdet

-- BasisDet.lean
#print axioms SimpleGraph.latticeDet_eq_div_card_basisDetGroup_sq
#print axioms SimpleGraph.certificateMatrix_det_eq_card_sq_mul_latticeDet

-- BasisDetAlgebra.lean
#print axioms Matrix.modularHom
#print axioms Matrix.ker_modularHom_eq_range
#print axioms Matrix.index_range_mulVec
#print axioms Matrix.natCard_range_modularHom
#print axioms Matrix.range_modularHom_eq_closure_columns

-- BasisDet.lean
#print axioms SimpleGraph.basisDetGroup

-- CertificateDefs.lean
#print axioms Matrix.certificateMatrix
#print axioms Matrix.certificateCoordinates

-- Lemma 2.5, lem:E6Zm

-- E6NotSumSquares.lean
#print axioms LineSystem.E₆.not_exists_lattice_isometry_int
#print axioms LineSystem.E₆.not_exists_integral_gram_simpleRoot
#print axioms LineSystem.dnRoot_cast_zmod_two_eq_of_orthogonal
#print axioms LineSystem.integerInner_cast_zmod_two_eq

-- Proposition 2.6, prop:types

-- Types.lean
#print axioms SimpleGraph.IsRepresentation.isGeneralizedLineGraph_iff_rootType_isClassical
#print axioms SimpleGraph.isExceptional_iff_rank_latticeDet

-- E8Criterion.lean
#print axioms SimpleGraph.isRepresentedIn_E₈_iff_rank_le

-- LatticeIntegral.lean
#print axioms LineSystem.integerVector_int_smul
#print axioms LineSystem.Dn.exists_integerVector_of_mem_span
#print axioms LineSystem.E₆.not_exists_gram_in_span_Dn

-- Types.lean
#print axioms LineSystem.RootType.IsClassical
#print axioms LineSystem.RootType.IsExceptional
#print axioms LineSystem.RootType.not_isClassical_iff_isExceptional
#print axioms LineSystem.RootType.isExceptional_iff_rank_latticeDet
#print axioms LineSystem.RootType.exists_E₆_simple_roots
#print axioms SimpleGraph.IsRepresentation.not_rootType_isExceptional_of_isGeneralizedLineGraph
#print axioms SimpleGraph.IsRepresentation.isExceptional_iff_rootType_isExceptional
#print axioms SimpleGraph.IsRepresentation.isExceptional_iff_rank_latticeDet

-- E8Criterion.lean
#print axioms LineSystem.An.inclusionE₈OfLE
#print axioms LineSystem.Dn.inclusionOfLE
#print axioms LineSystem.Dn.inclusionE₈OfLE
#print axioms LineSystem.E₆.inclusionE₈
#print axioms LineSystem.E₇.inclusionE₈
#print axioms LineSystem.RootType.inclusionE₈
#print axioms SimpleGraph.isRepresentedIn_E₈_iff_posSemidef_and_rank_le

-- Lemma 3.1, lem:noncut

-- NonCut.lean
#print axioms SimpleGraph.Connected.exists_noncut_isRepresentedIn_E₈
#print axioms SimpleGraph.Connected.exists_noncut_with_neighbor

-- Definition 3.2, def:certificate

-- CertificateDefs.lean
#print axioms Matrix.IsGramCertificate
#print axioms Matrix.HasPositiveLeadingMinors

-- CertificateSylvester.lean
#print axioms Matrix.posDef_of_positive_leading_minors
#print axioms Matrix.positive_leading_minors_iff_posDef
#print axioms Matrix.positive_leading_minors_iff_posDef_map
#print axioms Matrix.positive_leading_minors_order_independent

-- Certificate.lean
#print axioms Matrix.certificate_positive_iff

-- CertificateExistence.lean
#print axioms SimpleGraph.integralGramMatrix_isSymm

-- Lemma 3.3, lem:certificate

-- CertificateExistence.lean
#print axioms Matrix.exists_isGramCertificate_iff_posSemidef
#print axioms SimpleGraph.exists_integralGramMatrix_certificate_iff

-- Certificate.lean
#print axioms Matrix.IsGramCertificate.card_eq_rank

-- CertificateExistence.lean
#print axioms Matrix.isGramCertificate_of_linearIndependent_rows

-- Certificate.lean
#print axioms Matrix.IsGramCertificate.posDef
#print axioms Matrix.IsGramCertificate.det_pos
#print axioms Matrix.IsGramCertificate.identity_map
#print axioms Matrix.IsGramCertificate.factorization
#print axioms Matrix.IsGramCertificate.posSemidef

-- CertificateExistence.lean
#print axioms Matrix.PosSemidef.posDef_principal_of_linearIndependent_rows
#print axioms Matrix.mul_adjugate_mul_eq_det_smul_of_row_span
#print axioms Matrix.isGramCertificate_of_row_basis
#print axioms Matrix.exists_isGramCertificate_of_posSemidef

-- Lemma 3.4, lem:extension

-- Extension.lean
#print axioms SimpleGraph.isRepresentedIn_adjoinVertex_iff

-- CertificateDefs.lean
#print axioms Matrix.certificateDet
#print axioms SimpleGraph.adjoinVertex

-- ExtensionGraph.lean
#print axioms SimpleGraph.adjoinVertexDecidableAdj
#print axioms SimpleGraph.adjoinVertex_adj_some_some
#print axioms SimpleGraph.adjoinVertex_adj_none_some
#print axioms SimpleGraph.adjoinVertex_adj_some_none
#print axioms SimpleGraph.not_adjoinVertex_adj_none_none
#print axioms SimpleGraph.adjoinVertexEmbedding
#print axioms SimpleGraph.Connected.adjoinVertex
#print axioms SimpleGraph.certificateIndicator
#print axioms SimpleGraph.IsRepresentation.of_adjoinVertex
#print axioms SimpleGraph.IsRepresentation.adjoinVertex

-- ExtensionGeometry.lean
#print axioms Matrix.IsGramCertificate.linearIndependent_gram
#print axioms Matrix.IsGramCertificate.span_gram
#print axioms Matrix.gramProjection
#print axioms Matrix.gramProjection_mem_span
#print axioms Matrix.inner_gramProjection
#print axioms Matrix.gramProjection_inner
#print axioms Matrix.gramProjection_inner_self
#print axioms Matrix.gramProjection_inner_eq_of_mem_span
#print axioms Matrix.gramProjection_inner_self_le
#print axioms Matrix.gramProjection_inner_self_eq_of_mem_span

-- ExtensionArithmetic.lean
#print axioms Matrix.intCast_inv_bilinear
#print axioms Matrix.dotProduct_adjugate_column
#print axioms Matrix.IsGramCertificate.gramProjection_inner
#print axioms Matrix.IsGramCertificate.gramProjection_inner_self

-- ExtensionRepresentation.lean
#print axioms SimpleGraph.IsRepresentation.isRepresentedIn_adjoinVertex_of_norm_le

-- Lemma 3.5, lem:admissible

-- Admissible.lean
#print axioms SimpleGraph.isRepresentedIn_adjoinVertex_iff_exists_admissible
#print axioms SimpleGraph.existsUnique_admissible_of_isRepresentedIn_adjoinVertex

-- CertificateDefs.lean
#print axioms Matrix.IsAdmissible
#print axioms Matrix.admissibleNeighbors

-- Admissible.lean
#print axioms Matrix.certificateCoordinates_apply_basis
#print axioms Matrix.vecMul_certificateCoordinates_basis
#print axioms Matrix.mem_admissibleNeighbors_basis_iff
#print axioms Matrix.admissibleNeighbors_zero
#print axioms Matrix.IsAdmissible.neighbors_nonempty
#print axioms Matrix.certificateIndicator_admissibleNeighbors
#print axioms Matrix.admissibleNeighbors_inj
#print axioms SimpleGraph.isRepresentedIn_adjoinVertex_admissibleNeighbors
#print axioms SimpleGraph.admissible_certificateIndicator_of_isRepresentedIn_adjoinVertex

-- Theorem 3.6, thm:growth

-- Growth.lean
#print axioms SimpleGraph.growth_represents_levels

-- CertificateDefs.lean
#print axioms SimpleGraph.levels
#print axioms SimpleGraph.CanonicalForm
#print axioms SimpleGraph.CertificateChoice
#print axioms SimpleGraph.growthChildren
#print axioms SimpleGraph.growth

-- CertificateExistence.lean
#print axioms SimpleGraph.certificateChoice

-- GrowthStructure.lean
#print axioms SimpleGraph.Iso.adjoinVertex
#print axioms SimpleGraph.Iso.adjoinVertexInduceCompl
#print axioms SimpleGraph.mem_levels_of_iso
#print axioms SimpleGraph.bot_mem_levels_one
#print axioms SimpleGraph.levels_eq_empty_of_ge
#print axioms SimpleGraph.exists_parent_of_mem_levels
#print axioms SimpleGraph.CanonicalForm.idempotent
#print axioms SimpleGraph.canon_eq_self_of_mem_growth
#print axioms SimpleGraph.eq_of_mem_growth_of_iso

-- Growth.lean
#print axioms SimpleGraph.mem_growthChildren_iff
#print axioms SimpleGraph.growthChildren_eq
#print axioms SimpleGraph.growth_sound_and_complete_succ
#print axioms SimpleGraph.growth_subset_levels
#print axioms SimpleGraph.existsUnique_mem_growth_iso
#print axioms SimpleGraph.growth_eq_empty_of_ge

-- Theorem C.1, thm:main

-- Main.lean
#print axioms SimpleGraph.isExceptional_and_not_posDef_iff
#print axioms SimpleGraph.isExceptional_and_posDef_iff
#print axioms SimpleGraph.singularExceptionalGrowth_represents
#print axioms SimpleGraph.definiteExceptionalGrowth_represents
#print axioms SimpleGraph.IsExceptional.card_bounds
#print axioms SimpleGraph.IsExceptional.card_mem_of_posDef
#print axioms Matrix.PosSemidef.posDef_iff_rank_eq
#print axioms SimpleGraph.exceptionalRankDetPairs
#print axioms SimpleGraph.Iso.posDef_two_add_adjMatrix_iff
#print axioms SimpleGraph.IsExceptional.rank_mem
#print axioms SimpleGraph.isExceptional_iff_mem_levels_rank_latticeDet
#print axioms SimpleGraph.singularExceptionalGrowth
#print axioms SimpleGraph.definiteExceptionalGrowth
#print axioms SimpleGraph.mem_singularExceptionalGrowth_iff
#print axioms SimpleGraph.mem_definiteExceptionalGrowth_iff

-- Proposition 3.7 and following paragraph, prop:maximal

-- Maximal.lean
#print axioms SimpleGraph.IsExceptional.isMaximalExceptional_iff_no_admissible
#print axioms SimpleGraph.IsExceptional.isMaximalExceptional_iff_no_extension

-- Main.lean
#print axioms SimpleGraph.maximalExceptionalGrowth_represents

-- Maximal.lean
#print axioms SimpleGraph.IsRepresentedIn.comp_embedding
#print axioms SimpleGraph.IsGeneralizedLineGraph.of_embedding
#print axioms SimpleGraph.IsExceptional.isRepresentedIn_E₈
#print axioms SimpleGraph.IsExceptional.card_certificate_le_eight
#print axioms SimpleGraph.Iso.isExceptional_iff
#print axioms SimpleGraph.IsMaximalExceptional
#print axioms SimpleGraph.IsMaximalExceptional.embedding_surjective
#print axioms SimpleGraph.Connected.exists_adj_mem_notMem
#print axioms SimpleGraph.Embedding.adjoinVertex
#print axioms SimpleGraph.IsExceptional.adjoinVertex
#print axioms SimpleGraph.Iso.isMaximalExceptional_iff

-- Main.lean
#print axioms SimpleGraph.maximalExceptionalGrowth
#print axioms SimpleGraph.mem_maximalExceptionalGrowth_iff

#print axioms SimpleGraph.CanonicalForm.ofChoice
