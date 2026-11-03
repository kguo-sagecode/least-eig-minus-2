/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.SideClaims.Cuboctahedron
import LineGraphs.SideClaims.HadamardSpectra
import LineGraphs.SideClaims.Sylvester

/-! # Axiom audit of the side claims

The side claims of [CGSS] formalized here: the remark after
Definition 3.1 that the six diagonals of the cuboctahedron represent `A₃`, and the background
claims of Section 6 (the spectra of `PᵀP` and `PPᵀ`, the Sylvester matrices of every order `2^s`
and Hypothesis 6.1 for them, and the Sylvester case). Each line must print only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- [CGSS], the remark after Definition 3.1
#print axioms LineSystem.cuboctahedronVertices_eq
#print axioms LineSystem.ncard_cuboctahedronVertices
#print axioms LineSystem.IsCubeEdge.sym2_eq_of_midpoint_eq
#print axioms LineSystem.ncard_cubeEdges
#print axioms LineSystem.cuboctahedron
#print axioms LineSystem.cuboctahedron_Φ_inter_span_singleton
#print axioms LineSystem.numLines_cuboctahedron
#print axioms LineSystem.ncard_cuboctahedronDiagonals
#print axioms LineSystem.cuboctahedron_eq_Dn
#print axioms LineSystem.cuboctahedron.isoAn
#print axioms LineSystem.nonempty_iso_cuboctahedron_An

-- [CGSS], Section 6, the spectra of PᵀP and PPᵀ
#print axioms Matrix.IsHadamard.charpoly_transpose_hadamardPairs_mul
#print axioms Matrix.IsHadamard.charpoly_hadamardPairs_mul_transpose
#print axioms Matrix.IsHadamard.spectrumMultiset_transpose_hadamardPairs_mul
#print axioms Matrix.IsHadamard.spectrumMultiset_hadamardPairs_mul_transpose
#print axioms Matrix.IsHadamard.eigenvalueMultiplicity_transpose_hadamardPairs_mul_zero
#print axioms Matrix.IsHadamard.eigenvalueMultiplicity_transpose_hadamardPairs_mul_half_sq
#print axioms Matrix.IsHadamard.eigenvalueMultiplicity_hadamardPairs_mul_transpose_zero
#print axioms Matrix.IsHadamard.eigenvalueMultiplicity_hadamardPairs_mul_transpose_half_sq
#print axioms Matrix.IsHadamard.finrank_eigenspace_transpose_hadamardPairs_mul_zero
#print axioms Matrix.IsHadamard.finrank_eigenspace_transpose_hadamardPairs_mul_half_sq
#print axioms Matrix.IsHadamard.finrank_eigenspace_hadamardPairs_mul_transpose_zero
#print axioms Matrix.IsHadamard.finrank_eigenspace_hadamardPairs_mul_transpose_half_sq

-- [CGSS], Section 6, the Sylvester matrices
#print axioms Matrix.isHadamard_sylvester
#print axioms Matrix.sylvester_succ
#print axioms Matrix.sylvesterKronecker_eq_sylvester
#print axioms Matrix.sylvester_fourRowAgreement
#print axioms Matrix.hadamardRowProduct_sylvester_sylvesterEquiv
#print axioms Matrix.hadamardRowProduct_sylvester
#print axioms Matrix.exists_hadamardRowProduct_sylvester_eq
#print axioms Matrix.image_hadamardRowProduct_sylvester
#print axioms Matrix.card_image_hadamardRowProduct_sylvester
#print axioms Matrix.two_mul_card_filter_hadamardRowProduct_sylvester
#print axioms Matrix.inner_hadamardRowProduct_sylvester_of_ne
#print axioms Matrix.sylvester_lines
#print axioms Computations.C16.h2_eq_sylvester
#print axioms Computations.C16.h4_eq_sylvester
#print axioms Computations.C16.h8_eq_sylvester
#print axioms Computations.C16.h16_eq_sylvester
