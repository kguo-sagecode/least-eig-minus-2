/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.LatticeBasic
import LineGraphs.Exceptional.Lattice
import LineGraphs.Exceptional.LatticeRank
import LineGraphs.Exceptional.RootLatticeBasis
import LineGraphs.Exceptional.RootLatticeClassical
import LineGraphs.Exceptional.RootLattice
import LineGraphs.Exceptional.LatticeCoordinates
import LineGraphs.Exceptional.BasisDetAlgebra
import LineGraphs.Exceptional.BasisDet
import LineGraphs.Exceptional.E6NotSumSquares
import LineGraphs.Exceptional.LatticeIntegral
import LineGraphs.Exceptional.Types
import LineGraphs.Exceptional.ElementaryDivisorsAlgebra
import LineGraphs.Exceptional.ElementaryDivisorsMatrix
import LineGraphs.Exceptional.ElementaryDivisors
import LineGraphs.Exceptional.CertificateDefs
import LineGraphs.Exceptional.NonCut
import LineGraphs.Exceptional.CertificateSylvester
import LineGraphs.Exceptional.Certificate
import LineGraphs.Exceptional.CertificateExistence
import LineGraphs.Exceptional.E8Criterion
import LineGraphs.Exceptional.ExtensionGraph
import LineGraphs.Exceptional.ExtensionGeometry
import LineGraphs.Exceptional.ExtensionArithmetic
import LineGraphs.Exceptional.ExtensionRepresentation
import LineGraphs.Exceptional.Extension
import LineGraphs.Exceptional.Admissible
import LineGraphs.Exceptional.GrowthStructure
import LineGraphs.Exceptional.Growth
import LineGraphs.Exceptional.Maximal
import LineGraphs.Exceptional.Main

/-! # The exceptional-graphs note in Lean

Every module of the formalization of Sections 2 and 3 of the note
`exceptional/note/exceptional.tex` ([Exc]).
Section 2: the lattice of a representation and its determinant, `lem:rootlattice`,
`lem:snf`, `lem:basisdet`, `lem:E6Zm`, `prop:types` (1) and (2). Section 3: `lem:noncut`,
`def:certificate`, `lem:certificate`, `prop:types` (3), `lem:extension`, `lem:admissible`,
`thm:growth`, `prop:maximal` (Proposition 3.7). Appendix C: `thm:main` (Theorem C.1), and
the abstract sets representing the three lists. The database files, the program and
`labelg` are not verified. The separate axiom audit is `LineGraphs.Exceptional.Audit`.
-/
