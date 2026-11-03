/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Spectral.Gram
import LineGraphs.Spectral.Positivity

/-!
# Graph representations and extremal multiplicities

The graph assertions of Theorem 3.5 of the spectral toolkit and the Gram-matrix
lemma in `blueprint/sec4-leasteigenvalue.tex`. A representation has Gram matrix 2I+A.
-/

open Matrix Module

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A graph representation is a family whose Gram matrix is 2I plus adjacency:
squared norms are two, adjacent inner products are one, and other distinct
inner products are zero. No finiteness of the vertex set is needed for the definition. -/
def IsRepresentation (x : V → E) : Prop :=
  Matrix.gram ℝ x = (2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ

variable [Fintype V]

omit [Fintype V] in
/-- The Gram matrix of a graph representation is positive semidefinite. -/
theorem IsRepresentation.posSemidef [Finite V] {x : V → E} (hx : X.IsRepresentation x) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef := by
  -- Steps `gram-represent`, `s4gramfwd`: use positivity of a Gram matrix.
  have hp := Matrix.posSemidef_gram ℝ x
  rw [show Matrix.gram ℝ x = _ from hx] at hp
  exact hp

/-- The opening of Section 4 of [CGSS] (`lem:4-gram`); Theorem 3.5 of the spectral
toolkit: positivity of 2I+A is equivalent to a representation in ℝⁿ. -/
theorem exists_representation_iff_posSemidef :
    (∃ x : V → EuclideanSpace ℝ (Fin (Fintype.card V)), X.IsRepresentation x) ↔
      ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).PosSemidef := by
  constructor
  · rintro ⟨x, hx⟩
    exact hx.posSemidef X
  · intro hp
    -- Steps `gram-represent`, `s4gramback`: rank at most n supplies n-dimensional coordinates.
    have hr := Matrix.rank_le_card_width ((2 : ℝ) • 1 + X.adjMatrix ℝ)
    obtain ⟨x, hx⟩ := hp.exists_gram_euclideanSpace hr
    exact ⟨x, hx⟩

/-- The rank of 2I+A is the dimension of the span of any graph representation. -/
theorem IsRepresentation.rank_two_add_adjMatrix {x : V → E} (hx : X.IsRepresentation x) :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank =
      finrank ℝ (Submodule.span ℝ (Set.range x)) := by
  -- Step `gram-boundrank`: identify the represented matrix with the Gram matrix.
  have hr := Matrix.rank_gram_eq_finrank_span x
  rw [show Matrix.gram ℝ x = _ from hx] at hr
  exact hr

/-- Shifting by two turns the -2 eigenspace into the kernel of 2I+A. -/
theorem rank_two_add_adjMatrix_add_multiplicity_neg_two :
    ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank +
      X.eigenvalueMultiplicity (-2) = Fintype.card V := by
  let C : Matrix V V ℝ := (2 : ℝ) • 1 + X.adjMatrix ℝ
  -- Step `gram-minusmult`: compare the shifted kernel and the original eigenspace.
  have hker : Module.End.eigenspace (X.adjMatrix ℝ).toLin' (-2) = C.toLin'.ker := by
    ext x
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, toLin'_apply, toLin'_apply]
    change X.adjMatrix ℝ *ᵥ x = (-2 : ℝ) • x ↔ C *ᵥ x = 0
    simp only [C, add_mulVec, smul_mulVec, one_mulVec]
    constructor <;> intro hx
    · rw [hx, ← add_smul]; simp
    · ext u
      have hu := congrFun hx u
      simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hu ⊢
      linarith
  -- Step `gram-minusmult`: apply rank-nullity and the algebraic/geometric multiplicity bridge.
  have hrn := LinearMap.finrank_range_add_finrank_ker C.toLin'
  have hr : C.rank = finrank ℝ C.toLin'.range :=
    C.rank_eq_finrank_range_toLin (Pi.basisFun ℝ V) (Pi.basisFun ℝ V)
  rw [← hr, ← hker, ← (X.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank,
    finrank_pi] at hrn
  exact hrn

/-- Theorem 3.5 of the spectral toolkit: a representation in dimension ℓ forces -2 multiplicity at
least n-ℓ. -/
theorem IsRepresentation.multiplicity_neg_two_ge [FiniteDimensional ℝ E]
    {x : V → E} (hx : X.IsRepresentation x) :
    Fintype.card V - finrank ℝ E ≤ X.eigenvalueMultiplicity (-2) := by
  -- Steps `gram-boundrank`, `gram-minusmult`: the vector span has dimension at most ℓ.
  have hbound : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).rank ≤ finrank ℝ E := by
    rw [hx.rank_two_add_adjMatrix X]
    exact Submodule.finrank_le _
  have hr := X.rank_two_add_adjMatrix_add_multiplicity_neg_two
  omega

/-- Theorem 3.5 of the spectral toolkit: a representation in fewer dimensions than vertices has
least eigenvalue -2. -/
theorem IsRepresentation.leastEigenvalue_eq_neg_two_of_finrank_lt
    [Nonempty V] [FiniteDimensional ℝ E] {x : V → E} (hx : X.IsRepresentation x)
    (hdim : finrank ℝ E < Fintype.card V) : X.leastEigenvalue = -2 := by
  -- Step `s4gramsing`: a nonsingular Gram matrix would give too many independent vectors.
  have hdet : ((2 : ℝ) • (1 : Matrix V V ℝ) + X.adjMatrix ℝ).det = 0 := by
    by_contra hn
    have hgram : (Matrix.gram ℝ x).det ≠ 0 := by rwa [show Matrix.gram ℝ x = _ from hx]
    have hbound := (Matrix.linearIndependent_of_det_gram_ne_zero hgram).fintype_card_le_finrank
    omega
  exact X.leastEigenvalue_eq_neg_two_iff.mpr ⟨hx.posSemidef X, hdet⟩

/-- Shifting the negative adjacency matrix by two turns the 2 eigenspace into a kernel. -/
theorem rank_two_sub_adjMatrix_add_multiplicity_two :
    ((2 : ℝ) • (1 : Matrix V V ℝ) - X.adjMatrix ℝ).rank +
      X.eigenvalueMultiplicity 2 = Fintype.card V := by
  let C : Matrix V V ℝ := (2 : ℝ) • 1 - X.adjMatrix ℝ
  -- Step `gram-upperrank`: identify the kernel with the 2 eigenspace.
  have hker : Module.End.eigenspace (X.adjMatrix ℝ).toLin' 2 = C.toLin'.ker := by
    ext x
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, toLin'_apply, toLin'_apply]
    change X.adjMatrix ℝ *ᵥ x = (2 : ℝ) • x ↔ C *ᵥ x = 0
    simp only [C, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero, eq_comm]
  -- Step `gram-upperrank`: rank-nullity counts the remaining dimensions.
  have hrn := LinearMap.finrank_range_add_finrank_ker C.toLin'
  have hr : C.rank = finrank ℝ C.toLin'.range :=
    C.rank_eq_finrank_range_toLin (Pi.basisFun ℝ V) (Pi.basisFun ℝ V)
  rw [← hr, ← hker, ← (X.isHermitian_adjMatrix ℝ).eigenvalueMultiplicity_eq_finrank,
    finrank_pi] at hrn
  exact hrn

/-- The paragraph before Theorem 3.8 of [CGSS]; Theorem 3.5 of the spectral toolkit:
a Gram representation of 2I-A in dimension ℓ gives 2 multiplicity ≥ n-ℓ. -/
theorem multiplicity_two_ge_of_gram_representation [FiniteDimensional ℝ E]
    (x : V → E) (hx : Matrix.gram ℝ x = (2 : ℝ) • 1 - X.adjMatrix ℝ) :
    Fintype.card V - finrank ℝ E ≤ X.eigenvalueMultiplicity 2 := by
  -- Step `gram-upperrank`: Gram rank is bounded by the ambient dimension.
  have hbound : ((2 : ℝ) • (1 : Matrix V V ℝ) - X.adjMatrix ℝ).rank ≤ finrank ℝ E := by
    rw [← hx, Matrix.rank_gram_eq_finrank_span]
    exact Submodule.finrank_le _
  have hr := X.rank_two_sub_adjMatrix_add_multiplicity_two
  omega

/-- The upper-shift Gram representation bounds every adjacency eigenvalue by two. -/
theorem eigenvalue_le_two_of_gram_representation (x : V → E)
    (hx : Matrix.gram ℝ x = (2 : ℝ) • 1 - X.adjMatrix ℝ) :
    ∀ μ ∈ X.spectrumMultiset, μ ≤ 2 := by
  -- Step `gram-uppertop`: positivity of the upper shift gives the spectral upper bound.
  have hp := Matrix.posSemidef_gram ℝ x
  rw [hx] at hp
  exact ((X.isHermitian_adjMatrix ℝ).posSemidef_smul_one_sub_iff 2).mp hp

/-- The paragraph before Theorem 3.8 of [CGSS]; Theorem 3.5 of the spectral toolkit:
if an upper-shift Gram representation uses fewer dimensions than
vertices, the largest adjacency eigenvalue is exactly two. -/
theorem largestEigenvalue_eq_two_of_gram_representation [Nonempty V] [FiniteDimensional ℝ E]
    (x : V → E) (hx : Matrix.gram ℝ x = (2 : ℝ) • 1 - X.adjMatrix ℝ)
    (hdim : finrank ℝ E < Fintype.card V) : X.largestEigenvalue = 2 := by
  -- Step `gram-uppertop`: the lower multiplicity bound makes two occur in the spectrum.
  have hmult := X.multiplicity_two_ge_of_gram_representation x hx
  have hpos : 0 < X.eigenvalueMultiplicity 2 := by omega
  have hmem : (2 : ℝ) ∈ X.spectrumMultiset := Multiset.count_pos.mp hpos
  apply le_antisymm
  · exact X.eigenvalue_le_two_of_gram_representation x hx _
      (X.isHermitian_adjMatrix ℝ).largestEigenvalue_mem_spectrumMultiset
  · exact (X.isHermitian_adjMatrix ℝ).le_largestEigenvalue_of_mem hmem

end SimpleGraph
