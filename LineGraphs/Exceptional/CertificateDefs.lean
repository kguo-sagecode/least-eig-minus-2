/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.LatticeBasic
import LineGraphs.Representation.Basic
import LineGraphs.LineSystem.Models
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Integer certificates and the objects used in the growth

Definitions 3.2 and the definitions surrounding Lemmas 3.4--3.5 and Theorem 3.6 of [Exc].
The canonical form is an abstract parameter; no claim about `labelg` is made here.
-/

open Matrix

namespace Matrix

variable {V : Type*} [DecidableEq V]

-- Definition 3.2 [Exc]
/-- Definition `def:certificate` (Definition 3.2) of [Exc]: every leading principal
minor is positive in the specified ordering. The empty minor is included and equals one. -/
def HasPositiveLeadingMinors {R : Type*} [CommRing R] [PartialOrder R] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) R) : Prop :=
  ∀ (k : ℕ) (hk : k ≤ r), 0 < (G.submatrix (Fin.castLE hk) (Fin.castLE hk)).det

-- Definition 3.2 [Exc]
/-- Definition `def:certificate` (Definition 3.2) of [Exc]: the integer certificate
conditions on a specified set of indices. Symmetry of `M` is a hypothesis of the theorems. -/
structure IsGramCertificate (M : Matrix V V ℤ) (B : Finset V) : Prop where
  positive : ∃ e : Fin B.card ≃ B,
    HasPositiveLeadingMinors ((M.submatrix Subtype.val Subtype.val).submatrix e e)
  identity : (M.submatrix (Subtype.val : B → V) Subtype.val).det • M =
    M.submatrix id (Subtype.val : B → V) *
      (M.submatrix (Subtype.val : B → V) Subtype.val).adjugate *
      M.submatrix (Subtype.val : B → V) id

-- Lemma 2.4 / Lemma 3.4 [Exc]
/-- The principal matrix `G` used in `lem:basisdet` (Lemma 2.4) and
`lem:extension` (Lemma 3.4) of [Exc]. The index set `B` is arbitrary;
no certificate hypothesis is required to define this matrix. -/
def certificateMatrix (M : Matrix V V ℤ) (B : Finset V) : Matrix B B ℤ :=
  M.submatrix Subtype.val Subtype.val

-- Lemma 3.4 [Exc]
/-- The determinant `D` used in `lem:extension` (Lemma 3.4) of [Exc].
The index set `B` is arbitrary and need not be a certificate. -/
def certificateDet (M : Matrix V V ℤ) (B : Finset V) : ℤ :=
  (certificateMatrix M B).det

-- Lemma 2.4 / Lemma 3.4 [Exc]
/-- The integer matrix `C = adj(G) M[B,·]` in `lem:basisdet` (Lemma 2.4) and
`lem:extension` (Lemma 3.4) of [Exc]. The index set `B` is arbitrary;
no certificate hypothesis is required to define this matrix. -/
def certificateCoordinates (M : Matrix V V ℤ) (B : Finset V) : Matrix B V ℤ :=
  (certificateMatrix M B).adjugate * M.submatrix Subtype.val id

-- Lemma 3.5 [Exc]
/-- The predicate preceding `lem:admissible` (Lemma 3.5) of [Exc], including the
requirement that every entry of `s` is zero or one. -/
def IsAdmissible (M : Matrix V V ℤ) (B : Finset V) (s : B → ℤ) : Prop :=
  (∀ b, s b = 0 ∨ s b = 1) ∧
  (∀ u, (s ᵥ* certificateCoordinates M B) u = 0 ∨
    (s ᵥ* certificateCoordinates M B) u = certificateDet M B) ∧
  s ⬝ᵥ ((certificateMatrix M B).adjugate *ᵥ s) ≤ 2 * certificateDet M B ∧
  (B.card = 8 → s ⬝ᵥ ((certificateMatrix M B).adjugate *ᵥ s) = 2 * certificateDet M B)

-- Lemma 3.5 [Exc]
/-- The set `N_s` preceding `lem:admissible` (Lemma 3.5) of [Exc]. -/
def admissibleNeighbors (M : Matrix V V ℤ) (B : Finset V) (s : B → ℤ) : Set V :=
  {u | (s ᵥ* certificateCoordinates M B) u = certificateDet M B}

end Matrix

namespace SimpleGraph

variable {V : Type*}

-- Lemma 3.4 [Exc]
/-- The graph `X_N` in `lem:extension` (Lemma 3.4) of [Exc]; `none` is the new vertex. -/
def adjoinVertex (X : SimpleGraph V) (N : Set V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some v => v ∈ N
    | some v, none => v ∈ N
    | some v, some w => X.Adj v w
  symm.symm := by
    rintro (_ | v) (_ | w) <;> simp only <;> try tauto
  loopless.irrefl := by
    rintro (_ | v)
    · exact not_false
    · exact X.loopless.irrefl v

-- Theorem 3.6 [Exc]
/-- The levels preceding `thm:growth` (Theorem 3.6) of [Exc], as sets of labelled graphs.
The representation condition is equivalent to positive semidefiniteness and rank at
most eight by `isRepresentedIn_E₈_iff_posSemidef_and_rank_le`. The note's isomorphism
classes are those of these labelled graphs and are handled by `CanonicalForm`. -/
noncomputable def levels (n : ℕ) : Set (SimpleGraph (Fin n)) := by
  classical
  exact {X | X.Connected ∧ X.IsRepresentedIn LineSystem.E₈}

-- Theorem 3.6 [Exc]
/-- The abstract canonical form preceding `thm:growth` (Theorem 3.6) of [Exc]. -/
structure CanonicalForm where
  canon : ∀ {n : ℕ}, SimpleGraph (Fin n) → SimpleGraph (Fin n)
  iso : ∀ {n : ℕ} (X : SimpleGraph (Fin n)), canon X ≃g X
  eq_iff : ∀ {n : ℕ} (X Y : SimpleGraph (Fin n)),
    canon X = canon Y ↔ Nonempty (X ≃g Y)

-- Theorem 3.6 [Exc]
/-- The certificate choice in `thm:growth` (Theorem 3.6) of [Exc]. Validity is required
only for positive semidefinite graphs, including the empty graph. -/
structure CertificateChoice where
  indices : ∀ {n : ℕ}, SimpleGraph (Fin n) → Finset (Fin n)
  valid : ∀ {n : ℕ} (X : SimpleGraph (Fin n)),
    letI := Classical.decRel X.Adj
    ((2 : ℝ) • 1 + X.adjMatrix ℝ).PosSemidef →
      X.integralGramMatrix.IsGramCertificate (indices X)

-- Theorem 3.6 [Exc]
/-- The children in `thm:growth` (Theorem 3.6) of [Exc], reindexed onto `Fin (n+1)`.
The certificate and the nonzero admissible vector are used exactly as in the note. -/
noncomputable def growthChildren (c : CertificateChoice) {n : ℕ}
    (X : SimpleGraph (Fin n)) : Set (SimpleGraph (Fin (n + 1))) := by
  classical
  exact {Y | ∃ s : c.indices X → ℤ, s ≠ 0 ∧
    X.integralGramMatrix.IsAdmissible (c.indices X) s ∧
    Y = (X.adjoinVertex (X.integralGramMatrix.admissibleNeighbors (c.indices X) s)).comap
      (finSuccEquiv n)}

-- Theorem 3.6 [Exc]
/-- The recursively generated sets in `thm:growth` (Theorem 3.6) of [Exc]. The unused
zeroth set is empty; at one vertex the unique graph is `⊥ = K₁`. -/
noncomputable def growth (c : CertificateChoice) (q : CanonicalForm) :
    (n : ℕ) → Set (SimpleGraph (Fin n))
  | 0 => ∅
  | 1 => {⊥}
  | n + 2 => {Y | ∃ X ∈ growth c q (n + 1), ∃ Z ∈ growthChildren c X, Y = q.canon Z}

end SimpleGraph
