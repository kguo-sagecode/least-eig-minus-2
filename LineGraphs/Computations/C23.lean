/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.Example513
import LineGraphs.Cited.HallConnor.Complement
import LineGraphs.Computations.C9Petersen

/-!
# C23: the designs of the remark in Example 5.13 of [CGSS]

Example 5.13 of [CGSS] (`Design.not_flagGraphCharacterized_of_resolvable`) turns a resolvable
`2`-design `D'` with parameters `(k(2k-1), k, 4k²-1, 2k+1, 1)` into a cospectral mate of the
flag graph of any design `D₁` with parameters
`(k(2k-1), (k-1)(2k-1), k(2k+1), (k-1)(2k+1), k(2k-3))` (p. 325). This module supplies
the explicit designs for the paper's own instances, with every design property checked by
`decide +kernel`. Page references are to [CGSS], J. Algebra 43 (1976), 305–327. The data come from
`cgss/certificates/c23_lean_data.py`.

## Main statements

* `Computations.C23.not_flagGraphCharacterized_6_3_10_5_2`: Example 5.13 (p. 325) for
  `k = 2`, the flag graph of the `(6,3,10,5,2)` design `Computations.C15.design` is not
  characterized by its spectrum. Here `D'` is `Computations.C23.oneFactorDesign`, the edges of
  `K₆`, resolved by the one-factorization `Computations.C23.oneFactorization`.
* `Computations.C23.pairGraphIso` and `Computations.C23.petersenLineGraphIso`: Example 5.13
  (p. 325), for `k = 2` the graph `H` is the graph on the pairs of points of `D₁`, two
  pairs adjacent when their union is a block (`Design.pairGraph`), and it is the line graph of
  the Petersen graph.
* `Computations.C23.false_of_parameters_three`: Example 5.13 (p. 325), for `k = 3` the
  design `D₁` does not exist; its parameters are `(15,10,21,14,9)`
  (`Computations.C23.parameters_three`), the case `s = 5`, `t = 2` of Remark 5.12, excluded by
  Hall–Connor through the complementary parameters `(15,5,21,7,2)`.
* `Computations.C23.not_flagGraphCharacterized_28_21_36_27_20`: Example 5.13 (p. 325)
  for `k = 4`, with `D'` the dual of a hyperoval in the projective plane of order `8`
  (`Computations.C23.hyperovalDesign`, resolution `Computations.C23.hyperovalResolution`) and
  `D₁` the complement of the residual of the `(37,9,2)` biplane of quartic residues mod `37`
  (`Computations.C23.complementDesign`; the biplane is `Computations.C23.biplaneDesign` and the
  residual is checked in `Computations.C23.image_residualBlocks`).
-/

namespace Design

variable {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P] [DecidableEq B]
  {v k b r lam : ℕ}

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325): the graph on the pairs of points of a design, two
pairs being adjacent whenever their union is a block. -/
def pairGraph (D : Design P B v k b r lam) : SimpleGraph {s : Finset P // s.card = 2} where
  Adj s t := s ≠ t ∧ ∃ label, s.val ∪ t.val = D.block label
  symm.symm := fun _ _ ⟨h, label, hl⟩ ↦ ⟨Ne.symm h, label, by rw [Finset.union_comm, hl]⟩
  loopless.irrefl := fun _ h ↦ h.1 rfl

-- Example 5.13
/-- Decidable adjacency in `Design.pairGraph`, Example 5.13 of [CGSS] (p. 325). -/
instance pairGraphDecidable (D : Design P B v k b r lam) : DecidableRel D.pairGraph.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

namespace Resolution

-- Example 5.13
/-- Decidable adjacency in the graph `H` of Example 5.13 of [CGSS] (p. 325). It is a
local instance of this module only, so that it does not compete with the classical instances
of the Example 5.13 modules. -/
local instance graphDecidable {c : ℕ} {D : Design P B v k b r lam} (R : D.Resolution c) :
    DecidableRel R.graph.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- Example 5.13
/-- A resolution given by a table of parallel classes, assumption 2 of Example 5.13 of [CGSS]
(p. 325): the blocks are labelled by a class and a position, and the blocks of each class
cover every point exactly once. -/
def ofTable {P : Type*} [Fintype P] [DecidableEq P] {c m : ℕ}
    (D : Design P (Fin c × Fin m) v k b r lam)
    (hcover : ∀ i p, ∃ j, p ∈ D.block (i, j))
    (hdisj : ∀ i j j' p, p ∈ D.block (i, j) → p ∈ D.block (i, j') → j = j') :
    D.Resolution c where
  classOf := Prod.fst
  unique_block i p := by
    obtain ⟨j, hj⟩ := hcover i p
    refine ⟨(i, j), ⟨rfl, hj⟩, ?_⟩
    rintro ⟨i', j'⟩ ⟨hi, hj'⟩
    dsimp only at hi
    subst hi
    rw [hdisj i' j' j p hj' hj]

end Resolution

end Design

namespace Computations.C23

attribute [local instance] Design.Resolution.graphDecidable

/-! ### The case `k = 2` -/

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the one-factorization `GK₆`
of `K₆`, with the points `0, …, 4` of `ℤ/5` and `∞ = 5`; factor `i` is
`{i, ∞}, {i + 1, i - 1}, {i + 2, i - 2}`. -/
def oneFactors : Fin 5 → Fin 3 → Finset (Fin 6) :=
  ![![{0, 5}, {1, 4}, {2, 3}],
    ![{1, 5}, {0, 2}, {3, 4}],
    ![{2, 5}, {1, 3}, {0, 4}],
    ![{3, 5}, {2, 4}, {0, 1}],
    ![{4, 5}, {0, 3}, {1, 2}]]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the design `D'` with parameters
`(6,2,15,5,1)`, whose blocks are the edges of `K₆`. -/
def oneFactorDesign : Design (Fin 6) (Fin 5 × Fin 3) 6 2 15 5 1 where
  card_points := rfl
  card_blocks := rfl
  block x := oneFactors x.1 x.2
  card_block := by decide +kernel
  card_blocksThrough := by decide +kernel
  card_blocksThroughPair := by decide +kernel
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the five one-factors resolve `D'`. -/
def oneFactorization : oneFactorDesign.Resolution 5 :=
  Design.Resolution.ofTable oneFactorDesign (by decide +kernel) (by decide +kernel)

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the flag graph of the design `D₁` with
parameters `(6,3,10,5,2)` (`Computations.C15.design`, whose properties C15 checks by
`decide +kernel`) is not characterized by its spectrum, from the resolution
`oneFactorization`. (`Computations.C15.not_flagGraphCharacterized` proves the same from the
C15 certificate.) -/
theorem not_flagGraphCharacterized_6_3_10_5_2 : ¬ C15.design.FlagGraphCharacterized :=
  Design.not_flagGraphCharacterized_of_resolvable (k := 2) C15.design oneFactorDesign
    oneFactorization

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the pair of points of `D₁` assigned to
each block of `D'`. -/
def pairLabel : Fin 5 → Fin 3 → {s : Finset (Fin 6) // s.card = 2} :=
  ![![⟨{1, 2}, by decide⟩, ⟨{3, 4}, by decide⟩, ⟨{0, 5}, by decide⟩],
    ![⟨{3, 5}, by decide⟩, ⟨{2, 4}, by decide⟩, ⟨{0, 1}, by decide⟩],
    ![⟨{1, 4}, by decide⟩, ⟨{2, 5}, by decide⟩, ⟨{0, 3}, by decide⟩],
    ![⟨{2, 3}, by decide⟩, ⟨{1, 5}, by decide⟩, ⟨{0, 4}, by decide⟩],
    ![⟨{4, 5}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{0, 2}, by decide⟩]]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: `H` is the graph on the pairs of points of
`D₁`, two pairs being adjacent whenever their union is a block. -/
noncomputable def pairGraphIso : oneFactorization.graph ≃g C15.design.pairGraph where
  toEquiv := Equiv.ofBijective (fun x ↦ pairLabel x.1 x.2) (by decide +kernel)
  map_rel_iff' := by decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the pair-graph description of `H`. -/
theorem nonempty_iso_pairGraph : Nonempty (oneFactorization.graph ≃g C15.design.pairGraph) :=
  ⟨pairGraphIso⟩

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the edge of `SimpleGraph.petersen`
assigned to each block of `D'`. -/
def petersenLabel : Fin 5 → Fin 3 → Fin 10 × Fin 10 :=
  ![![(2, 3), (0, 1), (4, 7)],
    ![(5, 7), (1, 6), (2, 9)],
    ![(0, 9), (3, 6), (7, 8)],
    ![(1, 8), (3, 5), (4, 9)],
    ![(4, 6), (0, 5), (2, 8)]]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the labels are edges of the Petersen
graph. -/
theorem petersen_adj_petersenLabel :
    ∀ x : Fin 5 × Fin 3, SimpleGraph.petersen.Adj (petersenLabel x.1 x.2).1
      (petersenLabel x.1 x.2).2 := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the blocks of `D'` as edges of the
Petersen graph. -/
def petersenEdge (x : Fin 5 × Fin 3) : SimpleGraph.petersen.edgeSet :=
  ⟨s((petersenLabel x.1 x.2).1, (petersenLabel x.1 x.2).2), petersen_adj_petersenLabel x⟩

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: `H` is the line graph of the Petersen
graph. -/
noncomputable def petersenLineGraphIso :
    oneFactorization.graph ≃g SimpleGraph.petersen.lineGraph where
  toEquiv := Equiv.ofBijective petersenEdge (by decide +kernel)
  map_rel_iff' := by decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 2`: the line-graph description of `H`. -/
theorem nonempty_iso_petersen_lineGraph :
    Nonempty (oneFactorization.graph ≃g SimpleGraph.petersen.lineGraph) :=
  ⟨petersenLineGraphIso⟩

/-! ### The case `k = 3` -/

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 3`: the parameters of `D₁` are
`(15,10,21,14,9)`, and `s = 2k - 1 = 5`, `t = k - 1 = 2`. -/
theorem parameters_three :
    (3 * (2 * 3 - 1), (3 - 1) * (2 * 3 - 1), 3 * (2 * 3 + 1), (3 - 1) * (2 * 3 + 1),
      3 * (2 * 3 - 3)) = (15, 10, 21, 14, 9) ∧ 2 * 3 - 1 = 5 ∧ 3 - 1 = 2 := by
  decide

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 3`: these are the parameters of Theorem 5.8,
case (iii), with `s = 5` and `t = 2`, the second case of Remark 5.12 (p. 325), through
`Design.nonbipartiteParameters_and_even_resolution_family`. -/
theorem nonbipartiteParameters_three : Design.NonbipartiteParameters 15 10 21 14 9 5 2 :=
  (Design.nonbipartiteParameters_and_even_resolution_family (k := 3) (by decide)).1

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 3`: "the design `D₁` does not exist, cf.
Remark 5.12". Its parameters are `(15,10,21,14,9)`, and its complement would be a
`(15,5,21,7,2)` design, which Hall–Connor excludes (`Design.false_of_parameters_15_10_9`,
as in the Lean of Remark 5.12, `Design.flagGraphCharacterized_of_lam_lt_nineteen`;
p. 325). -/
theorem false_of_parameters_three {P B : Type*} [Fintype P] [Fintype B] [DecidableEq P]
    [DecidableEq B] (D : Design P B (3 * (2 * 3 - 1)) ((3 - 1) * (2 * 3 - 1)) (3 * (2 * 3 + 1))
      ((3 - 1) * (2 * 3 + 1)) (3 * (2 * 3 - 3))) : False :=
  D.false_of_parameters_15_10_9

/-! ### The case `k = 4` -/

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the dual of a hyperoval `O` in the
projective plane of order `8`. Over `GF(8) = GF(2)[x]/(x³ + x + 1)`, `O` is the conic
`{(1,t,t²)}` with `(0,0,1)` and `(0,1,0)`. The points of `D'` are the `28` lines missing `O`;
the blocks are the `63` points off `O`, each the set of the four external lines through it;
class `i` consists of the seven points off `O` on the `i`-th line through `(0,0,1) ∈ O`. -/
def hyperovalBlocks : Fin 9 → Fin 7 → Finset (Fin 28) :=
  ![![{0, 4, 12, 20}, {2, 9, 22, 27}, {10, 15, 18, 23}, {3, 7, 11, 19}, {5, 16, 21, 24},
      {1, 13, 17, 25}, {6, 8, 14, 26}],
    ![{0, 5, 14, 23}, {2, 4, 8, 19}, {7, 17, 21, 26}, {3, 12, 18, 25}, {6, 10, 13, 27},
      {1, 9, 20, 24}, {11, 15, 16, 22}],
    ![{0, 1, 2, 3}, {6, 16, 23, 25}, {4, 11, 13, 24}, {5, 9, 15, 26}, {8, 12, 17, 22},
      {10, 14, 19, 21}, {7, 18, 20, 27}],
    ![{4, 5, 6, 7}, {9, 13, 18, 21}, {11, 14, 17, 20}, {2, 12, 16, 26}, {0, 10, 22, 25},
      {1, 15, 19, 27}, {3, 8, 23, 24}],
    ![{8, 9, 10, 11}, {3, 14, 16, 27}, {5, 19, 20, 25}, {1, 6, 12, 21}, {2, 7, 13, 23},
      {4, 18, 22, 26}, {0, 15, 17, 24}],
    ![{12, 13, 14, 15}, {6, 19, 22, 24}, {1, 5, 8, 18}, {4, 17, 23, 27}, {3, 10, 20, 26},
      {0, 7, 9, 16}, {2, 11, 21, 25}],
    ![{16, 17, 18, 19}, {1, 11, 23, 26}, {7, 10, 12, 24}, {0, 8, 21, 27}, {4, 9, 14, 25},
      {2, 6, 15, 20}, {3, 5, 13, 22}],
    ![{20, 21, 22, 23}, {7, 8, 15, 25}, {0, 13, 19, 26}, {3, 6, 9, 17}, {2, 14, 18, 24},
      {5, 11, 12, 27}, {1, 4, 10, 16}],
    ![{24, 25, 26, 27}, {2, 5, 10, 17}, {3, 4, 15, 21}, {1, 7, 14, 22}, {8, 13, 16, 20},
      {0, 6, 11, 18}, {9, 12, 19, 23}]]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the design `D'` with
parameters `(28,4,63,9,1)`. -/
def hyperovalDesign : Design (Fin 28) (Fin 9 × Fin 7) 28 4 63 9 1 where
  card_points := rfl
  card_blocks := rfl
  block x := hyperovalBlocks x.1 x.2
  card_block := by decide +kernel
  card_blocksThrough := by decide +kernel
  card_blocksThroughPair := by decide +kernel
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the nine pencils resolve `D'`. -/
def hyperovalResolution : hyperovalDesign.Resolution 9 :=
  Design.Resolution.ofTable hyperovalDesign (by decide +kernel) (by decide +kernel)

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the base block of the `(37,9,2)` biplane,
the quartic residues mod `37`. -/
def quarticResidues : Finset (Fin 37) := {1, 7, 9, 10, 12, 16, 26, 33, 34}

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: `quarticResidues` is the set of nonzero
fourth powers mod `37`. -/
theorem quarticResidues_eq_image :
    quarticResidues = (Finset.univ.erase 0).image (fun t : Fin 37 ↦ t * t * t * t) := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: `quarticResidues` is a `(37,9,2)`
difference set, every nonzero residue being a difference of two of its elements in exactly two
ways. -/
theorem card_filter_sub_quarticResidues : ∀ d : Fin 37, d ≠ 0 →
    ((quarticResidues ×ˢ quarticResidues).filter (fun x ↦ x.1 - x.2 = d)).card = 2 := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the blocks of the biplane, block `t`
being the translate of `quarticResidues` by `t` (`biplaneBlocks_eq`). -/
def biplaneBlocks : Fin 37 → Finset (Fin 37) :=
  ![{1, 7, 9, 10, 12, 16, 26, 33, 34}, {2, 8, 10, 11, 13, 17, 27, 34, 35},
    {3, 9, 11, 12, 14, 18, 28, 35, 36}, {0, 4, 10, 12, 13, 15, 19, 29, 36},
    {0, 1, 5, 11, 13, 14, 16, 20, 30}, {1, 2, 6, 12, 14, 15, 17, 21, 31},
    {2, 3, 7, 13, 15, 16, 18, 22, 32}, {3, 4, 8, 14, 16, 17, 19, 23, 33},
    {4, 5, 9, 15, 17, 18, 20, 24, 34}, {5, 6, 10, 16, 18, 19, 21, 25, 35},
    {6, 7, 11, 17, 19, 20, 22, 26, 36}, {0, 7, 8, 12, 18, 20, 21, 23, 27},
    {1, 8, 9, 13, 19, 21, 22, 24, 28}, {2, 9, 10, 14, 20, 22, 23, 25, 29},
    {3, 10, 11, 15, 21, 23, 24, 26, 30}, {4, 11, 12, 16, 22, 24, 25, 27, 31},
    {5, 12, 13, 17, 23, 25, 26, 28, 32}, {6, 13, 14, 18, 24, 26, 27, 29, 33},
    {7, 14, 15, 19, 25, 27, 28, 30, 34}, {8, 15, 16, 20, 26, 28, 29, 31, 35},
    {9, 16, 17, 21, 27, 29, 30, 32, 36}, {0, 10, 17, 18, 22, 28, 30, 31, 33},
    {1, 11, 18, 19, 23, 29, 31, 32, 34}, {2, 12, 19, 20, 24, 30, 32, 33, 35},
    {3, 13, 20, 21, 25, 31, 33, 34, 36}, {0, 4, 14, 21, 22, 26, 32, 34, 35},
    {1, 5, 15, 22, 23, 27, 33, 35, 36}, {0, 2, 6, 16, 23, 24, 28, 34, 36},
    {0, 1, 3, 7, 17, 24, 25, 29, 35}, {1, 2, 4, 8, 18, 25, 26, 30, 36},
    {0, 2, 3, 5, 9, 19, 26, 27, 31}, {1, 3, 4, 6, 10, 20, 27, 28, 32},
    {2, 4, 5, 7, 11, 21, 28, 29, 33}, {3, 5, 6, 8, 12, 22, 29, 30, 34},
    {4, 6, 7, 9, 13, 23, 30, 31, 35}, {5, 7, 8, 10, 14, 24, 31, 32, 36},
    {0, 6, 8, 9, 11, 15, 25, 32, 33}]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the blocks of the biplane are the
translates of the base block. -/
theorem biplaneBlocks_eq : ∀ t, biplaneBlocks t = quarticResidues.image (· + t) := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the `(37,9,37,9,2)` biplane. -/
def biplaneDesign : Design (Fin 37) (Fin 37) 37 9 37 9 2 where
  card_points := rfl
  card_blocks := rfl
  block := biplaneBlocks
  card_block := by decide +kernel
  card_blocksThrough := by decide +kernel
  card_blocksThroughPair := by decide +kernel
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the `28` points off the base block, in
increasing order. -/
def residualPoints : Fin 28 → Fin 37 :=
  ![0, 2, 3, 4, 5, 6, 8, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30,
    31, 32, 35, 36]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: `residualPoints` numbers the points off
the base block without repetition. -/
theorem residualPoints_injective : Function.Injective residualPoints := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: `residualPoints` numbers all the points
off the base block. -/
theorem image_residualPoints : Finset.univ.image residualPoints = quarticResiduesᶜ := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the residual of the `(37,9,2)` biplane
with base block the quartic residues `{1,7,9,10,12,16,26,33,34}` mod `37`, with respect to
that block. The `28` points off the base block are numbered in increasing order
(`residualPoints`), and block `t - 1` is the translate by `t` of the base block, minus the base
block (`image_residualBlocks`). -/
def residualBlocks : Fin 36 → Finset (Fin 28) :=
  ![{1, 6, 7, 8, 11, 20, 26}, {2, 7, 9, 12, 21, 26, 27}, {0, 3, 8, 10, 13, 22, 27},
    {0, 4, 7, 8, 9, 14, 23}, {1, 5, 9, 10, 11, 15, 24}, {1, 2, 8, 10, 12, 16, 25},
    {2, 3, 6, 9, 11, 13, 17}, {3, 4, 10, 11, 12, 14, 18}, {4, 5, 12, 13, 15, 19, 26},
    {5, 7, 11, 13, 14, 16, 27}, {0, 6, 12, 14, 15, 17, 20}, {6, 8, 13, 15, 16, 18, 21},
    {1, 9, 14, 16, 17, 19, 22}, {2, 7, 10, 15, 17, 18, 23}, {3, 7, 16, 18, 19, 20, 24},
    {4, 8, 11, 17, 19, 21, 25}, {5, 8, 9, 12, 18, 20, 22}, {9, 10, 13, 19, 20, 21, 23},
    {6, 10, 14, 21, 22, 24, 26}, {11, 15, 20, 22, 23, 25, 27}, {0, 11, 12, 16, 21, 23, 24},
    {7, 12, 13, 17, 22, 24, 25}, {1, 13, 14, 18, 23, 25, 26}, {2, 8, 14, 15, 19, 24, 27},
    {0, 3, 9, 15, 16, 25, 26}, {4, 10, 16, 17, 20, 26, 27}, {0, 1, 5, 17, 18, 21, 27},
    {0, 2, 11, 18, 19, 22, 26}, {1, 3, 6, 12, 19, 23, 27}, {0, 1, 2, 4, 13, 20, 24},
    {2, 3, 5, 14, 20, 21, 25}, {1, 3, 4, 7, 15, 21, 22}, {2, 4, 5, 6, 16, 22, 23},
    {3, 5, 8, 17, 23, 24, 26}, {4, 6, 9, 18, 24, 25, 27}, {0, 5, 6, 7, 10, 19, 25}]

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: `residualBlocks` is the residual of the
biplane with respect to its base block. -/
theorem image_residualBlocks : ∀ t : Fin 36,
    (residualBlocks t).image residualPoints = biplaneBlocks t.succ \ quarticResidues := by
  decide +kernel

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the residual design, with parameters
`(28,7,36,9,2)`. -/
def residualDesign : Design (Fin 28) (Fin 36) 28 7 36 9 2 where
  card_points := rfl
  card_blocks := rfl
  block := residualBlocks
  card_block := by decide +kernel
  card_blocksThrough := by decide +kernel
  card_blocksThroughPair := by decide +kernel
  one_lt_v := by decide
  one_lt_k := by decide
  b_pos := by decide

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the design `D₁` with parameters
`(28,21,36,27,20)`, the complement of `residualDesign`. -/
def complementDesign : Design (Fin 28) (Fin 36) 28 21 36 27 20 :=
  residualDesign.compl (by decide)

-- Example 5.13
/-- Example 5.13 of [CGSS] (p. 325), `k = 4`: the flag graph of the design `D₁` with
parameters `(28,21,36,27,20)` is not characterized by its spectrum. -/
theorem not_flagGraphCharacterized_28_21_36_27_20 :
    ¬ complementDesign.FlagGraphCharacterized :=
  Design.not_flagGraphCharacterized_of_resolvable (k := 4) complementDesign hyperovalDesign
    hyperovalResolution

end Computations.C23
