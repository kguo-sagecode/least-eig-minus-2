/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.CocktailParty
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# The eight-vertex models of SE4

The labellings are those of Definition 1.1 and Section 2 of `cgss/proofs/reg8/reg8.tex`,
the input `res:414-SE4` to Remark 4.14 of [CGSS].
-/

namespace SimpleGraph

/-- Decidable adjacency for the disjoint unions used in SE4. -/
instance decidableAdjSum {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  rintro (u | u) (v | v) <;> dsimp [SimpleGraph.sum] <;> infer_instance

-- SE4 (Remark 4.14)
/-- SE4's matching with edges `01`, `23`, `45`, `67`. -/
def fourK2 : SimpleGraph (Fin 8) := fromRel fun i j ↦ i.val / 2 = j.val / 2

-- SE4 (Remark 4.14)
/-- SE4's disjoint cycles on `0,1,2` and `3,4,5,6,7`. -/
def cycleThreeFive : SimpleGraph (Fin 8) :=
  fromEdgeSet (↑({s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 6), s(6, 7),
    s(7, 3)} : Finset (Sym2 (Fin 8))))

-- SE4 (Remark 4.14)
/-- SE4's disjoint cycles on `0,1,2,3` and `4,5,6,7`. -/
def twoC4 : SimpleGraph (Fin 8) :=
  fromEdgeSet (↑({s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(4, 5), s(5, 6), s(6, 7),
    s(7, 4)} : Finset (Sym2 (Fin 8))))

-- SE4 (Remark 4.14)
/-- SE4's complete graphs on `0,1,2,3` and `4,5,6,7`. -/
def twoK4 : SimpleGraph (Fin 8) := fromRel fun i j ↦ i.val / 4 = j.val / 4

-- Definition 1.1 (SE4)
/-- The eight-cycle with additional chords `P`, Definition 1.1 of SE4. -/
def cycleWithChords (P : Finset (Sym2 (Fin 8))) : SimpleGraph (Fin 8) :=
  cycleGraph 8 ⊔ fromEdgeSet (P : Set (Sym2 (Fin 8)))

-- Definition 1.1 (SE4)
/-- The cube `Q₃`: the eight-cycle with chords `03`, `16`, `25`, `47` (SE4). -/
def cubeGraph : SimpleGraph (Fin 8) := cycleWithChords {s(0, 3), s(1, 6), s(2, 5), s(4, 7)}

-- Definition 1.1 (SE4)
/-- The Wagner graph: the eight-cycle with chords `04`, `15`, `26`, `37` (SE4). -/
def wagnerGraph : SimpleGraph (Fin 8) := cycleWithChords {s(0, 4), s(1, 5), s(2, 6), s(3, 7)}

-- Definition 1.1 (SE4)
/-- SE4's `Y₁`, obtained by truncating one vertex of `K₃,₃`: the eight-cycle
with chords `02`, `15`, `36`, `47`. -/
def truncatedK33Graph : SimpleGraph (Fin 8) :=
  cycleWithChords {s(0, 2), s(1, 5), s(3, 6), s(4, 7)}

-- Definition 1.1 (SE4)
/-- SE4's `Y₂`, obtained by truncating two vertices of `K₄`: the eight-cycle
with chords `02`, `15`, `37`, `46`. -/
def twiceTruncatedK4Graph : SimpleGraph (Fin 8) :=
  cycleWithChords {s(0, 2), s(1, 5), s(3, 7), s(4, 6)}

-- Definition 1.1 (SE4)
/-- SE4's `Y₄`, two diamonds joined at their degree-two vertices: the eight-cycle
with chords `02`, `13`, `46`, `57`. -/
def twoDiamondsGraph : SimpleGraph (Fin 8) :=
  cycleWithChords {s(0, 2), s(1, 3), s(4, 6), s(5, 7)}

instance : DecidableRel fourK2.Adj := by unfold fourK2; infer_instance
instance : DecidableRel cycleThreeFive.Adj := by unfold cycleThreeFive; infer_instance
instance : DecidableRel twoC4.Adj := by unfold twoC4; infer_instance
instance : DecidableRel twoK4.Adj := by unfold twoK4; infer_instance
instance (P : Finset (Sym2 (Fin 8))) : DecidableRel (cycleWithChords P).Adj := by
  unfold cycleWithChords
  infer_instance
instance : DecidableRel cubeGraph.Adj := by unfold cubeGraph; infer_instance
instance : DecidableRel wagnerGraph.Adj := by unfold wagnerGraph; infer_instance
instance : DecidableRel truncatedK33Graph.Adj := by unfold truncatedK33Graph; infer_instance
instance : DecidableRel twiceTruncatedK4Graph.Adj := by unfold twiceTruncatedK4Graph; infer_instance
instance : DecidableRel twoDiamondsGraph.Adj := by unfold twoDiamondsGraph; infer_instance

/-- The matching model of SE4 is the complement of the cocktail party graph. -/
def fourK2.cocktailPartyComplIso : fourK2 ≃g (cocktailParty 4)ᶜ where
  toEquiv := ((Equiv.prodCongr (Equiv.refl (Fin 4)) finTwoEquiv.symm).trans
    finProdFinEquiv).symm
  map_rel_iff' := by decide +kernel

/-- The sum labelling of the `C₃ + C₅` model of SE4. -/
def cycleThreeFive.sumIso : (cycleGraph 3) ⊕g (cycleGraph 5) ≃g cycleThreeFive where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

/-- The sum labelling of the `2C₄` model of SE4. -/
def twoC4.sumIso : (cycleGraph 4) ⊕g (cycleGraph 4) ≃g twoC4 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

/-- The valency of the matching model of SE4. -/
theorem fourK2_isRegularOfDegree : fourK2.IsRegularOfDegree 1 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the `C₃ + C₅` model of SE4. -/
theorem cycleThreeFive_isRegularOfDegree : cycleThreeFive.IsRegularOfDegree 2 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the `2C₄` model of SE4. -/
theorem twoC4_isRegularOfDegree : twoC4.IsRegularOfDegree 2 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the `2K₄` model of SE4. -/
theorem twoK4_isRegularOfDegree : twoK4.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the cube model of SE4. -/
theorem cubeGraph_isRegularOfDegree : cubeGraph.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the Wagner model of SE4. -/
theorem wagnerGraph_isRegularOfDegree : wagnerGraph.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the `Y₁` model of SE4. -/
theorem truncatedK33Graph_isRegularOfDegree : truncatedK33Graph.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the `Y₂` model of SE4. -/
theorem twiceTruncatedK4Graph_isRegularOfDegree :
    twiceTruncatedK4Graph.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide +kernel

/-- The valency of the `Y₄` model of SE4. -/
theorem twoDiamondsGraph_isRegularOfDegree : twoDiamondsGraph.IsRegularOfDegree 3 := by
  unfold IsRegularOfDegree
  decide +kernel

end SimpleGraph
