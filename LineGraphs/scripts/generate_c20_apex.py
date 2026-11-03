# Generator of Computations/C20Apex.lean (LN6 form of C20); edge order of the Sage pairs in C20Data.lean.
from pathlib import Path

OUT = Path(__file__).resolve().parents[1] / "Computations"

HEAD = r'''/-
Copyright (c) 2026 Krystal Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C20

/-!
# C20 in the form of LN6: the pairs of `N_c`

LN6 of `cgss/prerequisites.md` takes model (ii) of E₈, with `E₇ = E₈ ∩ (e₇ - e₈)^⊥` and
`E₆ = E₇ ∩ (e₆ - e₇)^⊥` (1-based, as in `LineSystem.E₇`, `LineSystem.E₆`), and the root
`c = ½ ∑ᵢ eᵢ`, which lies in all three. The root used is `c` (not `e₇ - e₈`): it is the apex
`neighborApex` of the Sage pairs of `C20E6.lean`, `C20E7.lean` and `C20E8.lean` (table roots
63, 115 and 225, the vector `(1, …, 1)` in doubled coordinates), by `neighborApex_eq_c`. Then
`N_c` consists of the pairs `{eᵢ + eⱼ, c - eᵢ - eⱼ}`, where `{i, j}` runs over the edges of

* `K₈` for E₈ (28 pairs, 56 roots),
* `K₆` together with `{7, 8}` for E₇ (16 pairs, 32 roots),
* `K₅` for E₆ (10 pairs, 20 roots).

In `Fin 8` these are the pairs `i < j` with no condition, with `j < 6` or `(i, j) = (6, 7)`, and
with `j < 5`. The two roots of a pair are exchanged by `pairInv c`.

## Main statements

* `E₈.c`, `E₈.c_mem`, `E₇.c_mem`, `E₆.c_mem`, and `neighborApex_eq_c` for each model.
* `E₈.cPairs`, `E₇.cPairs`, `E₆.cPairs`: the edges, with a sign, enumerate `N_c`;
  `cPairs_false`, `cPairs_true` give the two roots; `pairInv_cPairs` exchanges them.
* `E₈.N_c`, `E₇.N_c`, `E₆.N_c`: `N_c` as an explicit set; `card_N_c`: 56, 32 and 20.
-/

open Computations
open scoped RealInnerProductSpace

namespace LineSystem

/-- LN6: the root `c = ½ ∑ᵢ eᵢ` of model (ii) of E₈; it also lies in E₇ and E₆. -/
noncomputable def E₈.c : EuclideanSpace ℝ (Fin 8) :=
  (1 / 2 : ℝ) • ∑ i, EuclideanSpace.single i 1

theorem E₈.c_eq_integerVector : E₈.c = integerVector (1 / 2) (fun _ => 1) := by
  ext k
  simp [E₈.c]

/-- The doubled coordinates of `eᵢ + eⱼ`. -/
theorem integerVector_half_pairVector (i j : Fin 8) (hij : i ≠ j) :
    integerVector (1 / 2) (pairVector i j 2 2) =
      EuclideanSpace.single i (1 : ℝ) + EuclideanSpace.single j 1 := by
  ext k
  simp only [integerVector_apply, pairVector, Pi.add_apply, Pi.single_apply, PiLp.add_apply,
    PiLp.single_apply]
  split_ifs <;> simp_all
'''

T = r'''
/-! ### @E@ -/

/-- LN6: `neighborApex` of C20 for @E@ is `c = ½ ∑ᵢ eᵢ`. -/
theorem @E@.neighborApex_eq_c : @E@.neighborApex = E₈.c := by
  change integerVector (1 / 2) (@E@.tableModel.v (@A@ : Fin @N@)) = _
  rw [E₈.c_eq_integerVector]
  congr 1
  decide +kernel

/-- LN6: `c ∈ @E@`. -/
theorem @E@.c_mem : E₈.c ∈ @E@.Φ :=
  @E@.neighborApex_eq_c ▸ @E@.tableModel.root_mem (@A@ : Fin @N@)

/-- The pairs `i < j` of `Fin 8` indexing N_c in @E@: the edges of @K@. -/
abbrev @E@.CEdge := {p : Fin 8 × Fin 8 // @PRED@}

/-- The position in `C20.@M@Pairs` of an edge, in lexicographic order. -/
def @E@.edgeLabel (p : @E@.CEdge) : Fin @P@ :=
  ⟨[@TABLE@][8 * p.1.1.val + p.1.2.val]?.getD 0 % @P@,
    Nat.mod_lt _ (by decide)⟩

/-- The edge labels are a bijection. -/
noncomputable def @E@.edgeEquiv : @E@.CEdge ≃ Fin @P@ :=
  Equiv.ofBijective @E@.edgeLabel (by decide +kernel)

theorem @E@.card_CEdge : Fintype.card @E@.CEdge = @P@ := by
  rw [Fintype.card_congr @E@.edgeEquiv, Fintype.card_fin]

-- LN6 / computation C20
/-- LN6: the edges of @K@, with a sign, enumerate `N_c` in @E@; see `cPairs_false` and
`cPairs_true` for the two roots of each pair. -/
noncomputable def @E@.cPairs : @E@.CEdge × Bool ≃ @E@.N E₈.c :=
  ((@E@.edgeEquiv.prodCongr (Equiv.refl Bool)).trans @E@.neighborPairs).trans
    (Set.equivOfEq (by rw [@E@.neighborApex_eq_c]))

theorem @E@.coe_cPairs (p : @E@.CEdge) (s : Bool) :
    (@E@.cPairs (p, s) : EuclideanSpace ℝ (Fin 8)) = @E@.neighborPairs (@E@.edgeLabel p, s) :=
  rfl

-- LN6 / computation C20
/-- LN6: the first root of the pair at the edge `{i, j}` is `eᵢ + eⱼ`. -/
theorem @E@.cPairs_false (p : @E@.CEdge) :
    (@E@.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) =
      EuclideanSpace.single p.1.1 (1 : ℝ) + EuclideanSpace.single p.1.2 1 := by
  rw [@E@.coe_cPairs, ← integerVector_half_pairVector _ _ (@LT@).ne]
  change integerVector (1 / 2) (@E@.tableModel.v (@E@.neighborPairLabel (@E@.edgeLabel p, false)))
    = _
  congr 1
  exact (by decide +kernel : ∀ p : @E@.CEdge,
    @E@.tableModel.v (@E@.neighborPairLabel (@E@.edgeLabel p, false)) =
      pairVector p.1.1 p.1.2 2 2) p

-- LN6 / computation C20
/-- LN6: the second root of the pair at the edge `{i, j}` is `c - eᵢ - eⱼ`. -/
theorem @E@.cPairs_true (p : @E@.CEdge) :
    (@E@.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) =
      E₈.c - EuclideanSpace.single p.1.1 (1 : ℝ) - EuclideanSpace.single p.1.2 1 := by
  have h := @E@.neighborPairs_add (@E@.edgeLabel p)
  rw [← @E@.coe_cPairs, ← @E@.coe_cPairs, @E@.cPairs_false, @E@.neighborApex_eq_c] at h
  generalize (@E@.cPairs (p, true) : EuclideanSpace ℝ (Fin 8)) = y at h ⊢
  rw [← h]
  abel

-- LN6 / computation C20
/-- LN6: the involution `x ↦ c - x` of `N_c` exchanges the two roots of each pair. -/
theorem @E@.pairInv_cPairs (p : @E@.CEdge) :
    @E@.pairInv E₈.c isStarClosed_@E@ @E@.c_mem (@E@.cPairs (p, false)) = @E@.cPairs (p, true) := by
  apply Subtype.ext
  change E₈.c - (@E@.cPairs (p, false) : EuclideanSpace ℝ (Fin 8)) = _
  rw [@E@.cPairs_false, @E@.cPairs_true]
  abel

-- LN6 / computation C20
/-- LN6: `N_c` in @E@ is `{eᵢ + eⱼ, c - eᵢ - eⱼ}` over the edges `{i, j}` of @K@. -/
theorem @E@.N_c : @E@.N E₈.c = {x | ∃ p : Fin 8 × Fin 8,
    (@PRED@) ∧
      (x = EuclideanSpace.single p.1 1 + EuclideanSpace.single p.2 1 ∨
        x = E₈.c - EuclideanSpace.single p.1 1 - EuclideanSpace.single p.2 1)} := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨p, s⟩, hp⟩ := @E@.cPairs.surjective ⟨x, hx⟩
    have hx' : x = @E@.cPairs (p, s) := (congrArg Subtype.val hp).symm
    refine ⟨p.1, p.2, ?_⟩
    cases s
    · exact Or.inl (hx'.trans (@E@.cPairs_false p))
    · exact Or.inr (hx'.trans (@E@.cPairs_true p))
  · rintro ⟨p, hp, h | h⟩ <;> subst h
    · rw [← @E@.cPairs_false ⟨p, hp⟩]
      exact Subtype.mem _
    · rw [← @E@.cPairs_true ⟨p, hp⟩]
      exact Subtype.mem _

/-- C20 at `c`: `|N_c| = @NC@` in @E@, that is, @P@ pairs. -/
theorem @E@.card_N_c : (@E@.N E₈.c).ncard = @NC@ := @E@.card_N @E@.c_mem
'''
sub={"6":"₆","7":"₇","8":"₈"}
def table(pairs):
    t=[0]*64
    for k,(i,j) in enumerate(pairs): t[8*i+j]=k
    s=", ".join(map(str,t))
    # wrap
    out=[];line=""
    for tok in s.split(", "):
        if len(line)+len(tok)+2>80: out.append(line); line=""
        line+=tok+", "
    out.append(line.rstrip(", "))
    return ("\n    ").join(x.rstrip() for x in out)
import itertools
models={
 "8":(240,225,28,56,"K₈","p.1 < p.2",[(i,j) for i in range(8) for j in range(i+1,8)]),
 "7":(126,115,16,32,"K₆ and {7, 8}","p.1 < p.2 ∧ (p.2.val < 6 ∨ (p.1.val = 6 ∧ p.2.val = 7))",[(i,j) for i in range(6) for j in range(i+1,6)]+[(6,7)]),
 "6":(72,63,10,20,"K₅","p.1 < p.2 ∧ p.2.val < 5",[(i,j) for i in range(5) for j in range(i+1,5)]),
}
out=HEAD
for m in ["8","7","6"]:
    N,A,P,NC,K,PRED,pairs=models[m]
    s=T
    for k,v in [("@E@","E"+sub[m]),("@M@","e"+m),("@N@",N),("@A@",A),("@P@",P),("@NC@",NC),("@K@",K),("@PRED@",PRED),("@TABLE@",table(pairs)),("@LT@","p.2" if m=="8" else "p.2.1")]:
        s=s.replace(k,str(v))
    out+=s
out+="\nend LineSystem\n"
(OUT / "C20Apex.lean").write_text(out)
