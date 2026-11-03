# Generator of C4E6Stars.lean, C4E7Stars.lean, C4E8Stars.lean (templates; data from generate_c4_stars.py).
from pathlib import Path

OUT = Path(__file__).resolve().parents[1] / "Computations"

T = r'''/-
Copyright (c) 2026 Krystal Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.C4E@M@
import LineGraphs.Computations.C4StarData
import LineGraphs.Computations.StarOrbits

/-!
# C4 for every ordered star of @E@

The reflections in the roots of @E@ act transitively on its ordered stars, by two checked
reflection trees (`Computations.C4.e@M@RootParents` and `e@M@StarParents`). Hence the rows of
computation C4 proved for the fixed star `E@S@.hyp24` hold for every term `H : Hyp24` with
`H.S = @E@`: the orthogonality graph is strongly regular with parameters @SRG@,
`|Γa| = @G@` and `|Δ| = @D@`. The star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table is
`@E@.hyp24Simple`, at `Fin 8` indices 0, 1, 2.
-/

open Computations C4
open scoped RealInnerProductSpace

namespace LineSystem

/-- The tree over all roots of @E@, from the root `e₁ + e₂` (index @AI@). -/
theorem @E@.root_tree_checked : ∀ i : Fin @N@, i ≠ @A@ →
    listNat e@M@RootDepths (listFin @N@ e@M@RootParents i) < listNat e@M@RootDepths i ∧
    @E@.tableModel.q • @E@.tableModel.v i =
      @E@.tableModel.q • @E@.tableModel.v (listFin @N@ e@M@RootParents i) -
      integerInner (@E@.tableModel.v (listFin @N@ e@M@RootReflections i))
          (@E@.tableModel.v (listFin @N@ e@M@RootParents i)) •
        @E@.tableModel.v (listFin @N@ e@M@RootReflections i) := by
  decide +kernel

/-- The tree over the roots at product `-1` with `e₁ + e₂`, from `-e₁ + e₃` (index @BI@); each
reflecting root is orthogonal to `e₁ + e₂`. -/
theorem @E@.star_tree_checked : ∀ i : Fin @N@,
    integerInner (@E@.tableModel.v i) (@E@.tableModel.v @A@) = -@E@.tableModel.q →
    i ≠ @B@ →
    integerInner (@E@.tableModel.v (listFin @N@ e@M@StarParents i)) (@E@.tableModel.v @A@) =
      -@E@.tableModel.q ∧
    listNat e@M@StarDepths (listFin @N@ e@M@StarParents i) < listNat e@M@StarDepths i ∧
    integerInner (@E@.tableModel.v (listFin @N@ e@M@StarReflections i))
      (@E@.tableModel.v @A@) = 0 ∧
    @E@.tableModel.q • @E@.tableModel.v i =
      @E@.tableModel.q • @E@.tableModel.v (listFin @N@ e@M@StarParents i) -
      integerInner (@E@.tableModel.v (listFin @N@ e@M@StarReflections i))
          (@E@.tableModel.v (listFin @N@ e@M@StarParents i)) •
        @E@.tableModel.v (listFin @N@ e@M@StarReflections i) := by
  decide +kernel

-- Computation C4
/-- C4: the isometries preserving @E@ act transitively on its ordered stars. -/
theorem @E@.exists_isometry_star {a b : EuclideanSpace ℝ (Fin 8)} (ha : a ∈ @E@.Φ)
    (hb : b ∈ @E@.Φ) (hab : ⟪a, b⟫ = -1) :
    ∃ g ∈ @E@.isometryGroup, g @E@.hyp24.a = a ∧ g @E@.hyp24.b = b :=
  @E@.tableModel.exists_isometry_of_star @A@ @B@
    (fun i => by
      obtain ⟨g, hg, -, h⟩ := @E@.tableModel.exists_isometry_of_tree isStarClosed_@E@ 0
        (fun _ => True) @A@ (listFin @N@ e@M@RootParents) (listFin @N@ e@M@RootReflections)
        (listNat e@M@RootDepths)
        (fun i _ hi => ⟨trivial, (@E@.root_tree_checked i hi).1, inner_zero_right _,
          (@E@.root_tree_checked i hi).2⟩) i trivial
      exact ⟨g, hg, h⟩)
    (fun j hj => @E@.tableModel.exists_isometry_of_tree isStarClosed_@E@ _
      (fun i => integerInner (@E@.tableModel.v i) (@E@.tableModel.v @A@) =
        -@E@.tableModel.q) @B@
      (listFin @N@ e@M@StarParents) (listFin @N@ e@M@StarReflections) (listNat e@M@StarDepths)
      (fun i hi hne => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := @E@.star_tree_checked i hi hne
        exact ⟨h₁, h₂, (@E@.tableModel.inner_eq_zero_iff _ _).mpr h₃, h₄⟩) j hj)
    ha hb hab

namespace Hyp24

variable (H : Hyp24 (EuclideanSpace ℝ (Fin 8)))

/-- C4 for every ordered star of @E@: an isometry preserving `Φ` carries the fixed star
`@E@.hyp24` to the star of `H`. -/
theorem exists_isometry_of_S_eq_@E@ (hS : H.S = @E@) :
    ∃ g : EuclideanSpace ℝ (Fin 8) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8),
      (∀ x, g x ∈ H.S.Φ ↔ x ∈ @E@.hyp24.S.Φ) ∧ g @E@.hyp24.a = H.a ∧ g @E@.hyp24.b = H.b :=
  exists_isometry_of_S_eq @E@.hyp24 H rfl hS (fun _ _ => @E@.exists_isometry_star)

-- Computation C4
/-- C4 for every ordered star of @E@: its orthogonality graph is that of `@E@.hyp24`. -/
theorem nonempty_orthGraph_iso_of_S_eq_@E@ (hS : H.S = @E@) :
    Nonempty (@E@.hyp24.orthGraph ≃g H.orthGraph) := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_@E@ hS
  exact ⟨orthGraphIsoOfIsometry _ _ g hΦ ha hb⟩

-- Computation C4
/-- C4 for every ordered star of @E@: the orthogonality graph is strongly regular with
parameters @SRG@. -/
theorem orthGraph_isSRGWith_of_S_eq_@E@ (hS : H.S = @E@) :
    H.orthGraph.IsSRGWith @SRGS@ := by
  obtain ⟨e⟩ := H.nonempty_orthGraph_iso_of_S_eq_@E@ hS
  exact e.isSRGWith @E@.orthGraph_isSRGWith

-- Computation C4
/-- C4 for every ordered star of @E@: `|Γa| = @G@`. -/
theorem card_Γa_of_S_eq_@E@ (hS : H.S = @E@) : H.Γa.ncard = @G@ := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_@E@ hS
  rw [ncard_Γa_eq_of_isometry _ _ g hΦ ha hb, @E@.card_Γa]

-- Computation C4
/-- C4 for every ordered star of @E@: `|Δ| = @D@`, that is, @DL@ lines. -/
theorem card_Δ_of_S_eq_@E@ (hS : H.S = @E@) : H.Δ.ncard = @D@ := by
  obtain ⟨g, hΦ, ha, hb⟩ := H.exists_isometry_of_S_eq_@E@ hS
  rw [ncard_Δ_eq_of_isometry _ _ g hΦ ha hb, @E@.card_Δ]

end Hyp24

/-- The ordered star `(e₁ - e₂, e₂ - e₃)` of the blueprint's C4 table: in `Fin 8`,
`a = e₀ - e₁` and `b = e₁ - e₂` (indices @SA@ and @SB@ of the root table). -/
noncomputable def @E@.hyp24Simple : Hyp24 (EuclideanSpace ℝ (Fin 8)) :=
  @E@.tableModel.hyp24 isIndecomposable_@E@ isStarClosed_@E@
    (@SA@ : Fin @N@) (@SB@ : Fin @N@) (by decide +kernel)

theorem @E@.hyp24Simple_a : @E@.hyp24Simple.a =
    EuclideanSpace.single 0 (1 : ℝ) - EuclideanSpace.single 1 1 := by
  change integerVector (1 / 2) (@E@.tableModel.v (@SA@ : Fin @N@)) = _
  have hv : @E@.tableModel.v (@SA@ : Fin @N@) = ![2, -2, 0, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

theorem @E@.hyp24Simple_b : @E@.hyp24Simple.b =
    EuclideanSpace.single 1 (1 : ℝ) - EuclideanSpace.single 2 1 := by
  change integerVector (1 / 2) (@E@.tableModel.v (@SB@ : Fin @N@)) = _
  have hv : @E@.tableModel.v (@SB@ : Fin @N@) = ![0, 2, -2, 0, 0, 0, 0, 0] := by
    decide +kernel
  rw [hv]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply, Fin.ext_iff]

end LineSystem
'''
sub={"6":"₆","7":"₇","8":"₈"}
data={"8":(240,239,12,226,150,"(27, 10, 1, 5)","27 10 1 5",27,72,36),
      "7":(126,125,8,116,76,"(15, 6, 1, 3)","15 6 1 3",15,30,15),
      "6":(72,71,6,64,42,"(9, 4, 1, 2)","9 4 1 2",9,12,6)}
for m,(N,A,B,SA,SB,SRG,SRGS,G,D,DL) in data.items():
    s=T
    for k,v in [("@E@","E"+sub[m]),("@S@",sub[m]),("@M@",m),("@N@",N),("@AI@",A),("@BI@",B),("@A@",f"({A} : Fin {N})"),("@B@",f"({B} : Fin {N})"),("@SA@",SA),("@SB@",SB),
                ("@SRGS@",SRGS),("@SRG@",SRG),("@G@",G),("@DL@",DL),("@D@",D)]:
        s=s.replace(k,str(v))
    (OUT / f"C4E{m}Stars.lean").write_text(s)
