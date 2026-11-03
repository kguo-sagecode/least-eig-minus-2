/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineGraphSpectra.DesignGraphs
import LineGraphs.Seidel.CocktailParty

/-!
# Graph recognition for flag spectra

The auxiliary lemmas `lem:isolated` and `lem:dense` of Theorem 5.8 of [CGSS].
-/

namespace SimpleGraph


attribute [local instance] Classical.propDecidable

/-- Lemma `lem:isolated`, step `s558Yp`, Theorem 5.8 of [CGSS]: deleting isolated
vertices preserves the line graph and supplies the no-isolates hypothesis of Lemma 5.6. -/
theorem exists_forall_degree_pos_nonempty_iso_lineGraph {W : Type*} [Fintype W]
    (Y : SimpleGraph W) :
    ∃ Y' : SimpleGraph Y.support, (∀ w, 0 < Y'.degree w) ∧
      Nonempty (Y'.lineGraph ≃g Y.lineGraph) := by
  let Z := Y.induce Y.support
  have hno (w : Y.support) : 0 < Z.degree w := by
    obtain ⟨u, hwu⟩ := w.property
    exact (Z.degree_pos_iff_exists_adj w).mpr ⟨⟨u, ⟨w, hwu.symm⟩⟩, hwu⟩
  let f := (Copy.induce Y Y.support).toLineGraphEmbedding
  have hs : Function.Surjective f := by
    rintro ⟨⟨i, j⟩, hij⟩
    let i' : Y.support := ⟨i, ⟨j, hij⟩⟩
    let j' : Y.support := ⟨j, ⟨i, hij.symm⟩⟩
    exact ⟨⟨s(i', j'), hij⟩, rfl⟩
  exact ⟨Z, hno, ⟨{ toEquiv := Equiv.ofBijective f ⟨f.injective, hs⟩
                    map_rel_iff' := f.map_rel_iff }⟩⟩

/-- Step `s558CPX2`, Theorem 5.8 of [CGSS]: the cocktail party degree. -/
theorem cocktailParty_isRegularOfDegree (m : ℕ) :
    (cocktailParty m).IsRegularOfDegree (2 * m - 2) := by
  rintro ⟨i, a⟩
  have hn : (cocktailParty m).neighborFinset (i, a) =
      (Finset.univ.erase i) ×ˢ (Finset.univ : Finset Bool) := by
    ext ⟨j, b⟩
    rw [(cocktailParty m).mem_neighborFinset]
    simp [cocktailParty, ne_comm]
  rw [← card_neighborFinset_eq_degree, hn]
  rw [Finset.card_product (Finset.univ.erase i) (Finset.univ : Finset Bool)]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, Fintype.card_bool]
  have := i.isLt
  omega

/-- Lemma `lem:dense`, step `s558CPX1`, Theorem 5.8 of [CGSS]: cocktail party recognition. -/
theorem nonempty_iso_cocktailParty {W : Type*} [Fintype W] (Y : SimpleGraph W)
    [DecidableRel Y.Adj] {m : ℕ} (hm : 1 ≤ m) (hn : Fintype.card W = 2 * m)
    (hr : Y.IsRegularOfDegree (2 * m - 2)) : Nonempty (Y ≃g cocktailParty m) :=
  hr.nonempty_iso_cocktailParty hm hn

end SimpleGraph
