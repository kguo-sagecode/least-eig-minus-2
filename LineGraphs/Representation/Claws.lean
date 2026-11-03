/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Representation.GeneralizedLineGraph
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Claws and induced stars

Definition `def:claw` and Lemma `lem:4-clawstar` preceding Remark 4.12 of [CGSS].
-/

namespace SimpleGraph

variable {V W : Type*}

-- Definition (claws)
/-- Definition `def:claw`, Remark 4.12 of [CGSS]: a set of `k` pairwise
nonadjacent neighbours of a centre. -/
structure IsClawOfSize (X : SimpleGraph V) (k : ℕ) (u : V) (T : Finset V) : Prop where
  card : T.card = k
  adj : ∀ v ∈ T, X.Adj u v
  not_adj : ∀ v ∈ T, ∀ w ∈ T, ¬X.Adj v w

-- Definition (claws)
/-- Definition `def:claw`, Remark 4.12 of [CGSS]: a three-claw with centre `u`. -/
abbrev IsClaw (X : SimpleGraph V) (u : V) (T : Finset V) : Prop :=
  X.IsClawOfSize 3 u T

-- Definition (claws)
/-- Definition `def:claw`, Remark 4.12 of [CGSS]: a four-claw with centre `u`. -/
abbrev IsFourClaw (X : SimpleGraph V) (u : V) (T : Finset V) : Prop :=
  X.IsClawOfSize 4 u T

-- Definition (claws)
/-- Definition `def:claw`, Remark 4.12 of [CGSS]: no induced star on four vertices. -/
def ClawFree (X : SimpleGraph V) : Prop :=
  ¬(starGraph (0 : Fin 4)).IsIndContained X

-- Definition (claws)
/-- Definition `def:claw`, Remark 4.12 of [CGSS]: no induced star on five vertices. -/
def FourClawFree (X : SimpleGraph V) : Prop :=
  ¬(starGraph (0 : Fin 5)).IsIndContained X

-- Lemma (claws and stars)
/-- Lemma `lem:4-clawstar`, steps `s4csfwd` and `s4csbwd`, Remark 4.12 of [CGSS]:
an induced star is exactly a finite claw, for any number of leaves. -/
theorem starGraph_isIndContained_iff {X : SimpleGraph V} (k : ℕ) :
    (starGraph (0 : Fin (k + 1))).IsIndContained X ↔
      ∃ u T, X.IsClawOfSize k u T := by
  classical
  constructor
  · rintro ⟨f⟩
    let g : Fin k → V := fun i ↦ f i.succ
    have hg : Function.Injective g := f.injective.comp (Fin.succ_injective k)
    refine ⟨f 0, Finset.univ.image g, ?_, ?_, ?_⟩
    · simp [Finset.card_image_of_injective _ hg]
    · intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact f.map_rel_iff.mpr (starGraph_adj.mpr
        ⟨(Fin.succ_ne_zero i).symm, Or.inl rfl⟩)
    · intro v hv w hw hvw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      have h := f.map_rel_iff.mp hvw
      simp [starGraph_adj] at h
  · rintro ⟨u, T, hT⟩
    let e : T ≃ Fin k := T.equivFinOfCardEq hT.card
    let g : Fin k → V := fun i ↦ (e.symm i).val
    have hg : Function.Injective g := Subtype.val_injective.comp e.symm.injective
    have ha (i : Fin k) : X.Adj u (g i) := hT.adj _ (e.symm i).property
    have hn (i j : Fin k) : ¬X.Adj (g i) (g j) :=
      hT.not_adj _ (e.symm i).property _ (e.symm j).property
    let f : Fin (k + 1) → V := Fin.cases u g
    refine ⟨{ toFun := f, inj' := ?_, map_rel_iff' := ?_ }⟩
    · intro i j
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact fun _ ↦ rfl
      · exact fun h ↦ ((ha _).ne h).elim
      · exact fun h ↦ ((ha _).ne h.symm).elim
      · exact fun h ↦ congrArg Fin.succ (hg h)
    · intro i j
      change X.Adj (f i) (f j) ↔ _
      induction i using Fin.cases <;> induction j using Fin.cases <;>
        simp [f, starGraph_adj, ha, adj_comm, hn]

-- Lemma (claws and stars)
/-- Lemma `lem:4-clawstar`, assertion 1 for three leaves, Remark 4.12 of [CGSS]. -/
theorem clawFree_iff_forall_not_isClaw (X : SimpleGraph V) :
    X.ClawFree ↔ ∀ u T, ¬X.IsClaw u T := by
  simp only [ClawFree, starGraph_isIndContained_iff, not_exists, IsClaw]

-- Lemma (claws and stars)
/-- Lemma `lem:4-clawstar`, assertion 1 for four leaves, Remark 4.12 of [CGSS]. -/
theorem fourClawFree_iff_forall_not_isFourClaw (X : SimpleGraph V) :
    X.FourClawFree ↔ ∀ u T, ¬X.IsFourClaw u T := by
  simp only [FourClawFree, starGraph_isIndContained_iff, not_exists, IsFourClaw]

-- Lemma (claws and stars)
/-- Lemma `lem:4-clawstar`, step `s4csiso`, Remark 4.12 of [CGSS]:
claw-freeness is preserved by graph isomorphisms. -/
theorem Iso.clawFree_iff {X : SimpleGraph V} {Y : SimpleGraph W} (e : X ≃g Y) :
    X.ClawFree ↔ Y.ClawFree :=
  ⟨fun h h' ↦ h (h'.trans e.isIndContained'),
    fun h h' ↦ h (h'.trans e.isIndContained)⟩

-- Lemma (claws and stars)
/-- Lemma `lem:4-clawstar`, step `s4csiso`, Remark 4.12 of [CGSS]:
four-claw-freeness is preserved by graph isomorphisms. -/
theorem Iso.fourClawFree_iff {X : SimpleGraph V} {Y : SimpleGraph W} (e : X ≃g Y) :
    X.FourClawFree ↔ Y.FourClawFree :=
  ⟨fun h h' ↦ h (h'.trans e.isIndContained'),
    fun h h' ↦ h (h'.trans e.isIndContained)⟩

-- Definition (claws)
/-- Definition `def:claw`, Remark 4.12 of [CGSS]: a larger claw contains a
smaller one with the same centre. -/
theorem IsClawOfSize.exists_subset {X : SimpleGraph V} {k l : ℕ} {u : V} {T : Finset V}
    (h : X.IsClawOfSize k u T) (hl : l ≤ k) : ∃ S ⊆ T, X.IsClawOfSize l u S := by
  obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq (h.card ▸ hl)
  exact ⟨S, hST, hS, fun v hv ↦ h.adj v (hST hv),
    fun v hv w hw ↦ h.not_adj v (hST hv) w (hST hw)⟩

end SimpleGraph
