/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Cartan.DObstructions

/-!
# Unweighted Dynkin trees

Excluding affine D and E subgraphs from a tree leaves precisely paths and the
finite D and E arm lengths (`lem:unweighted-trees` of the Remark 3.11 blueprint).
-/

namespace SimpleGraph

/-- Truncating each arm gives an induced embedding of three-arm trees. -/
def armTreeEmbedding {a b : Fin 3 → ℕ} (hab : ∀ r, a r ≤ b r) :
    armTree a ↪g armTree b where
  toEmbedding := Function.Embedding.optionMap
    (Function.Embedding.sigmaMap (Function.Embedding.refl _) (fun r => Fin.castLEEmb (hab r)))
  map_rel_iff' := by
    rintro (_ | ⟨r, i⟩) (_ | ⟨s, j⟩) <;> rfl

variable {V : Type*} [Fintype V] {X : SimpleGraph V}

/-- A finite connected acyclic graph with no affine D or E subgraph has a Dynkin
path or arm labelling. Obstruction subgraphs need not be induced. -/
theorem dynkin_labelling_of_no_affine (hconn : X.Connected) (hacyc : X.IsAcyclic)
    (hD : ∀ ℓ, 4 ≤ ℓ → ¬ Nonempty (Copy (smithD ℓ) X))
    (hE₆ : ¬ Nonempty (Copy smithE₆ X)) (hE₇ : ¬ Nonempty (Copy smithE₇ X))
    (hE₈ : ¬ Nonempty (Copy smithE₈ X)) :
    Nonempty (pathGraph (Fintype.card V) ≃g X) ∨
      (∃ c, 0 < c ∧ Nonempty (armTree ![1, 1, c] ≃g X)) ∨
      Nonempty (armTree ![1, 2, 2] ≃g X) ∨
      Nonempty (armTree ![1, 2, 3] ≃g X) ∨
      Nonempty (armTree ![1, 2, 4] ≃g X) := by
  classical
  have htree : X.IsTree := ⟨hconn, hacyc⟩
  have hdegree (v : V) : X.degree v ≤ 3 := by
    by_contra hv
    exact hD 4 (by omega) (smithD_four_copy_of_degree_ge_four v (by omega))
  have hbranch (u v : V) (hu : X.degree u = 3) (hv : X.degree v = 3) : u = v := by
    by_contra hne
    obtain ⟨ℓ, hℓ, he⟩ := htree.exists_smithD_copy_of_two_branches hne hu.ge hv.ge
    exact hD ℓ (by omega) he
  by_cases hbranchExists : ∃ v, X.degree v = 3
  · obtain ⟨v, hv⟩ := hbranchExists
    have hother (w : V) (hw : w ≠ v) : X.degree w ≤ 2 := by
      have hle := hdegree w
      have hne : X.degree w ≠ 3 := fun h => hw (hbranch w v h hv)
      omega
    obtain ⟨a, hpos, hmono, e, _⟩ := exists_three_arm_labelling hconn hacyc v hv hother
    have h01 : a 0 ≤ a 1 := hmono (by decide)
    have h12 : a 1 ≤ a 2 := hmono (by decide)
    have h0pos := hpos 0
    have h1pos := hpos 1
    have h2pos := hpos 2
    have hfirst : a 0 = 1 := by
      by_contra hfirst
      have hle : ∀ r, (![2, 2, 2] : Fin 3 → ℕ) r ≤ a r := by
        intro r
        fin_cases r
        · change 2 ≤ a 0; omega
        · change 2 ≤ a 1; omega
        · change 2 ≤ a 2; omega
      exact hE₆ ⟨e.toCopy.comp (armTreeEmbedding hle).toCopy⟩
    have hsecond : a 1 ≤ 2 := by
      by_contra hsecond
      have hle : ∀ r, (![1, 3, 3] : Fin 3 → ℕ) r ≤ a r := by
        intro r
        fin_cases r
        · change 1 ≤ a 0; omega
        · change 3 ≤ a 1; omega
        · change 3 ≤ a 2; omega
      exact hE₇ ⟨e.toCopy.comp (armTreeEmbedding hle).toCopy⟩
    right
    rcases (show a 1 = 1 ∨ a 1 = 2 by omega) with hsecond | hsecond
    · left
      have heq : a = ![1, 1, a 2] := by
        ext i
        fin_cases i <;> simp_all
      exact ⟨a 2, h2pos, heq ▸ ⟨e⟩⟩
    · have hthird : a 2 ≤ 4 := by
        by_contra hthird
        have hle : ∀ r, (![1, 2, 5] : Fin 3 → ℕ) r ≤ a r := by
          intro r
          fin_cases r
          · change 1 ≤ a 0; omega
          · change 2 ≤ a 1; omega
          · change 5 ≤ a 2; omega
        exact hE₈ ⟨e.toCopy.comp (armTreeEmbedding hle).toCopy⟩
      right
      rcases (show a 2 = 2 ∨ a 2 = 3 ∨ a 2 = 4 by omega) with hthird | hthird | hthird
      · left
        have heq : a = ![1, 2, 2] := by ext i; fin_cases i <;> simp_all
        exact heq ▸ ⟨e⟩
      · right; left
        have heq : a = ![1, 2, 3] := by ext i; fin_cases i <;> simp_all
        exact heq ▸ ⟨e⟩
      · right; right
        have heq : a = ![1, 2, 4] := by ext i; fin_cases i <;> simp_all
        exact heq ▸ ⟨e⟩
  · left
    apply nonempty_iso_pathGraph hconn hacyc
    intro v
    have hle := hdegree v
    have hne : X.degree v ≠ 3 := fun h => hbranchExists ⟨v, h⟩
    omega

end SimpleGraph
