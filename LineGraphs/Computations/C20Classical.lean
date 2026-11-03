/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.NeighborCertificates
import LineGraphs.Computations.C4Classical

/-!
# Parametric root-neighborhood counts

The neighbors of an A root share one of its signed coordinates. For D there is
also an independent sign on the other coordinate.
-/

open Computations
open scoped RealInnerProductSpace

namespace LineSystem

private theorem card_outside_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Fintype.card {k : Fin n // k ≠ i ∧ k ≠ j} = n - 2 := by
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun k : Fin n => k ≠ i ∧ k ≠ j) =
      Finset.univ \ {i, j} := by ext k; simp
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [hij]

private theorem an_neighbor_condition {m : ℕ} (i j k l : Fin m)
    (hij : i ≠ j) (hkl : k ≠ l) :
    integerInner (pairVector k l 1 (-1)) (pairVector i j 1 (-1)) = 1 ↔
      (k = i ∧ l ≠ i ∧ l ≠ j) ∨ (l = j ∧ k ≠ i ∧ k ≠ j) := by
  rw [integerInner_pairVector]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [pairVector]

/-- The two families of roots adjacent at angle 60 degrees to an A root. -/
def An.neighborLabel {n : ℕ} (a : An.Index n)
    (p : Bool × {k : Fin (n + 1) // k ≠ a.val.1 ∧ k ≠ a.val.2}) : An.Index n :=
  if p.1 then ⟨(p.2.val, a.val.2), p.2.property.2⟩
  else ⟨(a.val.1, p.2.val), p.2.property.1.symm⟩

/-- Parametric enumeration of the neighborhood of any A root. -/
noncomputable def An.neighborEquiv {n : ℕ} (a : An.Index n) :
    (Bool × {k : Fin (n + 1) // k ≠ a.val.1 ∧ k ≠ a.val.2}) ≃
      (An n).N (integerVector 1 (anRoot a)) :=
  (An.integerModel n).subsetEquiv _ (fun _ h => h.1) (An.neighborLabel a)
    (by
      rintro ⟨s, k⟩ ⟨t, l⟩ h
      have hfst := congrArg (fun p : An.Index n => p.val.1) h
      have hsnd := congrArg (fun p : An.Index n => p.val.2) h
      cases s <;> cases t
      · exact Prod.ext rfl (Subtype.ext hsnd)
      · exact False.elim (l.property.1 hfst.symm)
      · exact False.elim (k.property.1 hfst)
      · exact Prod.ext rfl (Subtype.ext hfst)) (by
      intro x
      change (_ ∧ _) ↔ _
      rw [and_iff_right ((An.integerModel n).root_mem x)]
      change ⟪integerVector (An.integerModel n).c ((An.integerModel n).v x),
        integerVector (An.integerModel n).c ((An.integerModel n).v a)⟫ = 1 ↔ _
      rw [(An.integerModel n).inner_eq_one_iff]
      change integerInner (anRoot x) (anRoot a) = 1 ↔ _
      rcases x with ⟨⟨k, l⟩, hkl⟩
      rw [anRoot, anRoot, an_neighbor_condition _ _ _ _ a.property hkl]
      constructor
      · rintro (⟨hk, hli, hlj⟩ | ⟨hl, hki, hkj⟩)
        · exact ⟨(false, ⟨l, hli, hlj⟩), Subtype.ext (Prod.ext hk.symm rfl)⟩
        · exact ⟨(true, ⟨k, hki, hkj⟩), Subtype.ext (Prod.ext rfl hl.symm)⟩
      · rintro ⟨⟨s, m⟩, hm⟩
        have hfst := congrArg (fun p : An.Index n => p.val.1) hm
        have hsnd := congrArg (fun p : An.Index n => p.val.2) hm
        cases s
        · exact Or.inl ⟨hfst.symm, hsnd ▸ m.property.1, hsnd ▸ m.property.2⟩
        · exact Or.inr ⟨hsnd.symm, hfst ▸ m.property.1, hfst ▸ m.property.2⟩)

/-- C20: the A-family formula, valid for every root in every rank. -/
theorem An.card_N {n : ℕ} {r : EuclideanSpace ℝ (Fin (n + 1))} (hr : r ∈ (An n).Φ) :
    ((An n).N r).ncard = 2 * (n - 1) := by
  obtain ⟨a, rfl⟩ := hr
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (An.neighborEquiv a), Nat.card_eq_fintype_card,
    Fintype.card_prod, card_outside_pair _ _ a.property]
  simp

-- Only the four support coincidences and four Boolean signs are split; the rank is arbitrary.
private theorem dn_neighbor_condition {n : ℕ} (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (s t u v : Bool) :
    integerInner (pairVector k l (rootSign u) (rootSign v))
      (pairVector i j (rootSign s) (rootSign t)) = 1 ↔
      (k = i ∧ u = s ∧ l ≠ i ∧ l ≠ j) ∨
      (l = i ∧ v = s ∧ k ≠ i ∧ k ≠ j) ∨
      (k = j ∧ u = t ∧ l ≠ i ∧ l ≠ j) ∨
      (l = j ∧ v = t ∧ k ≠ i ∧ k ≠ j) := by
  rw [integerInner_pairVector]
  cases s <;> cases t <;> cases u <;> cases v <;>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [pairVector, rootSign]

private noncomputable def pairIndex {n : ℕ} (i k : Fin n) (hik : i ≠ k)
    (s t : Bool) : Dn.Index n :=
  (exists_dnRoot_eq_pairVector i k hik s t).choose

private theorem dnRoot_pairIndex {n : ℕ} (i k : Fin n) (hik : i ≠ k) (s t : Bool) :
    dnRoot (pairIndex i k hik s t) = pairVector i k (rootSign s) (rootSign t) :=
  (exists_dnRoot_eq_pairVector i k hik s t).choose_spec

/-- Choose the shared support, the new coordinate, and its sign. -/
noncomputable def Dn.neighborLabel {n : ℕ} (a : Dn.Index n)
    (p : Bool × {k : Fin n // k ≠ a.1.val.1 ∧ k ≠ a.1.val.2} × Bool) : Dn.Index n :=
  if p.1 then pairIndex a.1.val.2 p.2.1 p.2.1.property.2.symm a.2.2 p.2.2
  else pairIndex a.1.val.1 p.2.1 p.2.1.property.1.symm a.2.1 p.2.2

private theorem dnRoot_neighborLabel {n : ℕ} (a : Dn.Index n)
    (p : Bool × {k : Fin n // k ≠ a.1.val.1 ∧ k ≠ a.1.val.2} × Bool) :
    dnRoot (Dn.neighborLabel a p) =
      if p.1 then pairVector a.1.val.2 p.2.1 (rootSign a.2.2) (rootSign p.2.2)
      else pairVector a.1.val.1 p.2.1 (rootSign a.2.1) (rootSign p.2.2) := by
  simp only [Dn.neighborLabel]
  split <;> rw [dnRoot_pairIndex]

private theorem pairVector_sign_injective {n : ℕ} (i k l : Fin n)
    (hki : k ≠ i) (hli : l ≠ i) (a : ℤ) (s t : Bool)
    (h : pairVector i k a (rootSign s) = pairVector i l a (rootSign t)) :
    k = l ∧ s = t := by
  have hkl : k = l := by
    by_contra he
    have hk := congrFun h k
    simp [pairVector, hki, he, rootSign_ne_zero] at hk
  subst l
  exact ⟨rfl, rootSign_injective (by simpa [pairVector, hki] using congrFun h k)⟩

private theorem dn_neighborLabel_injective {n : ℕ} (a : Dn.Index n) :
    Function.Injective (Dn.neighborLabel a) := by
  rintro ⟨s, k, u⟩ ⟨t, l, v⟩ h
  have he := congrArg dnRoot h
  rw [dnRoot_neighborLabel, dnRoot_neighborLabel] at he
  cases s <;> cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true] at he
  · obtain ⟨hk, hu⟩ := pairVector_sign_injective _ _ _ k.property.1 l.property.1 _ _ _ he
    exact Prod.ext rfl (Prod.ext (Subtype.ext hk) hu)
  · have hi := congrFun he a.1.val.1
    simp [pairVector, ne_of_lt a.1.property, k.property.1.symm, l.property.1.symm,
      rootSign_ne_zero] at hi
  · have hi := congrFun he a.1.val.1
    simp only [pairVector, Pi.add_apply, Pi.single_apply, ne_of_lt a.1.property,
      k.property.1.symm, l.property.1.symm, ↓reduceIte, add_zero] at hi
    exact False.elim (rootSign_ne_zero _ hi.symm)
  · obtain ⟨hk, hu⟩ := pairVector_sign_injective _ _ _ k.property.2 l.property.2 _ _ _ he
    exact Prod.ext rfl (Prod.ext (Subtype.ext hk) hu)

private theorem dn_neighbor_cover {n : ℕ} (a x : Dn.Index n) :
    integerInner (dnRoot x) (dnRoot a) = 1 ↔ ∃ p, Dn.neighborLabel a p = x := by
  constructor
  · rcases a with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
    rcases x with ⟨⟨⟨k, l⟩, hkl⟩, u, v⟩
    rw [dnRoot, dnRoot, dn_neighbor_condition i j k l (ne_of_lt hij) (ne_of_lt hkl)]
    rintro (⟨rfl, rfl, hli, hlj⟩ | ⟨rfl, rfl, hki, hkj⟩ |
      ⟨rfl, rfl, hli, hlj⟩ | ⟨rfl, rfl, hki, hkj⟩)
    · refine ⟨(false, ⟨l, hli, hlj⟩, v), dnRoot_injective ?_⟩
      rw [dnRoot_neighborLabel]
      rfl
    · refine ⟨(false, ⟨k, hki, hkj⟩, u), dnRoot_injective ?_⟩
      rw [dnRoot_neighborLabel]
      exact add_comm _ _
    · refine ⟨(true, ⟨l, hli, hlj⟩, v), dnRoot_injective ?_⟩
      rw [dnRoot_neighborLabel]
      rfl
    · refine ⟨(true, ⟨k, hki, hkj⟩, u), dnRoot_injective ?_⟩
      rw [dnRoot_neighborLabel]
      exact add_comm _ _
  · rintro ⟨⟨s, k, t⟩, rfl⟩
    rcases a with ⟨⟨⟨i, j⟩, hij⟩, u, v⟩
    rw [dnRoot_neighborLabel]
    cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      rw [integerInner_pairVector] <;>
      cases u <;> cases v <;> cases t <;>
      simp [dnRoot, pairVector, rootSign, k.property.1, k.property.2,
        ne_of_lt hij, ne_of_gt hij]

/-- Parametric enumeration of the neighborhood of any D root. -/
noncomputable def Dn.neighborEquiv {n : ℕ} (a : Dn.Index n) :
    (Bool × {k : Fin n // k ≠ a.1.val.1 ∧ k ≠ a.1.val.2} × Bool) ≃
      (Dn n).N (integerVector 1 (dnRoot a)) :=
  (Dn.integerModel n).subsetEquiv _ (fun _ h => h.1) (Dn.neighborLabel a)
    (dn_neighborLabel_injective a) (by
      intro x
      change (_ ∧ _) ↔ _
      rw [and_iff_right ((Dn.integerModel n).root_mem x)]
      change ⟪integerVector (Dn.integerModel n).c ((Dn.integerModel n).v x),
        integerVector (Dn.integerModel n).c ((Dn.integerModel n).v a)⟫ = 1 ↔ _
      rw [(Dn.integerModel n).inner_eq_one_iff]
      exact dn_neighbor_cover a x)

/-- C20: the D-family formula, valid for every root in every rank. -/
theorem Dn.card_N {n : ℕ} {r : EuclideanSpace ℝ (Fin n)} (hr : r ∈ (Dn n).Φ) :
    ((Dn n).N r).ncard = 4 * (n - 2) := by
  obtain ⟨a, rfl⟩ := hr
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (Dn.neighborEquiv a), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_prod, card_outside_pair _ _ (ne_of_lt a.1.property)]
  simp
  omega

end LineSystem
