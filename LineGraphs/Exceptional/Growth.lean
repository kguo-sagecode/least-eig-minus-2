/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Exceptional.Admissible
import LineGraphs.Exceptional.GrowthStructure

/-! # Completeness and irredundancy of the abstract growth

Theorem `thm:growth` (Theorem 3.6) of [Exc]. The canonical form and the choice of
certificates remain arbitrary parameters satisfying their specifications.
-/

namespace SimpleGraph

-- Lemma 3.5 / Theorem 3.6 [Exc]
/-- The children preceding `thm:growth` (Theorem 3.6) of [Exc] are exactly the
nonempty-neighbour extensions represented in `E₈`, by `lem:admissible` (Lemma 3.5). -/
theorem mem_growthChildren_iff (c : CertificateChoice) {n : ℕ}
    {X : SimpleGraph (Fin n)} (hX : X ∈ levels n) (Y : SimpleGraph (Fin (n + 1))) :
    Y ∈ growthChildren c X ↔ ∃ N : Set (Fin n), N.Nonempty ∧
      (X.adjoinVertex N).IsRepresentedIn LineSystem.E₈ ∧
        Y = (X.adjoinVertex N).comap (finSuccEquiv n) := by
  classical
  have hp := hX.2.posSemidef_two_add_adjMatrix_and_rank_le_eight
  have hB := c.valid X hp.1
  have hr : (c.indices X).card ≤ 8 := by
    rw [hB.card_eq_rank X.integralGramMatrix_isSymm, X.integralGramMatrix_cast]
    exact hp.2
  constructor
  · rintro ⟨s, hne, hs, rfl⟩
    exact ⟨_, hs.neighbors_nonempty (hB.det_pos X.integralGramMatrix_isSymm).ne' hne,
      isRepresentedIn_adjoinVertex_admissibleNeighbors hX.1 hB hr hs hne, rfl⟩
  · rintro ⟨N, hN, hY, rfl⟩
    obtain ⟨s, hne, hs, he⟩ :=
      (isRepresentedIn_adjoinVertex_iff_exists_admissible hX.1 hB hr hN).mp hY
    exact ⟨s, hne, hs, by rw [he]⟩

-- Lemma 3.5 / Theorem 3.6 [Exc]
/-- The children do not depend on the choice of certificate, as stated after
`lem:admissible` (Lemma 3.5) and used in `thm:growth` (Theorem 3.6) of [Exc]. -/
theorem growthChildren_eq (c d : CertificateChoice) {n : ℕ} {X : SimpleGraph (Fin n)}
    (hX : X ∈ levels n) : growthChildren c X = growthChildren d X := by
  ext Y
  rw [mem_growthChildren_iff c hX, mem_growthChildren_iff d hX]

-- Theorem 3.6 [Exc]
/-- The simultaneous soundness and completeness induction in `thm:growth`
(Theorem 3.6) of [Exc], indexed from the singleton level. -/
theorem growth_sound_and_complete_succ (c : CertificateChoice) (q : CanonicalForm) (n : ℕ) :
    growth c q (n + 1) ⊆ levels (n + 1) ∧
      ∀ Z ∈ levels (n + 1), ∃ X ∈ growth c q (n + 1), Nonempty (X ≃g Z) := by
  classical
  induction n with
  | zero =>
    constructor
    · intro X hX
      have he : X = ⊥ := hX
      subst X
      exact bot_mem_levels_one
    · intro Z _
      have : Subsingleton (SimpleGraph (Fin 1)) := SimpleGraph.subsingleton_iff.mpr inferInstance
      obtain rfl : Z = ⊥ := Subsingleton.elim _ _
      exact ⟨⊥, rfl, ⟨Iso.refl⟩⟩
  | succ n ih =>
    constructor
    · rintro Y ⟨X, hX, Z, hZ, rfl⟩
      have hXL := ih.1 hX
      obtain ⟨N, hN, hR, rfl⟩ := (mem_growthChildren_iff c hXL Z).mp hZ
      let f := Iso.comap (finSuccEquiv (n + 1)) (X.adjoinVertex N)
      have hL : (X.adjoinVertex N).comap (finSuccEquiv (n + 1)) ∈ levels (n + 2) :=
        ⟨f.connected_iff.mpr (hXL.1.adjoinVertex X N hN), hR.comp_iso f⟩
      exact mem_levels_of_iso (q.iso _).symm hL
    · intro Z hZ
      obtain ⟨P, hP, N, hN, ⟨f⟩⟩ := exists_parent_of_mem_levels (by omega) hZ
      obtain ⟨X, hX, ⟨e⟩⟩ := ih.2 P hP
      let N' : Set (Fin (n + 1)) := e ⁻¹' N
      have hN' : N'.Nonempty := by
        obtain ⟨v, hv⟩ := hN
        exact ⟨e.symm v, by simpa only [N', Set.mem_preimage, e.apply_symm_apply] using hv⟩
      let i : X.adjoinVertex N' ≃g Z := (e.adjoinVertex N).trans f
      let T := (X.adjoinVertex N').comap (finSuccEquiv (n + 1))
      have hT : T ∈ growthChildren c X :=
        (mem_growthChildren_iff c (ih.1 hX) T).mpr ⟨N', hN', hZ.2.comp_iso i, rfl⟩
      refine ⟨q.canon T, ⟨X, hX, T, hT, rfl⟩, ?_⟩
      exact ⟨((q.iso T).trans (Iso.comap (finSuccEquiv (n + 1)) _)).trans i⟩

-- Theorem 3.6 [Exc]
/-- Soundness of the growth in `thm:growth` (Theorem 3.6) of [Exc]. The empty
zeroth growth set also satisfies this inclusion. -/
theorem growth_subset_levels (c : CertificateChoice) (q : CanonicalForm) (n : ℕ) :
    growth c q n ⊆ levels n := by
  cases n with
  | zero => exact Set.empty_subset _
  | succ n => exact (growth_sound_and_complete_succ c q n).1

-- Theorem 3.6 [Exc]
/-- Theorem `thm:growth` (Theorem 3.6) of [Exc]: every graph in a nonempty-numbered
level is isomorphic to exactly one generated graph, for every canonical form and every valid
choice of certificates. -/
theorem existsUnique_mem_growth_iso (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (hn : 1 ≤ n) {Z : SimpleGraph (Fin n)} (hZ : Z ∈ levels n) :
    ∃! X, X ∈ growth c q n ∧ Nonempty (X ≃g Z) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨X, hX, ⟨e⟩⟩ := (growth_sound_and_complete_succ c q m).2 Z hZ
  refine ⟨X, ⟨hX, ⟨e⟩⟩, ?_⟩
  rintro Y ⟨hY, ⟨f⟩⟩
  exact eq_of_mem_growth_of_iso c q hY hX ⟨f.trans e.symm⟩

-- Theorem 3.6 [Exc]
/-- Theorem `thm:growth` (Theorem 3.6) of [Exc], with soundness and unique
representation of each isomorphism class in a single statement. -/
theorem growth_represents_levels (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (hn : 1 ≤ n) :
    growth c q n ⊆ levels n ∧
      ∀ Z ∈ levels n, ∃! X, X ∈ growth c q n ∧ Nonempty (X ≃g Z) :=
  ⟨growth_subset_levels c q n, fun _ hZ => existsUnique_mem_growth_iso c q hn hZ⟩

-- Theorem 3.6 [Exc]
/-- The growth stops at 36 vertices, by the level bound preceding `thm:growth`
(Theorem 3.6) of [Exc]. -/
theorem growth_eq_empty_of_ge (c : CertificateChoice) (q : CanonicalForm)
    {n : ℕ} (hn : 37 ≤ n) : growth c q n = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro X hX
  have h := growth_subset_levels c q n hX
  rw [levels_eq_empty_of_ge hn] at h
  exact h

end SimpleGraph
