/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Seidel.RootTransitivity
import LineGraphs.Seidel.LineGraphCounts
import LineGraphs.Computations.C22Labels

/-! # The three endpoint graphs at the apex

The graphs `Δ₆`, `Δ₇`, `Δ₈` of `comp:414-Nc` and `lem:414-transversal` (Remark 4.14).
-/

namespace SimpleGraph

/-- The graph `Δ₆` in `comp:414-Nc`: a complete graph on the first five of eight endpoints. -/
def apexGraph6 : SimpleGraph (Fin 8) where
  Adj i j := i ≠ j ∧ i.val < 5 ∧ j.val < 5
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := h.1 rfl

/-- Adjacency decisions for the endpoint graph `Δ₆` of Remark 4.14. -/
instance apexGraph6DecidableAdj : DecidableRel apexGraph6.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The graph `Δ₇` in `comp:414-Nc`: `K₆` and the edge on the last two endpoints. -/
def apexGraph7 : SimpleGraph (Fin 8) where
  Adj i j := i ≠ j ∧ ((i.val < 6 ∧ j.val < 6) ∨ (6 ≤ i.val ∧ 6 ≤ j.val))
  symm.symm _ _ h := ⟨h.1.symm, h.2.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)⟩
  loopless.irrefl _ h := h.1 rfl

/-- Adjacency decisions for the endpoint graph `Δ₇` of Remark 4.14. -/
instance apexGraph7DecidableAdj : DecidableRel apexGraph7.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- C20's ordered pairs as actual edges of `Δ₆` (`comp:414-Nc`). -/
def apexGraph6Edge (p : LineSystem.E₆.CEdge) : apexGraph6.edgeSet :=
  ⟨s(p.1.1, p.1.2), p.2.1.ne, lt_trans p.2.1 p.2.2, p.2.2⟩

/-- C20's ordered pairs enumerate the edges of `Δ₆` (`comp:414-Nc`). -/
theorem apexGraph6Edge_bijective : Function.Bijective apexGraph6Edge := by decide +kernel

/-- C20's ordered pairs as actual edges of `Δ₆` (`comp:414-Nc`). -/
noncomputable def apexGraph6EdgeEquiv : LineSystem.E₆.CEdge ≃ apexGraph6.edgeSet :=
  Equiv.ofBijective apexGraph6Edge apexGraph6Edge_bijective

/-- C20's ordered pairs as actual edges of `Δ₇` (`comp:414-Nc`). -/
def apexGraph7Edge (p : LineSystem.E₇.CEdge) : apexGraph7.edgeSet :=
  ⟨s(p.1.1, p.1.2), p.2.1.ne, by
    rcases p.2.2 with h | ⟨hi, hj⟩
    · exact Or.inl ⟨lt_trans p.2.1 h, h⟩
    · exact Or.inr ⟨by change 6 ≤ p.1.1.val; omega, by change 6 ≤ p.1.2.val; omega⟩⟩

/-- C20's ordered pairs enumerate the edges of `Δ₇` (`comp:414-Nc`). -/
theorem apexGraph7Edge_bijective : Function.Bijective apexGraph7Edge := by decide +kernel

/-- The edge equivalence for `Δ₇` (`comp:414-Nc`). -/
noncomputable def apexGraph7EdgeEquiv : LineSystem.E₇.CEdge ≃ apexGraph7.edgeSet :=
  Equiv.ofBijective apexGraph7Edge apexGraph7Edge_bijective

/-- Restrict the first five endpoints of `Δ₆` to `Fin 5` (`lem:414-E6`). -/
def apexPair5 (p : LineSystem.E₆.CEdge) : Computations.C22.Pair 5 :=
  ⟨(⟨p.1.1, lt_trans p.2.1 p.2.2⟩, ⟨p.1.2, p.2.2⟩), p.2.1⟩

/-- The endpoint restriction in `lem:414-E6` is bijective. -/
theorem apexPair5_bijective : Function.Bijective apexPair5 := by decide +kernel

/-- Separate the last edge of `Δ₇` from the first six endpoints (`lem:414-E7`). -/
def apexSumPair6 (p : LineSystem.E₇.CEdge) : Computations.C22.Pair 6 ⊕ Fin 1 :=
  if h : p.1.2.val < 6 then
    Sum.inl ⟨(⟨p.1.1, lt_trans p.2.1 h⟩, ⟨p.1.2, h⟩), p.2.1⟩ else Sum.inr 0

/-- The endpoint restriction in `lem:414-E7` is bijective. -/
theorem apexSumPair6_bijective : Function.Bijective apexSumPair6 := by decide +kernel

/-- The endpoint-pair formula for the base graph in `lem:414-E7`. -/
theorem triangularAddOne_adj_sumPair {n : ℕ} (p q : Computations.C22.Pair n ⊕ Fin 1) :
    (triangularAddOne n).Adj
      ((Equiv.sumCongr (completeGraphEdgeEquiv (Fin n)) (Equiv.refl (Fin 1))) p)
      ((Equiv.sumCongr (completeGraphEdgeEquiv (Fin n)) (Equiv.refl (Fin 1))) q) ↔
        Computations.C22.sumPairAdj p q := by
  rcases p with p | p <;> rcases q with q | q <;>
    simp [triangularAddOne, Computations.C22.sumPairAdj, Computations.C22.pairAdj,
      lineGraph_completeGraph_adj]

set_option backward.isDefEq.respectTransparency false in
/-- Identify `L(Δ₆)` with `T(5)` in `lem:414-E6`. -/
noncomputable def apexGraph6LineIso : apexGraph6.lineGraph ≃g
    (⊤ : SimpleGraph (Fin 5)).lineGraph := by
  let f := (Equiv.ofBijective apexPair5 apexPair5_bijective).trans
    (completeGraphEdgeEquiv (Fin 5))
  refine { toEquiv := apexGraph6EdgeEquiv.symm.trans f, map_rel_iff' := ?_ }
  intro u v
  obtain ⟨p, rfl⟩ := apexGraph6EdgeEquiv.surjective u
  obtain ⟨q, rfl⟩ := apexGraph6EdgeEquiv.surjective v
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change (⊤ : SimpleGraph (Fin 5)).lineGraph.Adj
    (completeGraphEdgeEquiv (Fin 5) (apexPair5 p))
    (completeGraphEdgeEquiv (Fin 5) (apexPair5 q)) ↔ _
  rw [lineGraph_completeGraph_adj]
  change Computations.C22.pairAdj (apexPair5 p) (apexPair5 q) ↔
    apexGraph6.lineGraph.Adj (apexGraph6Edge p) (apexGraph6Edge q)
  unfold apexGraph6Edge
  rw [lineGraph_adj_mk_iff]
  exact (by decide +kernel : ∀ p q : LineSystem.E₆.CEdge,
    Computations.C22.pairAdj (apexPair5 p) (apexPair5 q) ↔
      s(p.1.1, p.1.2) ≠ s(q.1.1, q.1.2) ∧
        (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2)) p q

set_option backward.isDefEq.respectTransparency false in
/-- Identify `L(Δ₇)` with `T(6)` and an isolated vertex in `lem:414-E7`. -/
noncomputable def apexGraph7LineIso : apexGraph7.lineGraph ≃g triangularAddOne 6 := by
  let f := (Equiv.ofBijective apexSumPair6 apexSumPair6_bijective).trans
    (Equiv.sumCongr (completeGraphEdgeEquiv (Fin 6)) (Equiv.refl (Fin 1)))
  refine { toEquiv := apexGraph7EdgeEquiv.symm.trans f, map_rel_iff' := ?_ }
  intro u v
  obtain ⟨p, rfl⟩ := apexGraph7EdgeEquiv.surjective u
  obtain ⟨q, rfl⟩ := apexGraph7EdgeEquiv.surjective v
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change (triangularAddOne 6).Adj
    ((Equiv.sumCongr (completeGraphEdgeEquiv (Fin 6)) (Equiv.refl (Fin 1))) (apexSumPair6 p))
    ((Equiv.sumCongr (completeGraphEdgeEquiv (Fin 6)) (Equiv.refl (Fin 1))) (apexSumPair6 q)) ↔ _
  rw [triangularAddOne_adj_sumPair]
  change Computations.C22.sumPairAdj (apexSumPair6 p) (apexSumPair6 q) ↔
    apexGraph7.lineGraph.Adj (apexGraph7Edge p) (apexGraph7Edge q)
  unfold apexGraph7Edge
  rw [lineGraph_adj_mk_iff]
  exact (by decide +kernel : ∀ p q : LineSystem.E₇.CEdge,
    Computations.C22.sumPairAdj (apexSumPair6 p) (apexSumPair6 q) ↔
      s(p.1.1, p.1.2) ≠ s(q.1.1, q.1.2) ∧
        (p.1.1 = q.1.1 ∨ p.1.1 = q.1.2 ∨ p.1.2 = q.1.1 ∨ p.1.2 = q.1.2)) p q

end SimpleGraph
