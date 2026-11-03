/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.GraphCertificates
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Multiset.Powerset

/-!
# Clique invariants and non-isomorphism certificates

Enumeration prunes candidates to common neighbours before extending a clique. Only actual
cliques are materialized. Profiles retain the per-vertex counts needed for C22.
-/

namespace Computations

/-- Extend cliques by one vertex, restricting the recursive search to its later neighbours. -/
def cliqueExtensions {α : Type*} (adj : α → α → Bool) (next : List α → List (List α)) :
    List α → List (List α)
  | [] => []
  | v :: vs => cliqueExtensions adj next vs ++ (next (vs.filter (adj v))).map (v :: ·)

/-- Enumerate fixed-size cliques by structural recursion, so the kernel can evaluate the search. -/
def cliquesOn {α : Type*} (adj : α → α → Bool) : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | k + 1, vs => cliqueExtensions adj (cliquesOn adj k) vs

private theorem sublistsLen_filter {α : Type*} (p : α → Bool) (k : ℕ) (vs : List α) :
    (vs.filter p).sublistsLen k = (vs.sublistsLen k).filter (fun s => s.all p) := by
  induction vs generalizing k with
  | nil => cases k <;> simp [List.filter_cons, List.all_nil]
  | cons v vs ih =>
    cases k with
    | zero => simp [List.filter_cons, List.all_nil]
    | succ k =>
      by_cases hv : p v = true <;>
        simp [List.sublistsLen_succ_cons, hv, ih, List.filter_append, List.filter_map,
          Function.comp_def, List.all_cons]

/-- The pruned enumeration equals exhaustive fixed-size subset enumeration. -/
theorem cliquesOn_eq_filter {α : Type*} (adj : α → α → Bool) (k : ℕ) (vs : List α) :
    cliquesOn adj k vs =
      (vs.sublistsLen k).filter (fun s => decide (s.Pairwise (fun i j => adj i j = true))) := by
  induction k generalizing vs with
  | zero => simp [cliquesOn]
  | succ k ih =>
    induction vs with
    | nil => simp [cliquesOn, cliqueExtensions]
    | cons v vs ihvs =>
      simp only [cliquesOn] at ihvs
      simp only [cliquesOn, cliqueExtensions, ih, ihvs, sublistsLen_filter,
        List.sublistsLen_succ_cons,
        List.filter_append, List.filter_map, List.filter_filter]
      congr 1
      congr 1
      congr 1
      funext s
      apply Bool.eq_iff_iff.mpr
      simp [List.pairwise_cons, List.all_eq_true, and_comm]

/-- Fixed-size cliques in an integer adjacency table. -/
def matrixCliques (n k : ℕ) (A : IntMatrix) : List (List (Fin n)) :=
  cliquesOn (fun i j => entry A i j == 1) k (List.finRange n)

/-- The number of cliques of the requested size. -/
def cliqueCount (n k : ℕ) (A : IntMatrix) : ℕ := (matrixCliques n k A).length

/-- The number of cliques through each vertex, retaining repetitions in the profile. -/
def cliqueProfile (n k : ℕ) (A : IntMatrix) : List ℕ :=
  let cs := matrixCliques n k A
  (List.finRange n).map fun i => cs.countP (fun s => s.contains i)

end Computations

namespace SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The fixed-size vertex subsets which are cliques; all multiplicities are one. -/
noncomputable def cliqueMultiset (G : SimpleGraph V) (k : ℕ) : Multiset (Multiset V) := by
  classical
  exact (Finset.univ.val.powersetCard k).filter (fun s => s.Pairwise G.Adj)

/-- Isomorphisms carry the entire clique family to the other graph. -/
theorem Iso.cliqueMultiset_map {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    H.cliqueMultiset k = (G.cliqueMultiset k).map (Multiset.map e) := by
  classical
  have hu : (Finset.univ : Finset W).val = (Finset.univ : Finset V).val.map e := by
    exact congrArg Finset.val (Finset.univ_map_equiv_to_embedding e.toEquiv).symm
  let : Std.Symm G.Adj := G.symm
  let : Std.Symm H.Adj := H.symm
  have hp (s : Multiset V) : (s.map e).Pairwise H.Adj ↔ s.Pairwise G.Adj := by
    induction s using Quotient.inductionOn with
    | h l => simp [Multiset.pairwise_coe_iff_pairwise, List.pairwise_map, e.map_adj_iff]
  simp only [cliqueMultiset, hu, Multiset.powersetCard_map, Multiset.filter_map]
  simp only [Function.comp_def, hp]

/-- The multiset of per-vertex clique counts is an isomorphism invariant. -/
noncomputable def cliqueProfile (G : SimpleGraph V) (k : ℕ) : Multiset ℕ := by
  classical
  exact Finset.univ.val.map fun v => ((G.cliqueMultiset k).filter (v ∈ ·)).card

theorem Iso.cliqueProfile_eq {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (k : ℕ) :
    G.cliqueProfile k = H.cliqueProfile k := by
  classical
  have hu : (Finset.univ : Finset W).val = (Finset.univ : Finset V).val.map e := by
    exact congrArg Finset.val (Finset.univ_map_equiv_to_embedding e.toEquiv).symm
  simp only [cliqueProfile, hu, e.cliqueMultiset_map, Multiset.map_map,
    Multiset.filter_map, Multiset.card_map, Function.comp_def]
  congr 1
  funext v
  congr 1
  apply Multiset.filter_congr
  intro s _
  simp

end SimpleGraph

namespace Computations

/-- The list enumeration is exactly the mathematical family of clique subsets. -/
theorem matrixCliques_sound {n : ℕ} {A : IntMatrix} (h : checkAdjacency n A = true) (k : ℕ) :
    Multiset.ofList ((matrixCliques n k A).map (fun s : List (Fin n) => Multiset.ofList s)) =
      (graphOfMatrix h).cliqueMultiset k := by
  classical
  let : Std.Symm (graphOfMatrix h).Adj := (graphOfMatrix h).symm
  have hu : (List.finRange n : Multiset (Fin n)) = Finset.univ.val := by
    ext i
    simp
  simp only [matrixCliques, cliquesOn_eq_filter, SimpleGraph.cliqueMultiset, ← hu,
    Multiset.powersetCard_coe, Multiset.filter_coe, List.filter_map]
  apply congrArg (Multiset.ofList (α := Multiset (Fin n)))
  apply congrArg (List.map (Multiset.ofList (α := Fin n)))
  apply List.filter_congr
  intro s _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, beq_iff_eq]
  exact (Multiset.pairwise_coe_iff_pairwise (r := (graphOfMatrix h).Adj) (l := s)).symm

theorem cliqueProfile_sound {n : ℕ} {A : IntMatrix} (h : checkAdjacency n A = true) (k : ℕ) :
    (cliqueProfile n k A : Multiset ℕ) = (graphOfMatrix h).cliqueProfile k := by
  classical
  have hu : (List.finRange n : Multiset (Fin n)) = Finset.univ.val := by
    ext i
    simp
  rw [SimpleGraph.cliqueProfile, ← matrixCliques_sound h k, ← hu, Multiset.map_coe]
  apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
  apply List.map_congr_left
  intro i _
  simp [List.countP_eq_length_filter, Multiset.filter_coe, List.filter_map,
    Function.comp_def]

/-- The global count is the cardinality of the mathematical clique family. -/
theorem cliqueCount_sound {n : ℕ} {A : IntMatrix} (h : checkAdjacency n A = true) (k : ℕ) :
    cliqueCount n k A = ((graphOfMatrix h).cliqueMultiset k).card := by
  simpa [cliqueCount] using congrArg Multiset.card (matrixCliques_sound h k)

/-- Every graph isomorphism preserves the computable profile, up to reordering. -/
theorem cliqueProfile_perm_of_iso {n k : ℕ} {A B : IntMatrix}
    {hA : checkAdjacency n A = true} {hB : checkAdjacency n B = true}
    (e : graphOfMatrix hA ≃g graphOfMatrix hB) :
    (cliqueProfile n k A).Perm (cliqueProfile n k B) := by
  apply Multiset.coe_eq_coe.mp
  rw [cliqueProfile_sound hA, cliqueProfile_sound hB]
  exact e.cliqueProfile_eq k

/-- Checked permutations preserve the same invariant as arbitrary graph isomorphisms. -/
theorem cliqueProfile_perm_of_checkGraphIso {n k : ℕ} {A B : IntMatrix} {p : List ℕ}
    (hA : checkAdjacency n A = true) (hB : checkAdjacency n B = true)
    (h : checkGraphIso n A B p = true) : (cliqueProfile n k A).Perm (cliqueProfile n k B) := by
  obtain ⟨e⟩ := nonempty_graphOfMatrix_iso hA hB h
  exact cliqueProfile_perm_of_iso e

/-- Check unequal per-vertex clique-count multisets, including adjacency guards. -/
def checkNonisomorphic (n k : ℕ) (A B : IntMatrix) : Bool :=
  checkAdjacency n A && checkAdjacency n B &&
    !decide ((cliqueProfile n k A).Perm (cliqueProfile n k B))

/-- Different profiles rule out every isomorphism, not merely the supplied permutations. -/
theorem checkNonisomorphic_sound {n k : ℕ} {A B : IntMatrix}
    (hA : checkAdjacency n A = true) (hB : checkAdjacency n B = true)
    (h : checkNonisomorphic n k A B = true) :
    ¬ Nonempty (graphOfMatrix hA ≃g graphOfMatrix hB) := by
  rintro ⟨e⟩
  have he := e.cliqueProfile_eq k
  rw [← cliqueProfile_sound hA k, ← cliqueProfile_sound hB k] at he
  have hp := Multiset.coe_eq_coe.mp he
  simp only [checkNonisomorphic, Bool.and_eq_true_iff, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact h.2 hp

/-- Non-isomorphism transfers back to arbitrary labelled vertex types. -/
theorem not_nonempty_iso_of_checkNonisomorphic {n k : ℕ} {A B : IntMatrix}
    (hA : checkAdjacency n A = true) (hB : checkAdjacency n B = true)
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (v : Fin n ≃ V) (w : Fin n ≃ W)
    (hG : ∀ i j, G.Adj (v i) (v j) ↔ entry A i j = 1)
    (hH : ∀ i j, H.Adj (w i) (w j) ↔ entry B i j = 1)
    (h : checkNonisomorphic n k A B = true) : ¬ Nonempty (G ≃g H) := by
  rintro ⟨e⟩
  exact checkNonisomorphic_sound hA hB h
    ⟨(graphOfMatrixIso hA G v hG).trans (e.trans (graphOfMatrixIso hB H w hH).symm)⟩

end Computations
