/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.GraphCertificates

/-!
# SpectrumChecker

A single list/Bool spectral checker, implementing the interface in the spectral toolkit.
A list of `(integer node, natural multiplicity)` pairs cannot have mismatched list lengths.
Distinct nodes are checked; zero multiplicities are permitted. -/

namespace Computations

/-- The prescribed `j`th moment, evaluated entirely over integers. -/
def spectrumMoment (data : List (ℤ × ℕ)) (j : ℕ) : ℤ :=
  (data.map fun x => (x.2 : ℤ) * x.1 ^ j).sum

/-- Check symmetry, distinct nodes, annihilation and all required trace moments. -/
def checkSpectrum (n : ℕ) (A : IntMatrix) (data : List (ℤ × ℕ)) : Bool :=
  checkSymmetric n A && decide (data.map Prod.fst).Nodup &&
  checkAnnihilator n A (data.map Prod.fst) &&
  checkTraces n A (List.ofFn fun j : Fin data.length => (j.val, spectrumMoment data j.val))

theorem checkSpectrum_multiplicities {n : ℕ} {A : IntMatrix} {data : List (ℤ × ℕ)}
    (h : checkSpectrum n A data = true) :
    ∀ i : Fin data.length, (toMatrix (R := ℝ) n A).eigenvalueMultiplicity
      (data[i.val].1 : ℝ) = data[i.val].2 := by
  obtain ⟨⟨⟨hs, hd⟩, hp⟩, ht⟩ := by
    simpa only [checkSpectrum, Bool.and_eq_true_iff] using h
  have he : List.ofFn (fun i : Fin data.length => data[i.val].1) = data.map Prod.fst := by
    exact List.ofFn_getElem_eq_map data Prod.fst
  have hinj : Function.Injective (fun i : Fin data.length => data[i.val].1) := by
    apply List.nodup_ofFn.mp
    rw [he]
    exact of_decide_eq_true hd
  apply multiplicities_eq_of_checks (fun i : Fin data.length => data[i.val].1)
    (fun i => data[i.val].2) (fun j => spectrumMoment data j.val) hinj hs
    (by simpa only [he] using hp) ht
  intro j
  have hm : List.ofFn (fun i : Fin data.length => (data[i.val].2 : ℤ) * data[i.val].1 ^ j.val) =
      data.map (fun x => (x.2 : ℤ) * x.1 ^ j.val) := by
    exact List.ofFn_getElem_eq_map data (fun x : ℤ × ℕ => (x.2 : ℤ) * x.1 ^ j.val)
  rw [spectrumMoment, ← hm, List.sum_ofFn]

/-- Boolean reflection interface requested by the spectral toolkit. -/
theorem checkSpectrum_sound {n : ℕ} {A : Computations.IntMatrix}
    {data : List (ℤ × ℕ)} (h : Computations.checkSpectrum n A data = true) :
    (Computations.toMatrix (R := ℝ) n A).spectrumMultiset =
      (data.map fun x => Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  rw [← List.ofFn_getElem_eq_map data (fun x => Multiset.replicate x.2 (x.1 : ℝ)),
    List.sum_ofFn]
  obtain ⟨⟨⟨hs, hd⟩, hp⟩, ht⟩ := by
    simpa only [Computations.checkSpectrum, Bool.and_eq_true_iff] using h
  have he : List.ofFn (fun i : Fin data.length => data[i.val].1) = data.map Prod.fst := by
    exact List.ofFn_getElem_eq_map data Prod.fst
  have hi : Function.Injective (fun i : Fin data.length => (data[i.val].1 : ℝ)) := by
    have hn : Function.Injective (fun i : Fin data.length => data[i.val].1) := by
      apply List.nodup_ofFn.mp
      rw [he]
      exact of_decide_eq_true hd
    intro i j hij
    exact hn (Int.cast_injective hij)
  apply (Computations.checkSymmetric_sound hs).spectrumMultiset_eq_of_annihilatingPolynomial_trace
    (fun i : Fin data.length => (data[i.val].1 : ℝ)) hi
    (fun i => data[i.val].2)
    (Computations.checkAnnihilator_sound_ofFn (fun i : Fin data.length => data[i.val].1)
      (by simpa only [he] using hp))
  intro j
  rw [(Computations.checkSymmetric_sound hs).trace_pow_eq_multiplicities
    (fun i : Fin data.length => (data[i.val].1 : ℝ)) hi
    (Computations.checkAnnihilator_sound_ofFn (fun i : Fin data.length => data[i.val].1)
      (by simpa only [he] using hp))]
  simp_rw [Computations.checkSpectrum_multiplicities h]

/-- The spectrum certificate now states the spectrum of an actual graph. -/
theorem spectrum_graphOfMatrix_of_checkSpectrum {n : ℕ} {A : IntMatrix}
    {data : List (ℤ × ℕ)} (hA : checkAdjacency n A = true)
    (h : checkSpectrum n A data = true) :
    (graphOfMatrix hA).spectrumMultiset =
      (data.map fun x => Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  simpa only [SimpleGraph.spectrumMultiset, adjMatrix_graphOfMatrix] using checkSpectrum_sound h

/-- A spectrum certificate transfers to a graph on any explicitly labelled finite vertex type. -/
theorem spectrum_eq_of_checkSpectrum {n : ℕ} {A : IntMatrix} {data : List (ℤ × ℕ)}
    (hA : checkAdjacency n A = true) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : Fin n ≃ V)
    (hG : ∀ i j, G.Adj (label i) (label j) ↔ entry A i j = 1)
    (h : checkSpectrum n A data = true) :
    G.spectrumMultiset = (data.map fun x => Multiset.replicate x.2 (x.1 : ℝ)).sum := by
  have he := (graphOfMatrixIso hA G label hG).cospectral
  change ((graphOfMatrix hA).adjMatrix ℝ).charpoly = (G.adjMatrix ℝ).charpoly at he
  change (G.adjMatrix ℝ).charpoly.roots = _
  rw [← he, adjMatrix_graphOfMatrix]
  exact checkSpectrum_sound h

end Computations

/-- Compatibility name requested by the spectral toolkit. -/
alias Matrix.spectrumCertificate_sound := Computations.checkSpectrum_sound
