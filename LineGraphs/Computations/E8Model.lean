/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.E8Data
import LineGraphs.Computations.RootTables
import LineGraphs.LineSystem.Models

/-!
# E8Model

C4: identification of the checked lists with the existing structured E₈ model.
Only this bridge imports `Models`; the large pair sweeps use the list data alone. -/

namespace Computations.E₈Data

/-- List enumeration of Boolean functions, with a structural completeness proof. -/
def signFunctions : (n : ℕ) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n + 1 => (signFunctions n).flatMap fun s => [Fin.cons false s, Fin.cons true s]

theorem mem_signFunctions {n : ℕ} (s : Fin n → Bool) : s ∈ signFunctions n := by
  induction n with
  | zero => simp [signFunctions, Subsingleton.elim s Fin.elim0]
  | succ n ih =>
    rw [signFunctions, List.mem_flatMap]
    refine ⟨Fin.tail s, ih _, ?_⟩
    have hs : s = Fin.cons (s 0) (Fin.tail s) := (Fin.cons_self_tail s).symm
    rw [hs]
    cases s 0 <;> simp

/-- The small list used only to certify coverage of `Models.e₈Root`. -/
def e₈Indices : List LineSystem.E₈Index :=
  (List.finRange 8).flatMap (fun i => (List.finRange 8).flatMap (fun j =>
    if h : i < j then [Sum.inl (⟨(i, j), h⟩, (false, false)),
      Sum.inl (⟨(i, j), h⟩, (false, true)), Sum.inl (⟨(i, j), h⟩, (true, false)),
      Sum.inl (⟨(i, j), h⟩, (true, true))] else [])) ++
  (signFunctions 7).map Sum.inr

theorem mem_e₈Indices (a : LineSystem.E₈Index) : a ∈ e₈Indices := by
  rcases a with ⟨⟨⟨i, j⟩, hij⟩, b, c⟩ | s
  · apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange i, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_finRange j, ?_⟩
    simp only [dite_eq_left hij]
    cases b <;> cases c <;> simp
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨s, mem_signFunctions s, rfl⟩)

/-- Twenty structured indices per coverage certificate. -/
def e₈IndexChunk (k : ℕ) := (e₈Indices.drop (20 * k)).take 20

theorem e₈_coverage_chunk_0 : (e₈IndexChunk 0).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_1 : (e₈IndexChunk 1).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_2 : (e₈IndexChunk 2).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_3 : (e₈IndexChunk 3).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_4 : (e₈IndexChunk 4).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_5 : (e₈IndexChunk 5).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_6 : (e₈IndexChunk 6).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_7 : (e₈IndexChunk 7).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_8 : (e₈IndexChunk 8).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_9 : (e₈IndexChunk 9).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_10 : (e₈IndexChunk 10).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_chunk_11 : (e₈IndexChunk 11).all
    (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  decide +kernel

theorem e₈_coverage_checked :
    e₈Indices.all (fun a => e₈Tree.contains (List.ofFn (LineSystem.e₈Root a))) = true := by
  have he : e₈Indices = (List.range 12).flatMap e₈IndexChunk := by
    have hc : decide (e₈Indices = (List.range 12).flatMap e₈IndexChunk) = true := by
      decide +kernel
    exact of_decide_eq_true hc
  apply all_eq_true_of_chunks he
  apply List.all_eq_true.mp
  simp only [List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    e₈_coverage_chunk_0,
    e₈_coverage_chunk_1,
    e₈_coverage_chunk_2,
    e₈_coverage_chunk_3,
    e₈_coverage_chunk_4,
    e₈_coverage_chunk_5,
    e₈_coverage_chunk_6,
    e₈_coverage_chunk_7,
    e₈_coverage_chunk_8,
    e₈_coverage_chunk_9,
    e₈_coverage_chunk_10,
    e₈_coverage_chunk_11, Bool.and_self]

theorem e₈_count_checked : (e₈Roots.length == 240) = true := by decide +kernel

theorem e₈_keys_checked : decide ((e₈Roots.map vectorKey).IsChain (· < ·)) = true := by
  decide +kernel

theorem e₈_nodup_checked : decide e₈Roots.Nodup = true := by
  apply decide_eq_true
  exact List.Nodup.of_map vectorKey
    (List.isChain_iff_pairwise.mp (of_decide_eq_true e₈_keys_checked)).nodup

theorem ofFn_e₈Root_mem (a : LineSystem.E₈Index) :
    List.ofFn (LineSystem.e₈Root a) ∈ e₈Roots :=
  VectorTree.contains_sound (List.all_eq_true.mp e₈_coverage_checked a (mem_e₈Indices a))

theorem e₈Roots_eq_image : e₈Roots.toFinset =
    Finset.univ.image (fun a => List.ofFn (LineSystem.e₈Root a)) := by
  exact rootTable_eq_image LineSystem.e₈Root_injective ofFn_e₈Root_mem
    (of_decide_eq_true e₈_nodup_checked)
    (by simpa only [beq_iff_eq, LineSystem.card_E₈Index] using e₈_count_checked)

theorem e₈Roots_sound {v : IntVector} (hv : v ∈ e₈Roots) :
    ∃ a, List.ofFn (LineSystem.e₈Root a) = v := by
  have hm : v ∈ e₈Roots.toFinset := List.mem_toFinset.mpr hv
  rw [e₈Roots_eq_image] at hm
  simpa using hm

end Computations.E₈Data
