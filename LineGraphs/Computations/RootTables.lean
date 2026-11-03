/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.Checkers
import LineGraphs.LineSystem.IntegerModel

/-!
# Computable root tables and their mathematical interface

Structured indices serve counting and parametric proofs. Explicit lists give a computable
single-pass interface to the certificate checkers; fixed exceptional tables are materialized
in separate modules so the pair sweeps do not repeatedly evaluate the structured roots.
-/

namespace Computations

/-- A root table evaluated from a supplied executable enumeration of the indices. -/
def indexedRootTable {n : ℕ} {ι : Type*} (indices : List ι) (v : ι → Fin n → ℤ) :
    List IntVector := indices.map (fun a ↦ List.ofFn (v a))

theorem mem_indexedRootTable {n : ℕ} {ι : Type*} (indices : List ι)
    (cover : ∀ a, a ∈ indices) (v : ι → Fin n → ℤ) (w : IntVector) :
    w ∈ indexedRootTable indices v ↔ ∃ a, List.ofFn (v a) = w := by
  simp only [indexedRootTable, List.mem_map]
  exact ⟨fun ⟨a, _, ha⟩ ↦ ⟨a, ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, cover a, ha⟩⟩

/-- An injective list with the full finite cardinality covers every index. -/
theorem mem_indices_of_image {ι : Type*} [Fintype ι] {indices : List ι}
    {table : List IntVector} {f : ι → IntVector}
    (image : table = indices.map f) (nodup : table.Nodup)
    (length : table.length = Fintype.card ι) (a : ι) : a ∈ indices := by
  classical
  have hn : indices.Nodup := List.Nodup.of_map f (image ▸ nodup)
  have hl : indices.length = Fintype.card ι := by simpa [image] using length
  have he : indices.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hn, hl])
  exact List.mem_toFinset.mp (he ▸ Finset.mem_univ a)

/-- Coverage, distinctness and the cardinality identify a finite integer root table. -/
theorem rootTable_eq_image {n : ℕ} {ι : Type*} [Fintype ι]
    {v : ι → Fin n → ℤ} {table : List IntVector} (hinj : Function.Injective v)
    (cover : ∀ a, List.ofFn (v a) ∈ table) (nodup : table.Nodup)
    (length : table.length = Fintype.card ι) :
    table.toFinset = Finset.univ.image (fun a => List.ofFn (v a)) := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.mem_toFinset.mpr (cover a)
  · rw [Finset.card_image_of_injective _ (fun _ _ h => hinj (List.ofFn_inj.mp h)),
      Finset.card_univ, List.toFinset_card_of_nodup nodup, length]

/-- List membership is a total decoder, including for integer vectors outside the root range. -/
def decodeRoot (table : List IntVector) {n : ℕ} (w : Fin n → ℤ) : Bool :=
  table.contains (List.ofFn w)

@[simp] theorem decodeRoot_eq_true (table : List IntVector) {n : ℕ} (w : Fin n → ℤ) :
    decodeRoot table w = true ↔ List.ofFn w ∈ table := by simp [decodeRoot]

@[simp] theorem vectorAdd_ofFn {n : ℕ} (v w : Fin n → ℤ) :
    vectorAdd (List.ofFn v) (List.ofFn w) = List.ofFn (v + w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    exact congrArg (List.cons (v 0 + w 0)) (ih (fun i ↦ v i.succ) (fun i ↦ w i.succ))

end Computations

namespace LineSystem.IntegerModel

open Computations

variable {n : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin n))} (M : IntegerModel S)

open scoped RealInnerProductSpace

/-- Gram certificates use the integer model's scale and coordinate functions. -/
theorem inner_eq_of_checkGram {m : ℕ} (a : Fin m → M.ι) {G : IntMatrix}
    (h : checkGram n (List.ofFn fun i => List.ofFn (M.v (a i))) G = true) (i j : Fin m) :
    ⟪integerVector M.c (M.v (a i)), integerVector M.c (M.v (a j))⟫ =
      M.c * M.c * toMatrix (R := ℝ) m G i j := by
  have hd : M.v (a i) ⬝ᵥ M.v (a j) = entry G i j := by
    have hh := checkGram_sound h ⟨i.val, by simp⟩
      ⟨j.val, by simp⟩
    simpa [dot_ofFn, toMatrix] using hh
  rw [inner_integerVector, integerInner, hd]
  rfl

/-- Transport membership through a materialized root table. -/
theorem mem_iff_table {table : List IntVector}
    (htable : ∀ w, w ∈ table ↔ ∃ a, List.ofFn (M.v a) = w) (w : Fin n → ℤ) :
    integerVector M.c w ∈ S.Φ ↔ decodeRoot table w = true := by
  rw [M.mem_iff, decodeRoot_eq_true, htable]
  simp only [List.ofFn_inj]

/-- The existing list checker transfers directly through any integer model presentation. -/
theorem isStarClosed_of_checkStar {table : List IntVector} {decode : IntVector → Bool}
    (cover : ∀ a, List.ofFn (M.v a) ∈ table)
    (sound : ∀ w, decode (List.ofFn w) = true → ∃ a, M.v a = w)
    (checked : checkStar n (-M.q) decode table = true) : S.IsStarClosed := by
  apply M.isStarClosed_of_decoder (fun w ↦ decode (List.ofFn w)) sound
  intro a b hab
  have h := checkStar_sound checked (cover a) (cover b)
    (by simpa only [dot_ofFn, integerInner, dotProduct] using hab)
  simpa only [vectorAdd_ofFn] using h

end LineSystem.IntegerModel
