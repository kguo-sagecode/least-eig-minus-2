/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.RootSetClassification.LineCounts

/-!
# Similarity invariants and uniqueness of the coordinate model

Steps `rBinvariants`--`rBBCunique` of the indecomposable classification in
Remark 3.11 of [CGSS]. Rank, total root count, and the number of shortest roots
already distinguish the canonical list. The full length-count function is
transported as well, with its argument multiplied by the similarity factor.
-/

open scoped RealInnerProductSpace

namespace IsRootSet.IsSimilarity

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Φ : Set V} {Ψ : Set W} {f : V ≃ₗ[ℝ] W} {a : ℝ}

/-- Step `rBinvariants`: a similarity preserves the number of roots. -/
theorem ncard_eq (hf : IsRootSet.IsSimilarity Φ Ψ f a) : Φ.ncard = Ψ.ncard := by
  rw [← hf.image_eq, Set.ncard_image_of_injective _ f.injective]

/-- Step `rBinvariants`: a similarity transports every squared-length count. -/
theorem length_ncard_eq (hf : IsRootSet.IsSimilarity Φ Ψ f a) (q : ℝ) :
    {r ∈ Φ | ⟪r, r⟫ = q}.ncard = {s ∈ Ψ | ⟪s, s⟫ = a * q}.ncard := by
  have he : f '' {r ∈ Φ | ⟪r, r⟫ = q} = {s ∈ Ψ | ⟪s, s⟫ = a * q} := by
    ext s
    constructor
    · rintro ⟨r, ⟨hr, hq⟩, rfl⟩
      exact ⟨hf.image_eq ▸ Set.mem_image_of_mem f hr, by rw [hf.inner_map, hq]⟩
    · rintro ⟨hs, hq⟩
      obtain ⟨r, hr, rfl⟩ := hf.image_eq ▸ hs
      rw [hf.inner_map] at hq
      exact ⟨r, ⟨hr, mul_left_cancel₀ (ne_of_gt hf.factor_pos) hq⟩, rfl⟩
  rw [← he, Set.ncard_image_of_injective _ f.injective]

end IsRootSet.IsSimilarity

namespace RootSetModel

/-- The least squared root length in the table of `lem:counts`, Remark 3.11. -/
def minLengthSq {n : ℕ} : CartanMatrix.FiniteType n → ℝ
  | .b _ _ | .f₄ => 1
  | _ => 2

/-- The number of shortest roots, used in `rBinvariants`--`rBBCunique` of Remark 3.11. -/
def shortRootCount {n : ℕ} : CartanMatrix.FiniteType n → ℕ
  | .b n _ => 2 * n
  | .c n _ => 2 * n * (n - 1)
  | .f₄ => 24
  | .g₂ => 6
  | t => rootCount t

/-- The shortest-root column of `lem:counts`, including the one-length cases. -/
theorem lengthCount_minLengthSq {n : ℕ} (t : CartanMatrix.FiniteType n) :
    lengthCount t (minLengthSq t) = shortRootCount t := by
  cases t <;> simp [lengthCount, minLengthSq, shortRootCount]

/-- The minimum squared lengths in `lem:counts` are positive. -/
theorem minLengthSq_pos {n : ℕ} (t : CartanMatrix.FiniteType n) : 0 < minLengthSq t := by
  cases t <;> norm_num [minLengthSq]

/-- Every model has at least one shortest root (`rBinvariants`). -/
theorem shortRootCount_pos {n : ℕ} (t : CartanMatrix.FiniteType n) : 0 < shortRootCount t := by
  have hn := t.rank_pos
  cases t <;> dsimp [shortRootCount, rootCount]
  all_goals first | positivity | exact mul_pos (mul_pos (by decide) hn) (by omega)

/-- The count table bounds every squared root length from below (`rBinvariants`). -/
theorem minLengthSq_le {n : ℕ} (t : CartanMatrix.FiniteType n) {r : Space t}
    (hr : r ∈ roots t) : minLengthSq t ≤ ⟪r, r⟫ := by
  have hp : 0 < lengthCount t ⟪r, r⟫ := by
    rw [← length_counts]
    exact (Set.ncard_pos ((isRootSet t).finite.sep _)).mpr ⟨r, hr, rfl⟩
  cases t <;> dsimp [lengthCount, minLengthSq] at hp ⊢ <;>
    split_ifs at hp <;> first | omega | linarith

/-- The least length is attained in each model, as required in `rBinvariants`. -/
theorem exists_minLengthSq {n : ℕ} (t : CartanMatrix.FiniteType n) :
    ∃ r ∈ roots t, ⟪r, r⟫ = minLengthSq t := by
  apply (Set.ncard_pos ((isRootSet t).finite.sep _)).mp
  rw [length_counts, lengthCount_minLengthSq]
  exact shortRootCount_pos t

/-- Step `rBinvariants`: the least squared length determines the similarity factor. -/
theorem minLengthSq_eq_mul_of_similarity {m n : ℕ} {s : CartanMatrix.FiniteType m}
    {t : CartanMatrix.FiniteType n} {f : Space s ≃ₗ[ℝ] Space t} {a : ℝ}
    (hf : IsRootSet.IsSimilarity (roots s) (roots t) f a) :
    minLengthSq t = a * minLengthSq s := by
  obtain ⟨r, hr, hsr⟩ := exists_minLengthSq s
  obtain ⟨u, hu, htu⟩ := exists_minLengthSq t
  apply le_antisymm
  · have hfr : f r ∈ roots t := hf.image_eq ▸ Set.mem_image_of_mem f hr
    have h := minLengthSq_le t hfr
    rwa [hf.inner_map, hsr] at h
  · obtain ⟨x, hx, he⟩ := hf.image_eq ▸ hu
    have h := mul_le_mul_of_nonneg_left (minLengthSq_le s hx) hf.factor_pos.le
    rwa [← hf.inner_map, he, htu] at h

/-- Step `rBinvariants`: similarities preserve the number of shortest roots. -/
theorem shortRootCount_eq_of_similarity {m n : ℕ} {s : CartanMatrix.FiniteType m}
    {t : CartanMatrix.FiniteType n} {f : Space s ≃ₗ[ℝ] Space t} {a : ℝ}
    (hf : IsRootSet.IsSimilarity (roots s) (roots t) f a) :
    shortRootCount s = shortRootCount t := by
  have h := hf.length_ncard_eq (minLengthSq s)
  rw [← minLengthSq_eq_mul_of_similarity hf, length_counts, length_counts,
    lengthCount_minLengthSq, lengthCount_minLengthSq] at h
  exact h

/-- The uniqueness assertion of Theorem B of the blueprint for Remark 3.11 of [CGSS]: at a fixed
rank, the total and
shortest-root counts distinguish the canonical types, in place of steps `rBonevsTwo`--`rBBCunique`.
This proof does not need the number of lengths or their ratio. -/
theorem type_eq_of_counts {n : ℕ} (s t : CartanMatrix.FiniteType n)
    (hc : rootCount s = rootCount t) (hs : shortRootCount s = shortRootCount t) : s = t := by
  have hn := s.rank_pos
  have hn₁ : n - 1 + 1 = n := Nat.sub_add_cancel hn
  cases s <;> cases t <;> simp only [rootCount, shortRootCount] at hc hs <;>
    simp only [reduceCtorEq] <;> nlinarith

/-- Step `rBunique`: similar coordinate models in the canonical list have the
same type and rank. No conjugacy theorem for arbitrary bases is used. -/
theorem type_eq_of_similarity {m n : ℕ} (s : CartanMatrix.FiniteType m)
    (t : CartanMatrix.FiniteType n) {f : Space s ≃ₗ[ℝ] Space t} {a : ℝ}
    (hf : IsRootSet.IsSimilarity (roots s) (roots t) f a) :
    (⟨m, s⟩ : (n : ℕ) × CartanMatrix.FiniteType n) = ⟨n, t⟩ := by
  have hn : m = n := by
    have he := f.finrank_eq
    rwa [finrank_space, finrank_space] at he
  subst n
  have hc : rootCount s = rootCount t := by
    simpa only [root_counts] using hf.ncard_eq
  exact congrArg (Sigma.mk m) (type_eq_of_counts s t hc (shortRootCount_eq_of_similarity hf))

end RootSetModel
