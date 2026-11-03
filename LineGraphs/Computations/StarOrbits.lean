/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.Computations.StarCertificates
import LineGraphs.LineSystem.Reflections

/-!
# Transitivity on ordered stars from reflection trees

A reflection tree is a finite certificate that the reflections in roots act transitively on a set
of roots: every root other than the base has a parent of smaller depth, and a root whose
reflection maps the parent to it. Two such trees, one over all roots and one over the roots at
product `-1` with a base root `a₀` whose reflections fix `a₀`, show that the isometries preserving
`Φ` act transitively on the ordered stars. This is the route of LN5 in `cgss/prerequisites.md`,
with the chains of non-orthogonal roots replaced by checked trees.
-/

open scoped RealInnerProductSpace
open Computations

namespace Computations

/-- The entry at position `i` of a certificate list, as an index below `n`. -/
def listFin (n : ℕ) [NeZero n] (l : List ℕ) (i : Fin n) : Fin n :=
  ⟨l[i.val]?.getD 0 % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

/-- The entry at position `i` of a certificate list of depths. -/
def listNat {n : ℕ} (l : List ℕ) (i : Fin n) : ℕ := l[i.val]?.getD 0

end Computations

namespace LineSystem.IntegerModel

variable {d : ℕ} {S : LineSystem (EuclideanSpace ℝ (Fin d))} (M : IntegerModel S)

/-- The integer form of a reflection: `q • vᵢ = q • vₚ - ⟨vᵣ, vₚ⟩ • vᵣ` says that the reflection
in root `r` maps root `p` to root `i`. -/
theorem rootReflection_eq (i p r : M.ι)
    (h : M.q • M.v i = M.q • M.v p - integerInner (M.v r) (M.v p) • M.v r) :
    rootReflection (integerVector M.c (M.v r)) (S.inner_self _ (M.root_mem r))
      (integerVector M.c (M.v p)) = integerVector M.c (M.v i) := by
  rw [rootReflection_apply, inner_integerVector]
  ext k
  have hk := congrFun h k
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hk
  have hk' : (M.q : ℝ) * M.v i k =
      M.q * M.v p k - (integerInner (M.v r) (M.v p) : ℝ) * M.v r k := by
    exact_mod_cast hk
  simp only [PiLp.sub_apply, PiLp.smul_apply, integerVector_apply, smul_eq_mul]
  apply mul_left_cancel₀ M.q_ne_zero
  linear_combination (-M.c) * hk' -
    (M.c * (integerInner (M.v r) (M.v p) : ℝ) * M.v r k) * M.hc

/-- A checked reflection tree over the roots satisfying `D`: every such root is the image of
the base `root` under an isometry preserving `Φ` that fixes `y`. -/
theorem exists_isometry_of_tree (hS : S.IsStarClosed) (y : EuclideanSpace ℝ (Fin d))
    (D : M.ι → Prop) (root : M.ι) (parent refl : M.ι → M.ι) (depth : M.ι → ℕ)
    (h : ∀ i, D i → i ≠ root → D (parent i) ∧ depth (parent i) < depth i ∧
      ⟪integerVector M.c (M.v (refl i)), y⟫ = 0 ∧
      M.q • M.v i = M.q • M.v (parent i) -
        integerInner (M.v (refl i)) (M.v (parent i)) • M.v (refl i))
    (i : M.ι) (hi : D i) :
    ∃ g ∈ S.isometryGroup, g y = y ∧
      g (integerVector M.c (M.v root)) = integerVector M.c (M.v i) := by
  induction hn : depth i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    by_cases hr : i = root
    · exact ⟨1, S.isometryGroup.one_mem, rfl, by rw [hr]; rfl⟩
    obtain ⟨hp, hd, hy, hv⟩ := h i hi hr
    obtain ⟨g, hg, hgy, hgr⟩ := ih _ (hn ▸ hd) (parent i) hp rfl
    refine ⟨rootReflection _ (S.inner_self _ (M.root_mem (refl i))) * g,
      S.isometryGroup.mul_mem (rootReflection_mem_isometryGroup hS (M.root_mem _)) hg, ?_, ?_⟩
    · change rootReflection _ (S.inner_self _ (M.root_mem (refl i))) (g y) = y
      rw [hgy, rootReflection_apply_of_inner_eq_zero _ _ hy]
    · change rootReflection _ (S.inner_self _ (M.root_mem (refl i))) (g _) = _
      rw [hgr, M.rootReflection_eq i (parent i) (refl i) hv]

/-- Two reflection trees give transitivity on ordered stars: one over all roots from `a₀`, and
one over the roots at product `-1` with `a₀`, from `b₀`, fixing `a₀`. -/
theorem exists_isometry_of_star (a₀ b₀ : M.ι)
    (h₁ : ∀ i, ∃ g ∈ S.isometryGroup,
      g (integerVector M.c (M.v a₀)) = integerVector M.c (M.v i))
    (h₂ : ∀ j, integerInner (M.v j) (M.v a₀) = -M.q → ∃ g ∈ S.isometryGroup,
      g (integerVector M.c (M.v a₀)) = integerVector M.c (M.v a₀) ∧
      g (integerVector M.c (M.v b₀)) = integerVector M.c (M.v j))
    {a b : EuclideanSpace ℝ (Fin d)} (ha : a ∈ S.Φ) (hb : b ∈ S.Φ) (hab : ⟪a, b⟫ = -1) :
    ∃ g ∈ S.isometryGroup,
      g (integerVector M.c (M.v a₀)) = a ∧ g (integerVector M.c (M.v b₀)) = b := by
  rw [M.Φ_eq] at ha
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨g₁, hg₁, hg₁a⟩ := h₁ i
  have hb' : g₁.symm b ∈ S.Φ := (S.isometryGroup.inv_mem hg₁ b).mpr hb
  rw [M.Φ_eq] at hb'
  obtain ⟨j, hj⟩ := hb'
  have hj' : integerVector M.c (M.v j) = g₁.symm b := hj
  have hja : integerInner (M.v j) (M.v a₀) = -M.q := by
    rw [← M.inner_eq_neg_one_iff, hj', ← g₁.symm_apply_apply (integerVector M.c (M.v a₀)),
      hg₁a, LinearIsometryEquiv.inner_map_map, real_inner_comm]
    exact hab
  obtain ⟨g₂, hg₂, hg₂a, hg₂b⟩ := h₂ j hja
  refine ⟨g₁ * g₂, S.isometryGroup.mul_mem hg₁ hg₂, ?_, ?_⟩
  · change g₁ (g₂ _) = _
    rw [hg₂a, hg₁a]
    rfl
  · change g₁ (g₂ _) = _
    rw [hg₂b, hj', LinearIsometryEquiv.apply_symm_apply]

end LineSystem.IntegerModel

namespace LineSystem.Hyp24

variable {d : ℕ}

/-- Every ordered star of a model is the image of a fixed one: the model form of the hypotheses
of `orthGraphIsoOfIsometry`. -/
theorem exists_isometry_of_S_eq {S : LineSystem (EuclideanSpace ℝ (Fin d))} (H₀ H : Hyp24 _)
    (h₀ : H₀.S = S) (hS : H.S = S)
    (htrans : ∀ a b, a ∈ S.Φ → b ∈ S.Φ → ⟪a, b⟫ = -1 →
      ∃ g ∈ S.isometryGroup, g H₀.a = a ∧ g H₀.b = b) :
    ∃ g : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x, g x ∈ H.S.Φ ↔ x ∈ H₀.S.Φ) ∧ g H₀.a = H.a ∧ g H₀.b = H.b := by
  obtain ⟨g, hg, ha, hb⟩ := htrans H.a H.b (hS ▸ H.a_mem) (hS ▸ H.b_mem) H.inner_a_b
  exact ⟨g, fun x => by rw [hS, h₀]; exact hg x, ha, hb⟩

end LineSystem.Hyp24
