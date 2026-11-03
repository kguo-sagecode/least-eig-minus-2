/-
Copyright (c) 2026 Krystal Guo, University of Amsterdam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
import LineGraphs.LineSystem.Models

/-!
# The diagonals of the cuboctahedron form `A₃`

[CGSS], J. Algebra 43 (1976), the remark after Definition 3.1 (p. 311):
"`A₃` is represented by the 6 diagonals of the cubeoctahedron [4]". The first half of that
sentence, `A_n ⊂ D_{n+1}`, is `LineSystem.An_Φ_subset_Dn` (`LineGraphs/LineSystem/Models.lean`).

The cuboctahedron is defined in the standard way: its vertices are the midpoints of the edges of
the cube with vertices `(±1, ±1, ±1)`, where two vertices of the cube span an edge when they
differ in exactly one coordinate. The cube has twelve edges, with distinct midpoints, and the
midpoints are the twelve vectors with one coordinate `0` and two coordinates `±1`. Each has squared
norm 2, and the vertex opposite to `v` is `-v`, so a diagonal, the line through two opposite
vertices `v` and `-v`, carries exactly the two vectors `v` and `-v` of the vertex set. Thus the
twelve vertices, taken as the vector set `Φ`, form a line system whose lines are the six diagonals,
and it is isomorphic to the model `LineSystem.An 3` of Definition 3.1, in the sense of
`LineSystem.Iso`. Its vector set is that of `LineSystem.Dn 3`; the isomorphism with `An 3` is
checked on the integer roots, by the kernel.

## Main definitions

* `LineSystem.cubeVertices`: the eight vertices `(±1, ±1, ±1)` of the cube.
* `LineSystem.IsCubeEdge u v`: the vertices `u` and `v` of the cube span an edge.
* `LineSystem.cubeEdges`: the edges of the cube, as unordered pairs of vertices.
* `LineSystem.cuboctahedronVertices`: the midpoints of the edges of the cube.
* `LineSystem.cuboctahedron`: the line system of the diagonals of the cuboctahedron, with the
  twelve vertices as its vector set `Φ`.
* `LineSystem.cuboctahedronDiagonals`: the diagonals, the lines through opposite vertices.
* `LineSystem.cuboctahedron.isoAn`: an isomorphism of `cuboctahedron` with `An 3`.

## Main statements

* `LineSystem.cuboctahedronVertices_eq`: the midpoints are the vectors with one coordinate `0`
  and two coordinates `±1`.
* `LineSystem.ncard_cuboctahedronVertices`: there are twelve of them.
* `LineSystem.ncard_cubeEdges`, `LineSystem.IsCubeEdge.sym2_eq_of_midpoint_eq`: the cube has
  twelve edges, with distinct midpoints.
* `LineSystem.cuboctahedron_Φ_inter_span_singleton`: a diagonal carries exactly two vertices.
* `LineSystem.numLines_cuboctahedron`: the line system has six lines.
* `LineSystem.ncard_cuboctahedronDiagonals`: the cuboctahedron has six diagonals.
* `LineSystem.nonempty_iso_cuboctahedron_An`: the diagonals represent `A₃`.
* `LineSystem.cuboctahedron_eq_Dn`: the line system is `Dn 3`.
-/

open scoped RealInnerProductSpace

namespace LineSystem

/-! ### The cube and its edges -/

/-- For [CGSS], the remark after Definition 3.1. The eight vertices `(±1, ±1, ±1)` of the cube
`[-1, 1]³`. -/
def cubeVertices : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ i, x i = 1 ∨ x i = -1}

/-- For [CGSS], the remark after Definition 3.1. The vertices `u` and `v` of the cube `[-1, 1]³`
span an edge: they differ in exactly one coordinate. -/
def IsCubeEdge (u v : EuclideanSpace ℝ (Fin 3)) : Prop :=
  u ∈ cubeVertices ∧ v ∈ cubeVertices ∧ ∃! i, u i ≠ v i

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The vertices of the cuboctahedron: the midpoints of
the edges of the cube `[-1, 1]³`. -/
def cuboctahedronVertices : Set (EuclideanSpace ℝ (Fin 3)) :=
  {m | ∃ u v, IsCubeEdge u v ∧ midpoint ℝ u v = m}

/-- For [CGSS], the remark after Definition 3.1. The edges of the cube `[-1, 1]³`, as unordered
pairs of vertices. -/
def cubeEdges : Set (Sym2 (EuclideanSpace ℝ (Fin 3))) :=
  {e | ∃ u v, IsCubeEdge u v ∧ s(u, v) = e}

/-- The coordinates of a midpoint. -/
private theorem midpoint_apply_fin_three (u v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    midpoint ℝ u v i = (u i + v i) / 2 := by
  rw [midpoint_eq_smul_add]
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, invOf_eq_inv]
  ring

/-- The vertices of an edge of the cube agree outside the coordinate in which they differ. -/
private theorem IsCubeEdge.apply_eq {u v : EuclideanSpace ℝ (Fin 3)} (h : IsCubeEdge u v)
    {i : Fin 3} (hi : u i ≠ v i) {j : Fin 3} (hj : j ≠ i) : u j = v j := by
  obtain ⟨-, -, k, -, huniq⟩ := h
  by_contra hne
  exact hj ((huniq j hne).trans (huniq i hi).symm)

/-- The vertices of an edge of the cube are opposite in the coordinate in which they differ. -/
private theorem IsCubeEdge.add_apply_eq_zero {u v : EuclideanSpace ℝ (Fin 3)} (h : IsCubeEdge u v)
    {i : Fin 3} (hi : u i ≠ v i) : u i + v i = 0 := by
  rcases h.1 i with h1 | h1 <;> rcases h.2.1 i with h2 | h2
  all_goals first
    | exact absurd (h1.trans h2.symm) hi
    | linarith

/-- The midpoint of an edge of the cube is `0` exactly in the coordinate in which its vertices
differ, and `±1` in the other two. -/
private theorem IsCubeEdge.midpoint_apply {u v : EuclideanSpace ℝ (Fin 3)} (h : IsCubeEdge u v)
    {i : Fin 3} (hi : u i ≠ v i) (j : Fin 3) :
    (j = i → midpoint ℝ u v j = 0) ∧
      (j ≠ i → midpoint ℝ u v j = 1 ∨ midpoint ℝ u v j = -1) := by
  refine ⟨?_, fun hj ↦ ?_⟩
  · rintro rfl
    rw [midpoint_apply_fin_three, h.add_apply_eq_zero hi, zero_div]
  · rw [midpoint_apply_fin_three, h.apply_eq hi hj]
    rcases h.2.1 j with h2 | h2 <;> rw [h2] <;> norm_num

/-- An edge of the cube is `{m + eᵢ, m - eᵢ}`, for its midpoint `m` and the coordinate `i` in
which its vertices differ. -/
private theorem IsCubeEdge.sym2_eq {u v : EuclideanSpace ℝ (Fin 3)} (h : IsCubeEdge u v)
    {i : Fin 3} (hi : u i ≠ v i) :
    s(u, v) = s(midpoint ℝ u v + EuclideanSpace.single i 1,
      midpoint ℝ u v + EuclideanSpace.single i (-1)) := by
  have hsum := h.add_apply_eq_zero hi
  have key (w : EuclideanSpace ℝ (Fin 3)) (hw : w = u ∨ w = v) (c : ℝ) (hc : w i = c) :
      w = midpoint ℝ u v + EuclideanSpace.single i c := by
    ext j
    rw [PiLp.add_apply, midpoint_apply_fin_three, PiLp.single_apply]
    by_cases hj : j = i
    · subst hj
      rw [ite_eq_left rfl, hsum, ← hc]
      ring
    · have hwj : w j = v j := by
        rcases hw with rfl | rfl
        exacts [h.apply_eq hi hj, rfl]
      rw [ite_eq_right hj, hwj, h.apply_eq hi hj]
      ring
  rcases h.1 i with h1 | h1
  · have h2 : v i = -1 := by linarith
    rw [← key u (Or.inl rfl) 1 h1, ← key v (Or.inr rfl) (-1) h2]
  · have h2 : v i = 1 := by linarith
    rw [Sym2.eq_swap, ← key u (Or.inl rfl) (-1) h1, ← key v (Or.inr rfl) 1 h2]

/-- For [CGSS], the remark after Definition 3.1. Distinct edges of the cube have distinct
midpoints. -/
theorem IsCubeEdge.sym2_eq_of_midpoint_eq {u v u' v' : EuclideanSpace ℝ (Fin 3)}
    (h : IsCubeEdge u v) (h' : IsCubeEdge u' v') (hm : midpoint ℝ u v = midpoint ℝ u' v') :
    s(u, v) = s(u', v') := by
  obtain ⟨i, hi, -⟩ := h.2.2
  obtain ⟨i', hi', -⟩ := h'.2.2
  have hii' : i' = i := by
    by_contra hne
    have h0 : midpoint ℝ u v i' = 0 := by
      rw [hm]
      exact (h'.midpoint_apply hi' i').1 rfl
    rcases (h.midpoint_apply hi i').2 hne with h1 | h1 <;> rw [h1] at h0 <;> norm_num at h0
  subst hii'
  rw [h.sym2_eq hi, h'.sym2_eq hi', hm]

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The vertices of the cuboctahedron, the midpoints of
the edges of the cube `[-1, 1]³`, are the vectors with one coordinate `0` and the other two
coordinates `±1`. -/
theorem cuboctahedronVertices_eq : cuboctahedronVertices =
    {x | ∃ i, x i = 0 ∧ ∀ j, j ≠ i → x j = 1 ∨ x j = -1} := by
  ext m
  simp only [cuboctahedronVertices, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, v, huv, rfl⟩
    obtain ⟨i, hi, -⟩ := huv.2.2
    exact ⟨i, (huv.midpoint_apply hi i).1 rfl, fun j hj ↦ (huv.midpoint_apply hi j).2 hj⟩
  · rintro ⟨i, hi, hj⟩
    have hvert (c : ℝ) (hc : c = 1 ∨ c = -1) :
        m + EuclideanSpace.single i c ∈ cubeVertices := by
      intro j
      by_cases hji : j = i
      · subst hji
        simpa [hi] using hc
      · simpa [hji] using hj j hji
    refine ⟨m + EuclideanSpace.single i 1, m + EuclideanSpace.single i (-1),
      ⟨hvert 1 (Or.inl rfl), hvert (-1) (Or.inr rfl), i, ?_, ?_⟩, ?_⟩
    · norm_num [hi]
    · intro j hne
      by_contra hji
      simp [hji] at hne
    · ext j
      rw [midpoint_apply_fin_three]
      by_cases hji : j = i
      · subst hji
        simp [hi]
      · simp [hji]

/-! ### The vertices as the roots of `D₃` -/

/-- Every root of `D₃` has one coordinate `0` and two coordinates `±1`. -/
private theorem dnRoot_three_shape : ∀ p : DnIndex 3,
    ∃ i, dnRoot p i = 0 ∧ ∀ j, j ≠ i → dnRoot p j = 1 ∨ dnRoot p j = -1 := by
  decide +kernel

/-- Every vector with one coordinate `0` and two coordinates `±1` is a root of `D₃`. -/
private theorem exists_dnRoot_three : ∀ (i : Fin 3) (s : Fin 3 → Bool),
    ∃ p : DnIndex 3, dnRoot p = fun j ↦ if j = i then 0 else rootSign (s j) := by
  decide +kernel

/-- For [CGSS], the remark after Definition 3.1. The vertices of the cuboctahedron are the roots
`±eᵢ ± eⱼ` of the model `Dn 3`. -/
theorem cuboctahedronVertices_eq_Dn : cuboctahedronVertices = (Dn 3).Φ := by
  rw [cuboctahedronVertices_eq]
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, hj⟩
    classical
    obtain ⟨p, hp⟩ := exists_dnRoot_three i (fun j ↦ decide (x j = -1))
    refine ⟨p, ?_⟩
    ext j
    simp only [integerVector_apply, hp]
    by_cases hji : j = i
    · subst hji
      simp [hi]
    · rcases hj j hji with h | h <;> norm_num [hji, h, rootSign]
  · rintro ⟨p, rfl⟩
    obtain ⟨i, hi, hj⟩ := dnRoot_three_shape p
    refine ⟨i, by simp [hi], fun j hji ↦ ?_⟩
    rcases hj j hji with h | h <;> simp [h]

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The cuboctahedron has twelve vertices. -/
theorem ncard_cuboctahedronVertices : cuboctahedronVertices.ncard = 12 := by
  rw [cuboctahedronVertices_eq_Dn]
  change (Set.range (integerVector 1 ∘ dnRoot)).ncard = 12
  rw [Set.ncard_range_of_injective
      ((integerVector_injective one_ne_zero).comp dnRoot_injective),
    Nat.card_eq_fintype_card, card_DnIndex]
  rfl

/-- For [CGSS], the remark after Definition 3.1. The cube `[-1, 1]³` has twelve edges. Their
midpoints are distinct (`IsCubeEdge.sym2_eq_of_midpoint_eq`), and they are the twelve vertices of
the cuboctahedron. -/
theorem ncard_cubeEdges : cubeEdges.ncard = 12 := by
  let f : Sym2 (EuclideanSpace ℝ (Fin 3)) → EuclideanSpace ℝ (Fin 3) :=
    Sym2.lift ⟨fun u v ↦ midpoint ℝ u v, fun u v ↦ midpoint_comm u v⟩
  have himage : f '' cubeEdges = cuboctahedronVertices := by
    ext m
    constructor
    · rintro ⟨_, ⟨u, v, huv, rfl⟩, rfl⟩
      exact ⟨u, v, huv, rfl⟩
    · rintro ⟨u, v, huv, rfl⟩
      exact ⟨s(u, v), ⟨u, v, huv, rfl⟩, rfl⟩
  have hinj : Set.InjOn f cubeEdges := by
    rintro _ ⟨u, v, huv, rfl⟩ _ ⟨u', v', huv', rfl⟩ hm
    exact huv.sym2_eq_of_midpoint_eq huv' hm
  rw [← ncard_cuboctahedronVertices, ← himage, hinj.ncard_image]

/-! ### The line system of the diagonals -/

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The six diagonals of the cuboctahedron, as a line
system: its vector set `Φ` is the set of the twelve vertices. Opposite vertices are `v` and `-v`,
and the diagonal through them carries exactly these two vectors of `Φ`
(`cuboctahedron_Φ_inter_span_singleton`). -/
def cuboctahedron : LineSystem (EuclideanSpace ℝ (Fin 3)) where
  Φ := cuboctahedronVertices
  finite := by
    rw [cuboctahedronVertices_eq_Dn]
    exact (Dn 3).finite
  inner_self := by
    rw [cuboctahedronVertices_eq_Dn]
    exact (Dn 3).inner_self
  neg_mem := by
    rw [cuboctahedronVertices_eq_Dn]
    exact (Dn 3).neg_mem
  inner_mem := by
    rw [cuboctahedronVertices_eq_Dn]
    exact (Dn 3).inner_mem

/-- For [CGSS], the remark after Definition 3.1. The vector set of `cuboctahedron` is the set of
vertices of the cuboctahedron. -/
@[simp] theorem cuboctahedron_Φ : cuboctahedron.Φ = cuboctahedronVertices := rfl

section Lines

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In a line system, the line `ℝ ∙ v` through a vector `v` of `Φ` carries exactly the two vectors
`v` and `-v` of `Φ`. -/
private theorem Φ_inter_span_singleton_of_mem (S : LineSystem V) {v : V} (hv : v ∈ S.Φ) :
    S.Φ ∩ (ℝ ∙ v : Submodule ℝ V) = {v, -v} := by
  ext w
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Submodule.mem_span_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, a, rfl⟩
    have h1 := S.inner_self _ hw
    rw [real_inner_smul_left, real_inner_smul_right, S.inner_self _ hv] at h1
    have h2 : (a - 1) * (a + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · left
      rw [show a = 1 by linarith, one_smul]
    · right
      rw [show a = -1 by linarith, neg_one_smul]
  · rintro (rfl | rfl)
    · exact ⟨hv, 1, one_smul _ _⟩
    · exact ⟨S.neg_mem _ hv, -1, neg_one_smul _ _⟩

/-- In a line system, the lines `ℝ ∙ v` spanned by the vectors `v` of `Φ` number `numLines`: each
of them carries exactly two vectors of `Φ`. -/
private theorem ncard_span_singleton_eq_numLines (S : LineSystem V) :
    {L : Submodule ℝ V | ∃ v ∈ S.Φ, L = ℝ ∙ v}.ncard = S.numLines := by
  classical
  set s := S.finite.toFinset
  have hD : {L : Submodule ℝ V | ∃ v ∈ S.Φ, L = ℝ ∙ v} = ↑(s.image fun v ↦ ℝ ∙ v) := by
    ext L
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, s,
      Set.Finite.mem_toFinset]
    exact ⟨fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.symm⟩, fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.symm⟩⟩
  have hfib : ∀ L ∈ s.image (fun v ↦ ℝ ∙ v), (s.filter fun w ↦ ℝ ∙ w = L).card = 2 := by
    intro L hL
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hL
    have hv' : v ∈ S.Φ := S.finite.mem_toFinset.mp hv
    have hfilter : (s.filter fun w ↦ ℝ ∙ w = ℝ ∙ v) = {v, -v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, s,
        Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨hw, hwv⟩
        have hw' : w ∈ S.Φ ∩ (ℝ ∙ v : Submodule ℝ V) :=
          ⟨hw, hwv ▸ Submodule.mem_span_singleton_self w⟩
        rw [Φ_inter_span_singleton_of_mem S hv'] at hw'
        simpa using hw'
      · rintro (rfl | rfl)
        · exact ⟨hv', rfl⟩
        · exact ⟨S.neg_mem _ hv', by rw [← Set.neg_singleton, Submodule.span_neg]⟩
    rw [hfilter, Finset.card_pair]
    intro h
    have h1 : ⟪v, v⟫ = ⟪v, -v⟫ := congrArg (⟪v, ·⟫) h
    rw [inner_neg_right, S.inner_self _ hv'] at h1
    norm_num at h1
  rw [hD, Set.ncard_coe_finset, numLines, Set.ncard_eq_toFinset_card S.Φ S.finite,
    Finset.card_eq_sum_card_image (fun v ↦ ℝ ∙ v) s, Finset.sum_congr rfl hfib,
    Finset.sum_const, smul_eq_mul, Nat.mul_div_cancel _ two_pos]

end Lines

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The diagonal of the cuboctahedron through the
opposite vertices `v` and `-v`, the line `ℝ ∙ v`, carries no other vertex: its vectors in `Φ` are
`v` and `-v`. -/
theorem cuboctahedron_Φ_inter_span_singleton {v : EuclideanSpace ℝ (Fin 3)}
    (hv : v ∈ cuboctahedron.Φ) :
    cuboctahedron.Φ ∩ (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) = {v, -v} :=
  Φ_inter_span_singleton_of_mem cuboctahedron hv

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The diagonals of the cuboctahedron: the lines through
two opposite vertices `v` and `-v` (the negative of a vertex is a vertex, by
`cuboctahedron.neg_mem`). Such a line passes through the centre `0`, so it is the line `ℝ ∙ v`
spanned by `v`. -/
def cuboctahedronDiagonals : Set (Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {L | ∃ v ∈ cuboctahedronVertices, L = ℝ ∙ v}

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The line system of the diagonals of the cuboctahedron
has six lines. -/
theorem numLines_cuboctahedron : cuboctahedron.numLines = 6 := by
  rw [numLines, cuboctahedron_Φ, ncard_cuboctahedronVertices]

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. The cuboctahedron has six diagonals, and they are the
lines of `cuboctahedron`. -/
theorem ncard_cuboctahedronDiagonals : cuboctahedronDiagonals.ncard = 6 := by
  rw [← numLines_cuboctahedron]
  exact ncard_span_singleton_eq_numLines cuboctahedron

/-- For [CGSS], the remark after Definition 3.1. The line system of the diagonals of the
cuboctahedron is the model `Dn 3`: they have the same vector set. -/
theorem cuboctahedron_eq_Dn : cuboctahedron = Dn 3 := by
  have h : cuboctahedron.Φ = (Dn 3).Φ := cuboctahedronVertices_eq_Dn
  generalize Dn 3 = T at h
  cases T
  subst h
  rfl

/-! ### The isomorphism with `A₃` -/

/-- For [CGSS], the remark after Definition 3.1. The integer presentation of `cuboctahedron` by
the roots `±eᵢ ± eⱼ` of `Dn 3`. -/
noncomputable instance cuboctahedron.integerModel : IntegerModel cuboctahedron where
  ι := DnIndex 3
  fintype := inferInstance
  v := dnRoot
  q := 1
  c := 1
  hc := by norm_num
  inj := dnRoot_injective
  Φ_eq := cuboctahedronVertices_eq_Dn

/-- The correspondence of root indices behind the isomorphism of `Dn 3` with `An 3`. It comes
from the isometry of `ℝ³` onto the hyperplane `x₀ + x₁ + x₂ + x₃ = 0` of `ℝ⁴` that maps `eᵢ` to
`½(e₀ + eᵢ₊₁ − eₖ₊₁ − eₗ₊₁)`, where `{i, k, l} = {0, 1, 2}`. It maps `eᵢ − eⱼ` to
`eᵢ₊₁ − eⱼ₊₁`, and `eᵢ + eⱼ` to `e₀ − eₖ₊₁`, where `k` is the third coordinate; in `Fin 3`,
`k = -(i + j)`. -/
private def dnThreeToAn : DnIndex 3 → AnIndex 3
  | (⟨(i, j), h⟩, false, true) => ⟨(i.succ, j.succ), by simpa using h.ne⟩
  | (⟨(i, j), h⟩, true, false) => ⟨(j.succ, i.succ), by simpa using h.ne'⟩
  | (⟨(i, j), _⟩, false, false) => ⟨(0, (-(i + j)).succ), (Fin.succ_ne_zero (-(i + j))).symm⟩
  | (⟨(i, j), _⟩, true, true) => ⟨((-(i + j)).succ, 0), Fin.succ_ne_zero (-(i + j))⟩

/-- The correspondence of root indices is a bijection. -/
private theorem dnThreeToAn_bijective : Function.Bijective dnThreeToAn := by
  decide +kernel

/-- The correspondence of root indices preserves the integer inner products. -/
private theorem integerInner_dnThreeToAn : ∀ a b : DnIndex 3,
    1 * integerInner (dnRoot a) (dnRoot b) =
      1 * integerInner (anRoot (dnThreeToAn a)) (anRoot (dnThreeToAn b)) := by
  decide +kernel

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. An isomorphism of the line system of the diagonals
of the cuboctahedron with the model `An 3` of `A₃`. -/
noncomputable def cuboctahedron.isoAn : cuboctahedron.Iso (An 3) :=
  Iso.ofIntegerModels cuboctahedron.integerModel (An.integerModel 3)
    (Equiv.ofBijective dnThreeToAn dnThreeToAn_bijective) integerInner_dnThreeToAn

-- [CGSS], the remark after Definition 3.1
/-- [CGSS], the remark after Definition 3.1. `A₃` is represented by the six diagonals of the
cuboctahedron: their line system is isomorphic to the model `An 3`. -/
theorem nonempty_iso_cuboctahedron_An : Nonempty (cuboctahedron.Iso (An 3)) :=
  ⟨cuboctahedron.isoAn⟩

end LineSystem
