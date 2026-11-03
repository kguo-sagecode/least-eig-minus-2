# Notation

This file is the dictionary from the notation of [CGSS] to the notation of the blueprint and to
Lean names. The blueprint and the Lean files follow it. The Lean names are settled, by the
rules of §10; the Mathlib names in §9 were checked in Mathlib at commit `082e2d37`
(4 September 2026), the version pinned in `lake-manifest.json`. Where the paper has an error that
affects notation, we point to `cgss/errata.md`. A sentence such as "the blueprint writes $\ell$
for the rank" states a convention of the blueprint.

## 1. Conventions

These are our usual conventions, stated once.

- **Graphs** are $X$, $Y$, $Z$, never $G$; the letters $G$, $H$ are kept for groups. The paper's
  graphs $G$, $G_1$, $G_2$ become $X$, $X_1$, $X_2$, and its auxiliary graph $H$ (Theorems 4.11,
  4.13, 5.8) becomes $Y$. Vertices are $u$, $v$, $w$, $x$, in that order of preference, and $n$ is
  the number of vertices. The complement of $X$ is $\overline{X}$, and $\Gamma_i(v)$ is the set of
  vertices at distance $i$ from $v$; thus $\Gamma_1(v)$ is the neighbourhood of $v$.
- **Matrices and vectors** are written in functional notation: the $uv$-entry of $M$ is $M(u,v)$,
  and the entry of $\mathbf x$ indexed by $u$ is $\mathbf x(u)$. Subscripts index families, as in
  $\theta_r$, $E_r$, $X_1$, $\mathbf x_u$ (the vector representing the vertex $u$), $\mathbf e_i$ (a
  basis vector). $A=A(X)$ is the adjacency matrix, $J$ the all-ones matrix, $\mathbf j$ the all-ones
  vector, and $I$ the identity.
- **Strongly regular graphs** have parameters $(n,k,a,c)$: $n$ vertices, valency $k$, $a$ common
  neighbours for adjacent vertices and $c$ for nonadjacent ones. The eigenvalues are
  $k>\theta_1>\theta_2$, with multiplicities $1$, $m_1$, $m_2$, and
  $A=kE_0+\theta_1E_1+\theta_2E_2$ with spectral idempotents $E_r$ and eigenspaces $V_r$. [BvM]
  and [BCN] write $(v,k,\lambda,\mu)$, $r>s$ and $f,g$; Mathlib writes
  `SimpleGraph.IsSRGWith n k ℓ μ`. A generic eigenvalue, with or without multiplicity, is
  $\lambda$; a regular graph has valency $k$.
- **Vectors are bold**, through the author's macros, at the start of each document: `\Zu`, `\Zv`, `\Zw`, `\Zx`, `\Zy`,
  `\Zz`, and `\Zj` for the all-ones vector. The paper also needs bold $\mathbf a$, $\mathbf b$,
  $\mathbf c$, $\mathbf e_i$, $\mathbf h$, $\mathbf p_i$, $\mathbf r$, $\mathbf s$, $\mathbf t$,
  which the author's macros do not have. `blueprint/macros.tex` defines `\Za`, `\Zb`, `\Zc`, `\Ze`,
  `\Zh`, `\Zp`, `\Zr`, `\Zs`, `\Zt` in the same style, as `{\mathbf a}` and so on, and `\Ga`,
  `\Gb`, `\Gc` for $\Gamma_a$, $\Gamma_b$, $\Gamma_c$. None of the author's macros is redefined.
- **Inner products** are written $(\mathbf x,\mathbf y)$, as in the paper and in
  `blueprint/sec2-lines.tex`. The author's macro `\ip` is not
  used, since angle brackets are taken by Lamport's step numbers $\langle1\rangle2$. For the same
  reason the paper's $\langle\mathbf x\rangle$, the line spanned by $\mathbf x$, becomes
  $\mathbb R\mathbf x$ (`\re\Zx`). In Lean, `⟪x, y⟫` under `open scoped RealInnerProductSpace`.
- **This file** is Markdown, so it writes standard LaTeX: $\mathbf x$ for
  `\Zx`, $\overline X$ for `\comp{X}`, $\mathbb R$ for `\re`, $\operatorname{Orth}$ for
  `\opk{Orth}`, $\setminus$ for `\diff`. The blueprint writes the macros.
- **Dynkin types are upright** (`\typ{A}_\ell`, as in `cgss/proofs/remark311/remark311.tex`):
  $\mathrm A_\ell$, $\mathrm D_\ell$, $\mathrm E_6$, $\mathrm E_7$, $\mathrm E_8$, and for two root
  lengths $\mathrm B_\ell$, $\mathrm C_\ell$, $\mathrm F_4$, $\mathrm G_2$. Italic $A$ and $C$ are
  then free for the adjacency matrix and for the matrix of Theorem 3.7 (§8). The rank is $\ell$,
  not $n$ (§8). Markdown files may keep the paper's italic $A_n$, $D_n$, $E_8$ where no confusion
  can arise.
- **Section 5** keeps the usual design parameters $(v,k,b,r,\lambda)$, although
  they clash with our letters for vertices, valencies and eigenvalues (§8).
- **Standing assumptions of the paper.** Lines pass through the origin and span the ambient space
  (Section 2, first paragraph). The blueprint states the span explicitly: our ambient space is a
  finite-dimensional real inner product space $V$, and a set of lines need not span it.

## 2. Sets of lines (Section 2)

| [CGSS] | Meaning | Blueprint | Lean |
| --- | --- | --- | --- |
| set of lines at 60° and 90°, $S$ | finitely many lines through 0, pairwise at 60° or 90° | $S$, recorded by $\Phi=\Phi(S)$ | `LineSystem V` |
| (not named) | the vectors of squared norm 2 on the lines of $S$, both signs | $\Phi$ | field `S.Φ` |
| $\langle\mathbf x\rangle$ | the line spanned by $\mathbf x$ | $\mathbb R\mathbf x$ | `ℝ ∙ x` (`Submodule.span ℝ {x}`), rarely needed |
| star | three lines in a plane, pairwise at 60° | star; with vectors $\mathbf r$, $\mathbf s$, $-(\mathbf r+\mathbf s)$ where $(\mathbf r,\mathbf s)=-1$ | no predicate of its own: the vectors `H.a`, `H.b`, `H.c` of a `LineSystem.Hyp24`, and in `LineSystem.IsStarClosed` two vectors with inner product $-1$ |
| triangle | three lines, pairwise at 90° | triangle (of the orthogonality graph, §4) | none |
| star-closed (Def. 2.1) | with two lines of a star, contains the third | star-closed | `LineSystem.IsStarClosed` |
| maximal (Def. 2.2) | contains every line of its span at 60° or 90° to all its lines | maximal (within the span of $\Phi$; errata, Implicit hypothesis 7) | `LineSystem.IsMaximal` |
| indecomposable | not the union of two sets in proper orthogonal subspaces | indecomposable; the empty set is excluded where it matters (errata, Implicit hypothesis 4) | `LineSystem.IsIndecomposable` |
| unique up to orthogonal transformations | isomorphic | isomorphic, $S\cong T$ | `LineSystem.Iso`; an isomorphism extends to a linear isometry of the spans (LA2, LN4) |
| switching class of sets of vectors | the sets of one vector per line, up to changing signs | a *signing* of $S$: a choice of one of $\pm\mathbf r$ on each line; the switching class is the set of all signings | `LineSystem.Signing` (a section of $\Phi\to$ lines) |
| star closure (Section 3, before Theorem 3.8) | smallest star-closed set containing given lines | the star closure $\operatorname{sc}(\Sigma)$ (LN3) | `LineSystem.starClosure` |

The blueprint writes the star closure as $\operatorname{sc}(\Sigma)$ rather than with a bar, since a bar
denotes a complement; LN3 of `cgss/prerequisites.md` gives its properties.

**Hypothesis 2.4 and the sets of Section 2.** The paper's names are kept for the paper's own
objects.

| [CGSS] | Meaning | Blueprint | Lean |
| --- | --- | --- | --- |
| Hypothesis 2.4 | $S$ indecomposable and star-closed, with $\mathbf a,\mathbf b$ on lines of $S$ and $(\mathbf a,\mathbf b)=-1$ | Hypothesis 2.4, with the vectors $\mathbf a$, $\mathbf b$ fixed | structure `LineSystem.Hyp24` carrying `a`, `b` and the hypotheses (`blueprint/sec2-lines.tex`) |
| $c=-a-b$ | the third vector of the star | $\mathbf c$ | `H.c` |
| $\Gamma_a$, $\Gamma_b$, $\Gamma_c$ | vectors on lines of $S$ with prescribed inner products with $\mathbf a$, $\mathbf b$, $\mathbf c$ | $\Gamma_a$, $\Gamma_b$, $\Gamma_c$ | `H.Γa`, `H.Γb`, `H.Γc` |
| $\Delta$ | vectors on lines of $S$ orthogonal to $\mathbf a$, $\mathbf b$, $\mathbf c$; closed under negation | $\Delta$ (a set of vectors; Theorem 2.13 counts its lines, errata Error 6) | `H.Δ` |
| $\Sigma$ | $\{\mathbf a,\mathbf b,\mathbf c\}\cup\Gamma_a\cup\Gamma_b\cup\Gamma_c\cup\Delta$ | $\Sigma$ (only this set; §8) | `H.sigmaSet`: `Σ` is a token of Lean core (Sigma types) and cannot be an identifier |
| $\varphi_a,\varphi_b,\varphi_c$ (Lemma 2.6) | $\mathbf x\mapsto\mathbf x+\mathbf a$ and so on | $\varphi_a$, $\varphi_b$, $\varphi_c$ | `H.ΓaEquivΓb`, `H.ΓbEquivΓc`, `H.ΓcEquivΓa` |
| $z=b-c-x-y$ (Lemma 2.8), $f(x,y)$ (Lemma 2.10) | the third vertex of the triangle on an edge $\{\mathbf x,\mathbf y\}$ | $f(\mathbf x,\mathbf y)=\mathbf b-\mathbf c-\mathbf x-\mathbf y$ | `H.third x y` |
| $u$, $v$ (Lemma 2.10) | a nonadjacent pair in $\Gamma_a$ | $u$, $v$ as vertices, $\mathbf u$, $\mathbf v$ as vectors | `u v : H.Γa` |
| $K$, $L$, $M$, $N$ (Lemma 2.10) | the vertices adjacent to both, to $\mathbf u$ only, to $\mathbf v$ only, to neither | $K$, $L$, $M$, $N$ | no names of their own: Lemma 2.10 is proved for a graph $X$ with the triangle property, and `K`, `L`, `M`, `N` are the local notation of `SimpleGraph.HasTriangleProperty.NormalForm` for `X.commonNeighbors u v`, `X.neighborSet u \ X.neighborSet v`, `X.neighborSet v \ X.neighborSet u` and `Xᶜ.commonNeighbors u v` |
| $x'=f(x,u)$, $x''=f(x,v)$ | the partners of $x\in K$ in $L$ and $M$ | $x'$, $x''$ | `H.third x u`, `H.third x v` |
| $k$ (Lemma 2.10) | $\lvert K\rvert=\lvert L\rvert=\lvert M\rvert$ | $k$, kept (§8: the graph is then strongly regular with parameters $(6k-3,2k,1,k)$) | `k` |
| $n\in N$ (Lemma 2.10) | a vertex of $N$ | $w\in N$ | `w` |
| (errata, Gap 1) | $\lvert\Gamma_1(w)\cap K\rvert$ | $d_K(w)$ | no name: `(X.commonNeighbors u v ∩ X.neighborSet w).ncard`, in step 210dK (`SimpleGraph.HasTriangleProperty.ncard_commonNeighbors_inter_eq_or_add_two`) |

The blueprint uses the pairing of vertex and vector: a vertex of the orthogonality graph on
$\Gamma_a$ is written $x$, and the same element of $\Gamma_a$, as a vector, is written $\mathbf x$
(`\Zx`), as in `blueprint/sec2-lines.tex`.

## 3. Root systems (Section 3)

| [CGSS] | Meaning | Blueprint | Lean |
| --- | --- | --- | --- |
| $B^n=\{e_1,\dots,e_n\}$ | an orthonormal basis of $\mathbb R^n$ | the standard basis $\mathbf e_1,\dots,\mathbf e_\ell$ of $\mathbb R^\ell$ | `EuclideanSpace.single i 1`, or `EuclideanSpace.basisFun` |
| $T(n,m)$ | the $m$-subsets of an $n$-set | $\binom{[n]}{m}$ (§8: $T(m)$ is the triangular graph) | `Finset.powersetCard m Finset.univ` |
| $S(3,4,8)$ | the blocks of the 3-design $(8,4,14,7,3)$ | $S(3,4,8)$, with the labelling fixed in errata Gap 5 | `steiner348 : Finset (Finset (Fin 8))` |
| $A_n$ (Def. 3.1) | lines of $\mathbf e_i-\mathbf e_j$ in $\mathbb R^{n+1}$ | $\mathrm A_\ell$ | `LineSystem.An ℓ` |
| $D_n$, $n\ge4$ (Def. 3.1) | lines of $\pm\mathbf e_i\pm\mathbf e_j$ in $\mathbb R^n$ | $\mathrm D_\ell$ | `LineSystem.Dn ℓ` |
| $E_8$, model (i) (Def. 3.2) | $A_8$ and the lines of $\frac13\sum_{l=1}^9\mathbf e_l-(\mathbf e_h+\mathbf e_i+\mathbf e_j)$ | $\mathrm E_8$, model (i) | `LineSystem.E₈viaA₈` (coordinates tripled) |
| $E_8$, the second "(i)" (Def. 3.2; errata Error 6) | $D_8$ and the lines of $\frac12\sum\epsilon_i\mathbf e_i$, $\prod\epsilon_i=1$ | $\mathrm E_8$, model (ii); the default model, as in Section 4 | `LineSystem.E₈viaD₈` (coordinates doubled); `LineSystem.E₈ := E₈viaD₈` |
| $E_8$, model (iii) (Def. 3.2) | the lines of $2\mathbf e_i$ and of $\pm\mathbf e_h\pm\mathbf e_i\pm\mathbf e_j\pm\mathbf e_k$, $\{h,i,j,k\}\in S(3,4,8)$ | $\mathrm E_8$, model (iii) | `LineSystem.E₈viaSteiner` (integral) |
| $E_7$, $E_6$ (Def. 3.3) | lines of $E_8$ orthogonal to a line, to a star | $\mathrm E_7$, $\mathrm E_6$; in model (ii), $\mathrm E_7=\mathrm E_8\cap(\mathbf e_7-\mathbf e_8)^\perp$ and $\mathrm E_6=\mathrm E_7\cap(\mathbf e_6-\mathbf e_7)^\perp$ (LN6) | `LineSystem.E₇`, `LineSystem.E₆`; `S.orthogonalTo v` for the subsystem |
| $2I+C$ | Gram matrix of a signing of a root system | $2I+C$ | `Matrix.gram ℝ σ` for a signing `σ` |
| $C$ (before Thm. 3.7) | zero diagonal, entries $0,\pm1$; determined up to switching | $C$ (italic; types are upright), the *signed adjacency matrix* of the signing | `LineSystem.signedAdj σ` |
| $C$ in Remark 3.11 | undefined in the paper for two root lengths | $C=2G-2I$, where $G$ is the Gram matrix of unit vectors on the lines (`remark311.tex`, Lemma "C-convention"; errata Error 11) | same definition, on unit vectors |
| $\gamma_1,\dots,\gamma_n$ (proof of Thm. 3.7) | the remaining eigenvalues of $C$ | $\lambda_1,\dots,\lambda_\ell$ | none |
| $(C+2I)(C-\theta I)=0$ | the matrix equation | $\theta$ = the second constant: $\ell-1$, $2(\ell-2)$, 10, 16, 28 (errata Error 1) | `LineSystem.signedAdj_quadratic` |
| Root System (Def. 3.9, capital R) | finite spanning set satisfying (a), (b), (c) | Root System, as in the paper; written $\Phi$, not $\Sigma$ (§8) | predicate `IsRootSet Φ`, with a bridge to `RootPairing` (§9) |
| $\tau_r$ (Def. 3.9) | the reflection in $\mathbf r^\perp$ | $\tau_{\mathbf r}$ | `IsRootSet.reflection`, or Mathlib's `RootPairing.reflection` |
| $A_n$, $D_n$, $E_6$, $E_7$, $E_8$ in Figure 1 | the connected graphs with largest eigenvalue 2 (the printed labels have no tildes) | the Smith graphs $\tilde{\mathrm A}_\ell$ (the cycle on $\ell+1$ vertices), $\tilde{\mathrm D}_\ell$, $\tilde{\mathrm E}_6$, $\tilde{\mathrm E}_7$, $\tilde{\mathrm E}_8$ | `SimpleGraph.smithA ℓ` (or `cycleGraph (ℓ+1)`), `smithD ℓ`, `smithE₆`, `smithE₇`, `smithE₈` |
| $B_n$, $C_n$, $F_4$, $G_2$ (Rem. 3.11) | Root Systems with two root lengths, as lines | $\mathrm B_\ell$, $\mathrm C_\ell$, $\mathrm F_4$, $\mathrm G_2$ | models of `remark311.tex`; Mathlib's `CartanMatrix.B`, `C`, `F₄`, `G₂` |
| (prerequisites §1) | $N_{\mathbf r}(\Phi)=\{\mathbf u\in\Phi:(\mathbf u,\mathbf r)=1\}$ | $N_{\mathbf r}(\Phi)$ | `LineSystem.N S r` |
| (prerequisites §1) | the pairs $\{\mathbf u,\mathbf r-\mathbf u\}$ of $N_{\mathbf r}(\Phi)$ | the *pairs* of $N_{\mathbf r}(\Phi)$ | the involution `LineSystem.pairInv S r : S.N r ≃ S.N r` |

## 4. The three graph conventions

The paper defines graphs on sets of vectors in three different ways, and says so only once ("with
1 for adjacency, so opposite to the convention used in Section 2", before Theorem 3.8). The
blueprint gives the three graphs different names. For a family $(\mathbf x_u)$ of vectors of squared
norm 2 indexed by a set $U$, and $t\in\{0,1,-1\}$:

| Convention | Adjacency | Blueprint | Lean | Used in |
| --- | --- | --- | --- | --- |
| Section 2 | $(\mathbf x_u,\mathbf x_w)=0$ (lines at 90°) | the *orthogonality graph*, $\operatorname{Orth}(\Gamma_a)$ | in general `SimpleGraph.innerGraph x 0`, which the library does not use; on $\Gamma_a$, `LineSystem.Hyp24.orthGraph`, defined directly by $(\mathbf x,\mathbf y)=0$ | Section 2 from Lemma 2.8 on ("Henceforth we adopt graph terminology"): Lemmas 2.8–2.12, Theorem 2.13, Remark 2.11; the proof of Theorem 3.6 (with errata Error 5) |
| Section 4 | $(\mathbf x_u,\mathbf x_w)=1$ (lines at 60°, vectors at 60°) | the graph *represented by* $(\mathbf x_u)$; $(\mathbf x_u)$ *represents* $X$ when its Gram matrix is $2I+A(X)$ | `SimpleGraph.representedGraph x := innerGraph x 1`; the predicate `X.IsRepresentation x` and `X.IsRepresentedIn S` | Section 4 (the opening paragraph, Theorems 4.1–4.14), Section 5 (case (i) of Theorem 5.8, Corollary 5.10), Section 6; the sets $N_{\mathbf r}(\Phi)$ |
| before Theorem 3.8 | $(\mathbf x_u,\mathbf x_w)=-1$ (vectors at 120°) | the *obtuse graph*, $\operatorname{Obt}(\mathbf x)$; $(\mathbf x_u)$ *obtusely represents* $X$ when its Gram matrix is $2I-A(X)$ | no definition: the hypothesis `Matrix.gram ℝ v = (2 : ℝ) • 1 - X.adjMatrix ℝ` of `SimpleGraph.smith_exists_gram`, `SimpleGraph.smith_gram_delete_basis` and `SimpleGraph.eigenvalue_le_two_of_gram_representation` | the paragraph before Theorem 3.8, Theorem 3.8 and Figure 1; the Dynkin diagram of a base of simple roots (Remark 3.11, `remark311.tex`) |

One Lean definition covers all three, `SimpleGraph.innerGraph (x : U → V) (t : ℝ)`, with
`Adj u w := u ≠ w ∧ ⟪x u, x w⟫ = t`; the library uses it for the Section 4 convention, and states
the other two as above. On a set with inner products in $\{0,1\}$, such as $\Gamma_a$
(Lemma 2.6), the orthogonality graph is the complement of the represented graph. For instance, for
$\mathrm E_7$ the orthogonality graph on $\Gamma_a$ is $\overline{T(6)}$, with parameters
$(15,6,1,3)$, while $T(6)$ is the represented graph (errata Error 5). Likewise the orthogonality
graphs on $\Gamma_a$ for $\mathrm E_6$ and $\mathrm E_8$ are $L_2(3)$ (which is self-complementary)
and the complement of the Schläfli graph.

## 5. Graphs (Sections 4 to 6)

| [CGSS] | Meaning | Blueprint | Lean or Mathlib |
| --- | --- | --- | --- |
| order of $G$ | number of vertices | $n$ | `Fintype.card U` |
| $L(G)$ | line graph | $L(X)$ | `SimpleGraph.lineGraph` (vertices `X.edgeSet`) |
| $K_n$, $K_{m,n}$ | complete, complete bipartite | $K_n$, $K_{m,n}$ | `completeGraph (Fin n)` ($=\top$), `completeBipartiteGraph (Fin m) (Fin n)` |
| $K_{1,n}$, 3-claw, 4-claw | star; induced $K_{1,3}$, $K_{1,4}$ | $K_{1,n}$; claw | `SimpleGraph.starGraph`; claws by an induced embedding of `starGraph` |
| $C_4$, $C_5$, hexagon | cycles | $C_m$ | `SimpleGraph.cycleGraph m` |
| void graph (Lemma 2.12) | no edges | the empty graph $\overline{K_m}$ | `⊥ : SimpleGraph U` |
| $n$ triangles meeting at one vertex (Lemmas 2.9, 2.12) | the friendship (windmill) graph | the friendship graph with $m$ triangles, on $2m+1$ vertices (no symbol: $F$ is the flag graph) | `SimpleGraph.friendship m` (not in Mathlib) |
| $CP(a)$ | cocktail party graph on $2a$ vertices; [BvM] $K_{a\times2}$, [S68] $H(a)$ | $CP(m)$ (§8: $a$ is a strongly regular parameter) | `SimpleGraph.cocktailParty m : SimpleGraph (Fin m × Bool)` (not in Mathlib) |
| $L(G;a_1,\dots,a_m)$ | Hoffman's generalized line graph: $L(Y)$ with $CP(a_i)$ attached at the vertex $i$ | $L(Y;a_1,\dots,a_m)$, the $a_i$ always indexed; the paper's $L(K_m;\mathbf a)$ becomes $L(K_m;a_1,\dots,a_m)$, since $\mathbf a$ is the vector of Hypothesis 2.4 | `SimpleGraph.generalizedLineGraph Y a`; `X.IsGeneralizedLineGraph` |
| $e_{i,0}$, $e_{i,\alpha}$ | the basis of the representation of $L(G;a_1,\dots,a_m)$ | $\mathbf e_{i,0}$, $\mathbf e_{i,j}$ with $1\le j\le a_i$ (errata Error 13, item 5) | a basis indexed by `Σ i, Fin (a i + 1)` |
| $L(K_{1,n};a,0,\dots,0)$ (Rem. 4.12) | $K_{n+2a}$ minus $a$ disjoint edges | $L(K_{1,s};t,0,\dots,0)$ | none |
| triangular graph $T(m)$ (words in [CGSS]) | $L(K_m)$ | $T(m)$ | `(completeGraph (Fin m)).lineGraph` |
| lattice graph on 9 vertices | $L(K_{3,3})$ | $L_2(m)=L(K_{m,m})$ | `(completeBipartiteGraph (Fin m) (Fin m)).lineGraph` |
| "represented by a subset of $E_8$" | some family in $\Phi(\mathrm E_8)$ represents $X$ | $X$ is *represented in* $\mathrm E_8$ | `X.IsRepresentedIn LineSystem.E₈` |
| strongly regular | | strongly regular with parameters $(n,k,a,c)$ | `SimpleGraph.IsSRGWith n k a c` (Mathlib's letters are `n k ℓ μ`) |
| $\operatorname{spec}(G)$ | the distinct eigenvalues with their multiplicities | $\operatorname{spec}(X)$, written $\theta_0^{m_0}\theta_1^{m_1}\cdots$ | `(X.adjMatrix ℝ).charpoly`; cospectral: `X.Cospectral Y` (not in Mathlib) |
| least eigenvalue $-2$ | read literally, $\lambda_{\min}(X)=-2$; we read it as the lower bound in Theorems 4.10 and 4.11, which makes them stronger, and literally in Theorem 4.13 and Remark 4.14 (errata Implicit hypothesis 2, a note on reading) | $\lambda_{\min}(X)\ge-2$, that is $2I+A\succeq0$; in Theorem 4.13, also $-2$ an eigenvalue | `((2 : ℝ) • (1 : Matrix U U ℝ) + X.adjMatrix ℝ).PosSemidef`; in `SimpleGraph.seidel` also `-2 ∈ X.spectrumMultiset`, and in `SimpleGraph.seidel_seven` `X.leastEigenvalue = -2`; the bridge lemmas `SimpleGraph.leastEigenvalue_eq_neg_two_iff` and `SimpleGraph.neg_two_mem_spectrumMultiset_iff_det_eq_zero` |
| switching (Section 4: "switched into $\frac12\sum e_k-e_i-e_j$") | replace $\mathbf x_u$ by $\mathbf h-\mathbf x_u$ for $u$ in a set, where $(\mathbf h,\mathbf x_u)=1$ | *switching by* $\mathbf h$ (SW4) | no definition: the family `fun u ↦ if u ∈ U then h - x u else x u` of `SimpleGraph.IsRepresentation.switch` (Lemma (switching by vectors), `lem:4-switch`) |
| Seidel switching | complement the pairs between $U$ and $V(X)\setminus U$ | $X^U$ for $U\subseteq V(X)$ (`cgss/prerequisites.md` SW1 writes $X^Y$, which the blueprint renames, since $Y$ is a graph) | `SimpleGraph.switch X U` (not in Mathlib) |
| $(\pm1)$ adjacency matrix $2A-J+I$ (Cor. 5.10) | minus the Seidel matrix | $-S(X)$, where $S(X)=J-I-2A$ | `SimpleGraph.seidelMatrix X` |
| switching equivalent | in the same switching class | switching equivalent | `X.IsSwitchingEquivalent Y`, through the Seidel matrices (`Matrix.IsSwitchingEquivalent`) |
| $M$ (Lemma 5.5) | vertex-edge incidence matrix | $M$, rows indexed by vertices | `SimpleGraph.incMatrix ℝ` (columns indexed by all of `Sym2 U`; restrict to edges) |
| $v$ (Lemmas 5.1, 5.3, 5.5) | the valency | $k$ | `IsRegularOfDegree k` |
| $p$, $q$, $v$, $w$ (Lemma 5.6) | block sizes $p\le q$ and their valencies | $p$, $q$, $k_1$, $k_2$ | none |
| $B_1$, $B_2$ (Lemma 5.6) | biadjacency matrices | $B_1$, $B_2$ | none |
| $\alpha$, $\gamma$, $\gamma'$, $\delta$, $\delta'$ (Rem. 5.7) | eigenvalues of $B_1B_1^T$, $C$, $A(G_2)$ | $\lambda$ for $\alpha$; $\gamma$, $\gamma'$, $\delta$, $\delta'$ kept (errata Error 13, item 8) | none |
| $d$ (Theorem 4.4) | the valency | $k$ | `IsRegularOfDegree k` |
| $\alpha$, $\alpha_i$ (Theorem 4.4) | eigenvalues of $A$ on $\mathbf j^\perp$ | $\lambda$, $\lambda_i$ | none |

## 6. Special graphs and their names

The names of these graphs vary between sources. The blueprint and Lean follow [CGSS], and each Lean
docstring records the parameters and, where needed, the invariants that fix the graph.

| [CGSS] | Parameters | Other names and clashes | Lean |
| --- | --- | --- | --- |
| Chang I (Ex. 4.5): switch $T(8)$ by $\{\mathbf e_i+\mathbf e_{4+i}\}$, the edges of $4K_2$ | $(28,12,6,4)$ | [S68] $T'(8)$; [BvM] Chang1 | `SimpleGraph.changI` |
| Chang II: switch by the edges of $C_8$ | $(28,12,6,4)$ | [S68] $T'''(8)$, which switches by the 12 edges of the Wagner graph and gives the same graph; [BvM] Chang3 | `SimpleGraph.changII` |
| Chang III: switch by the edges of $C_3+C_5$ | $(28,12,6,4)$ | [S68] $T''(8)$; [BvM] Chang2 | `SimpleGraph.changIII` |
| Schläfli graph (Ex. 4.6, errata Error 2) | $(27,16,10,8)$ | its complement, with parameters $(27,10,1,5)$, is the collinearity graph of the generalized quadrangle of order $(2,4)$, and is the orthogonality graph on $\Gamma_a$ of $\mathrm E_8$ (§4). The two are easily confused, so the blueprint always gives the parameters. SageMath's `graphs.SchlaefliGraph()` is the 16-regular one | `SimpleGraph.schlafli` (16-regular), the graph of the Example 4.6 vectors (C9); `SimpleGraph.gq24` is the combinatorial graph $Q$ of `cgss/proofs/clebsch/clebsch.tex` (the double six), and C9's certificate isomorphism `SimpleGraph.schlafli.gq24ComplIso : schlafli ≃g gq24ᶜ` links the two |
| Shrikhande graph (Ex. 4.7) | $(16,6,2,2)$ | [S68] $L_2'(4)$; cospectral with $L_2(4)$ | `SimpleGraph.shrikhande` |
| Clebsch graph (Ex. 4.8) | $(16,10,6,6)$, 10-regular | [BvM] §10.7 agrees (the halved 5-cube) and calls the 5-regular complement, with parameters $(16,5,0,2)$, the folded 5-cube. Many other authors, and SageMath's `graphs.ClebschGraph()`, give the name to the 5-regular graph. [BCN] 3.11 (iii) misprints the parameters of the complement as $(16,5,0,1)$ (prerequisites SE2) | `SimpleGraph.clebsch` (10-regular), the graph of the Example 4.8 vectors (C9); `SimpleGraph.foldedFiveCube` for the complement, the combinatorial graph of `cgss/proofs/clebsch/clebsch.tex` on the even subsets of `Fin 5` with $\lvert s\triangle t\rvert=4$, and C9's certificate isomorphism `SimpleGraph.clebsch.foldedFiveCubeComplIso : clebsch ≃g foldedFiveCubeᶜ` links the two |
| Petersen graph (Ex. 4.9) | $(10,3,0,1)$ | $\overline{T(5)}$, the Kneser graph $K(5,2)$ | `SimpleGraph.petersen` |
| the graphs of Lemma 2.10 | $(9,4,1,2)$, $(15,6,1,3)$, $(27,10,1,5)$ | collinearity graphs of the generalized quadrangles of orders $(2,1)$, $(2,2)$, $(2,4)$, that is $L_2(3)$, $\overline{T(6)}$ and the complement of the Schläfli graph; [CGSS] calls them "the unique strongly regular graphs on 9, 15, 27 vertices" (errata Error 12) | no names for the first two, which are `(completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph` and `(completeGraph (Fin 6)).lineGraphᶜ` (C4: `LineSystem.E₆.latticeGraphIso`, `LineSystem.E₇.triangularGraphComplIso`); the third is `SimpleGraph.gq24` (SE3). The uniqueness in Lemma 2.10 is `H.orthGraph_iso_of_card_Γa_eq` |

The three Chang graphs are told apart by invariants (computation C22): the blueprint
(`blueprint/sec4-remark414.tex`, the repair of Gap 12) uses the profiles of 4-cliques through a
vertex, Chang I $\{32^4,36^{24}\}$, Chang II $\{34^{24},36^4\}$, Chang III $\{33^{10},35^{18}\}$ and
$T(8)$ $\{40^{28}\}$ (recomputed with Sage from the switching definitions), in
place of SE6's maximal cliques (Chang I $4^{32}5^{24}6^8$ and an automorphism group of order 384;
Chang II $4^{48}5^{48}$ and 96; Chang III $4^{75}5^{30}6^3$ and 360). [BvM] (§10.11, the table
under "Cliques and cocliques") and [S68] both list them in the order I, III, II of [CGSS]; a
quotation from either source must be translated.

## 7. Designs and Hadamard matrices (Sections 5 and 6)

| [CGSS] | Meaning | Blueprint | Lean |
| --- | --- | --- | --- |
| 2-design $D$ with $(v,k,b,r,\lambda)$, $v>1$, $k>1$, $b>0$ | points, blocks (repeated blocks allowed) | $D$, $D_1$, $D_2$ (italic; the types are upright); $(v,k,b,r,\lambda)$ | structure `Design` with `v k b r lam`: `λ` is the lambda keyword of Lean |
| $N$ | point-block incidence matrix | $N$ | `D.incMatrix` |
| complement, dual | | $\overline{D}$, $D^*$ | `D.compl` (Hall–Connor's `Design`); the dual is not defined in Lean |
| symmetric $(v,k,\lambda)$ design | $b=v$ | symmetric | `D.IsSymmetric` |
| resolvable, parallel | | resolvable; parallel class | a resolution into $c$ parallel classes, the structure `Design.Resolution D c` |
| $I(D)$ | incidence graph | $I(D)$ | `D.incidenceGraph` |
| $F(D)$ | flag graph, $L(I(D))$ | $F(D)$ | `D.flagGraph` |
| "characterized by its spectrum" | every cospectral graph is the flag graph of a design with the same parameters (errata Implicit hypothesis 6) | characterized by its spectrum, in this sense | `D.FlagGraphCharacterized` |
| $H_n$ | Hadamard matrix of order $n$ | $H$ (a matrix; no groups occur in Section 6) | `Matrix.IsHadamard` |
| Hadamard product of two rows | entrywise product | $H_i\circ H_j$, for the rows $H_i$ | `Matrix.hadamardRowProduct H i j`, a vector of `EuclideanSpace ℝ (Fin n)`; the pairs $i<j$ are `Matrix.HadamardPair n` |
| $P$ | the $\binom n2\times n$ matrix of the $H_i\circ H_j$ | $P$ | `Matrix.hadamardPairs H` |
| $A$ with $PP^T=nI+xA$ | a $(0,1,-1)$ matrix | $C_H$: for $d=2$ it is the matrix $C$ of Theorem 3.7 for these lines | `Matrix.hadamardSignedAdj H x` |
| $x$, $d=n/x$ | the parameters of Hypothesis 6.1 | $x$, $d$ (the paper's own; §8) | `x : ℕ`; there is no variable for $d$, which is the real `(n : ℝ) / x` in `Matrix.IsHadamard.hadamardSignedAdj_quadratic` and the natural number `n / x` in `Matrix.IsHadamard.FourRowAgreement.div_sq_eq_card_fourthRows` |
| Hypothesis 6.1 | any four rows agree in $\frac n8$ or $\frac18(n\pm x)$ places | Hypothesis 6.1 | `Matrix.IsHadamard.FourRowAgreement x` |

## 8. Clashes of letters

The paper reuses letters freely. We list the clashes that matter and how the blueprint resolves
each; "kept" means that the blueprint keeps the paper's letter for the paper's own object.

- **$C$.** The matrix of Theorem 3.7 and Remark 3.11, and the type $\mathrm C_\ell$. Types are
  upright, so italic $C$ is always the matrix (as in `remark311.tex`, §2). The same device frees
  italic $A$ (adjacency matrix), $B$, $D$ and $E$.
- **$A$.** The adjacency matrix, the type $\mathrm A_\ell$, and the $(0,1,-1)$ matrix of Section 6.
  Types are upright; the matrix of Section 6 is $C_H$.
- **$a$, $c$.** The strongly regular parameters, and the vectors $\mathbf a$, $\mathbf b$, $\mathbf c$ of
  Hypothesis 2.4. Vectors are always bold, so italic $a$, $c$ are the parameters. The paper's
  $CP(a)$ becomes $CP(m)$, the $a$ of Remark 4.12 becomes $t$, and the indexed $a_i$ of generalized
  line graphs are kept, never abbreviated to a bold $\mathbf a$.
- **$k$.** A valency; the block size of a design (Section 5); and $\lvert K\rvert$ in Lemma 2.10,
  where the graph is strongly regular with parameters $(6k-3,2k,1,k)$, so that the paper's $k$ is
  our $c$ and the valency is $2k$. Lemma 2.10 keeps its $k$ and writes the parameters out.
  Section 5 keeps $k$ for block sizes; there the valency of a flag graph is $r+k-2$, and
  Lemmas 5.1–5.6 are stated with $k$, $k_1$, $k_2$ before any design appears.
- **$n$.** The number of vertices; the dimension and rank ($\mathbb R^n$, $A_n$, $D_n$); the
  number of vertices or triangles in Lemma 2.12; a vertex $n\in N$ in Lemma 2.10; and the order of a
  Hadamard matrix. The blueprint writes the rank as $\ell$ ($\mathrm A_\ell$, $\mathrm D_\ell$,
  $\mathbb R^\ell$), as `remark311.tex` and LN6 already do; $m$ for the counts in Lemma 2.12; $w$ for
  vertices of $N$; and keeps $n$ for the order of a Hadamard matrix, which is the number of rows.
- **$v$.** A vertex; the valency (Section 5); the number of points of a design; and the vector
  $\mathbf v$ of Lemma 2.10. Valencies become $k$, $k_1$, $k_2$; $v$ is the number of points only
  in Section 5; the vector is $\mathbf v$.
- **$d$.** The valency in Theorem 4.4 (which becomes $k$), $n/x$ in Section 6 (kept), and in our
  usual notation the diameter or the index of the last eigenvalue.
- **$\lambda$.** The design parameter (kept in Section 5) and our generic eigenvalue. Section 5
  writes eigenvalues as $\theta$ or by name; in Lean, `lam`.
- **$\Sigma$.** The set of Hypothesis 2.4, the Root System of Definition 3.9, the representing set
  of Section 4, and a summation sign ($\frac12\Sigma e_k$ in Section 4). The blueprint keeps
  $\Sigma$ for the set of Hypothesis 2.4 only; a Root System is $\Phi$ (for roots of squared norm
  2, Theorem 3.10 says that it is exactly the $\Phi$ of a star-closed set of lines); a
  representation is a family $(\mathbf x_u)$; sums are written with limits.
- **$S$.** The set of lines of Section 2, the misprint in Definition 3.9 (b) (errata Error 10), the
  Steiner system $S(3,4,8)$ and the Seidel matrix $S(X)$. The last two always carry arguments.
- **$T$.** $T(n,m)$, the $m$-subsets of an $n$-set, and $T(m)=L(K_m)$. The blueprint writes
  $\binom{[n]}{m}$ for the former.
- **$G$, $H$.** Graphs in the paper, groups in our notation; $H_n$ is a Hadamard matrix; and
  `remark311.tex` writes $G$ for a Gram matrix. Graphs become $X$, $Y$, $Z$; the Hadamard matrix
  keeps $H$; the Gram matrix of Remark 3.11 keeps $G$ inside that remark.
- **$\Gamma$.** $\Gamma_a$, $\Gamma_b$, $\Gamma_c$, and the distance sets $\Gamma_i(v)$, which meet
  in Lemma 2.10 ($d_K(w)=\lvert\Gamma_1(w)\cap K\rvert$). The subscripts differ in kind
  (letters $a,b,c$ against numerals).
- **$B$.** The basis $B^n$ (dropped: the standard basis), the adjacency matrix $B$ before
  Theorem 3.8 (which becomes $A$), the biadjacency matrices $B_1$, $B_2$ of Lemma 5.6 (kept), and the
  type $\mathrm B_\ell$.
- **$E$.** The type $\mathrm E_8$, an edge set $E$ (Section 4), and a spectral idempotent $E_r$.
  Types are upright; the edge set is $E(X)$.
- **$D$.** The type $\mathrm D_\ell$ and a design $D$ (italic, kept).
- **$N$, $M$, $K$, $L$.** The sets of Lemma 2.10 (kept); $N_{\mathbf r}(\Phi)$ (always subscripted);
  the incidence matrices $N$ (designs) and $M$ (graphs), which appear only in Section 5; $K_n$ and
  $L(X)$ always carry arguments.
- **$\alpha$.** An angle (Lemma 2.3), an index (the generalized line graphs), and an eigenvalue
  (Theorem 4.4, Remark 5.7). The blueprint writes angles in degrees or as $\angle$, the index as
  $j$, and the eigenvalue as $\lambda$.
- **$x$.** A vector of $\Gamma_a$ (bold $\mathbf x$), a vertex, and the integer $x$ of Section 6 (kept).
- **Switching.** Three meanings: changing the signs of vectors of a signing (Section 2); replacing
  $\mathbf x_u$ by $\mathbf h-\mathbf x_u$ (Section 4, SW4); and Seidel switching of graphs (SW1). The blueprint
  says *re-signing*, *switching by $\mathbf h$*, and *Seidel switching*.

## 9. Mathlib names

These exist in Mathlib at the pinned commit; the project uses them for the notions they cover.

| Notion | Mathlib | Remark |
| --- | --- | --- |
| line graph | `SimpleGraph.lineGraph` | vertices `G.edgeSet` |
| strongly regular | `SimpleGraph.IsSRGWith n k ℓ μ`, `.matrix_eq`, `.param_eq`, `.compl` | admits the empty and complete graphs; `param_eq` uses truncated subtraction (SR1) |
| adjacency, degree, Laplacian | `SimpleGraph.adjMatrix`, `degMatrix`, `lapMatrix` | |
| incidence matrix | `SimpleGraph.incMatrix`, `incMatrix_mul_transpose` | a `Matrix α (Sym2 α) R`, indexed by all of `Sym2 α` |
| graphs | `completeGraph` (an abbreviation for `⊤`), `completeBipartiteGraph`, `starGraph`, `cycleGraph`, `pathGraph` | no Petersen, Schläfli, Clebsch, Shrikhande or cocktail party graphs |
| properties | `SimpleGraph.Connected`, `IsBipartite` (an abbreviation for `Colorable 2`), `IsBipartiteWith`, `IsRegularOfDegree`, `IsClique`, `IsNClique`, `IsIndepSet` | |
| isomorphism, complement | `SimpleGraph.Iso` (`≃g`), `Xᶜ` | |
| Gram matrices | `Matrix.gram`, `Matrix.posSemidef_gram` | |
| positive semidefinite, spectra | `Matrix.PosSemidef`, `Matrix.IsHermitian.eigenvalues`, `Matrix.charpoly`, `Matrix.charpoly_mul_comm'` | |
| Hadamard matrices | `Matrix.IsHadamard` (a structure) | `Mathlib/LinearAlgebra/Matrix/HadamardMatrix.lean` |
| Cartan matrices | `CartanMatrix.A`, `B`, `C`, `D`, `E`, `F₄`, `G₂`; `Matrix.IsFiniteCartan` | `CartanMatrix.A n` is an $n\times n$ matrix, the Cartan matrix of type $\mathrm A_n$ (rank $n$), although its docstring says "type Aₙ₋₁ (rank n-1)"; so a base of simple roots of our $\mathrm A_\ell$ has Gram matrix `CartanMatrix.A ℓ`. `CartanMatrix.E n` is a generalized family, and `E₆`, `E₇`, `E₈` are deprecated aliases of `E 6`, `E 7`, `E 8` |
| Coxeter matrices | `CoxeterMatrix.E₈` | |
| root pairings | `RootPairing`, `RootPairing.IsRootSystem`, `.IsCrystallographic`, `.IsReduced`, `.IsIrreducible`, `RootPairing.ofBilinear` | the bridge of Definition 3.9 and Theorem 3.10 |
| Euclidean spaces | `EuclideanSpace ℝ (Fin N)`, `LinearIsometry.extend`, `⟪x, y⟫` | |

In Lean identifiers, Greek letters are allowed except where they are tokens: `λ` (lambda),
`Σ` and `Π` (binders). Thus `Γa` and `Δ` are fine, and $\Sigma$ and $\lambda$ need other names
(`sigmaSet`, `lam`).

## 10. Lean names

These are the settled Lean names. A name changes only for a reason recorded here, such as the
shape that its Lean statement takes. The blueprint's `\lean{...}` tags use these names.

### Rules

1. **Mathlib's conventions.** Structures, classes and predicates are UpperCamelCase
   (`LineSystem.IsStarClosed`); other definitions are lowerCamelCase (`LineSystem.starClosure`,
   `H.orthGraph`); theorems are snake_case and name their conclusion, with `_of_` before a
   hypothesis when the name needs one (`LineSystem.classification_of_isMaximal`). A theorem about
   a structure or a predicate lives in its namespace, so that dot notation works
   (`LineSystem.IsMaximal.isStarClosed`, `H.triangle`). A definition that builds an isomorphism
   is named like a constructor (`LineSystem.Iso.ofOrthGraphIso`), and a theorem that one exists
   begins with `nonempty_iso`.
2. **Namespaces follow the objects**: `LineSystem` for line systems and for the
   root systems as line systems, `LineSystem.Hyp24` for the lemmas of Section 2, `SimpleGraph`
   for graphs, `Matrix` for matrices, `Design` for 2-designs, and `Computations.C1`, ...,
   `Computations.C24` for the numbered computations C1–C24 (`cgss/certificates/README.md`).
3. **The paper's objects keep the paper's letters**, Greek ones included, as Mathlib does for
   standard notation (`CategoryTheory.Limits.Cone.π`, `Real.Gamma`): `S.Φ`, `H.Γa`, `H.Δ`.
   Only the tokens of Lean are spelled out: `sigmaSet` for $\Sigma$ and `lam` for
   $\lambda$ (§9). The root systems are `LineSystem.An`, `Dn`, `E₆`, `E₇`, `E₈`;
   a bare `A` or `D` would clash with the adjacency matrix $A$ and a design $D$.
4. **No numbers from the paper in names**, with one exception: the structure `LineSystem.Hyp24`,
   which bundles the standing hypothesis of Section 2, and which the paper, the blueprint and the
   errata cite by its number throughout. The number of each result goes in its docstring
   (`/-- Lemma 2.3 of [CGSS]. -/`) and in a comment before it (`-- Lemma 2.3`), and
   `dependency-diagram.md` maps numbers to declarations. Thus Theorem 2.13 is
   `LineSystem.five_possibilities`, which names its content, and not
   `LineSystem.sectionTwo_classification`, which names its place.
5. **Theorems of other people keep their names.** Theorems 4.10, 4.11 and 4.13, which the paper
   states as the theorems of Hoffman, of Hoffman and Ray-Chaudhuri, and of Seidel, are
   `SimpleGraph.hoffman`, `SimpleGraph.hoffman_rayChaudhuri` and
   `SimpleGraph.seidel`; Theorem 3.8 is Smith's theorem, which we prove by Smith's argument, and is
   `SimpleGraph.smith`. The corollaries of Section 5 carry attributions too, but they are spectral
   characterizations and keep descriptive names.
6. **Counting lines.** The number of lines of `S` is `S.numLines`, that is, $\lvert\Phi\rvert/2$,
   and statements about numbers of lines use it (`LineSystem.numLines_E₈`).

A result with several parts may become several declarations; the tables list them all. A
docstring records any hypothesis that the paper leaves implicit (`cgss/errata.md`).

### Section 2

Here `H` is a term of `LineSystem.Hyp24`.

| Item | Lean name |
| --- | --- |
| line systems | `LineSystem`, `LineSystem.IsIndecomposable`, `LineSystem.Iso`, `LineSystem.numLines` |
| Def. 2.1 | `LineSystem.IsStarClosed` |
| Def. 2.2 | `LineSystem.IsMaximal` |
| Lemma 2.3 | `LineSystem.IsMaximal.isStarClosed` |
| Hyp. 2.4 | `LineSystem.Hyp24`, with `H.a`, `H.b`, `H.c`, `H.Γa`, `H.Γb`, `H.Γc`, `H.Δ`, `H.sigmaSet`, `H.third x y` and the orthogonality graph `H.orthGraph` |
| star identities (after Hyp. 2.4) | `H.c_mem`, `H.inner_b_c`, `H.inner_c_a`, `H.inner_c_b` |
| Lemma 2.5 | `H.Φ_eq_sigmaSet_union_neg` |
| Lemma 2.6 | `H.ΓaEquivΓb`, `H.ΓbEquivΓc`, `H.ΓcEquivΓa`, `H.inner_eq_zero_or_one`, `H.add_c_mem_Γb`, `H.sub_b_mem_Γc`; the literal forms, "isomorphic with respect to inner products", `H.inner_ΓaEquivΓb`, `H.inner_ΓbEquivΓc`, `H.inner_ΓcEquivΓa`, and the inner products within $\Gamma_b$ and $\Gamma_c$, `H.inner_eq_zero_or_one_of_mem_Γb`, `H.inner_eq_zero_or_one_of_mem_Γc` |
| Lemma 2.7 | `H.Δ_eq_sub`, `H.Φ_eq_recovery_union_neg` (the recovery formula), `H.Φ_eq_of_Γa_eq`; "$\Sigma$ is determined by $\Gamma_a\cup\{\mathbf a,\mathbf b,\mathbf c\}$" literally, `H.sigmaSet_eq_recoverySet` |
| Lemma 2.8 | `H.triangle`; the triangle property of the graph is `H.orthGraph_hasTriangleProperty`, for a new predicate `SimpleGraph.HasTriangleProperty` (it implies Mathlib's `SimpleGraph.LocallyLinear`, which asks only that every edge lie in exactly one triangle) |
| Lemma 2.9 | `H.orthGraph_iso_friendship_of_forall_adj` |
| Lemma 2.10 | the graph lemmas `SimpleGraph.HasTriangleProperty.normal_form_of_not_forall_adj` and `SimpleGraph.HasTriangleProperty.nonempty_iso_of_card_eq`; `H.card_Γa_mem`, `H.orthGraph_isSRGWith`, `H.orthGraph_iso_of_card_Γa_eq`; computation C1 is `Computations.C1.det_blockSumMinor` |
| Rem. 2.11 | none (a side claim, not formalized) |
| Lemma 2.12 | `H.orthGraph_cases`, `LineSystem.Iso.ofOrthGraphIso`; "one line, or Hypothesis 2.4", `LineSystem.IsIndecomposable.eq_pair_or_exists_hyp24` |
| Thm. 2.13 | `LineSystem.five_possibilities`, with the facts it takes from Section 3 as hypotheses (errata Gap 4); the unconditional form `LineSystem.five_possibilities'`, with those facts discharged by `LineSystem.modelInputs` (the packaged model facts, from C2 and C4, in `LineSystem/ClassificationModels.lean`), a term of the structure `LineSystem.ModelInputs` (`LineSystem/Section2Models.lean`). Uniqueness up to orthogonal transformations is `LineSystem.Iso.exists_ambient_isometry_of_same_model`, and the overlap of the first two cases (the zero-triangle case of Lemma 2.9: six lines in dimension 3) is `H.six_lines_of_iso_friendship_zero`. Both forms of `five_possibilities` state the data on $\Gamma_a$ and $\Delta$ for some star; the corollary for every star is `LineSystem.five_possibilities_forall_hyp24`, with the graph on `H.Γa` and the counts of `H.Γa` and `H.Δ` taken at the given star `H`; the one-line case, which has no star, stays with `five_possibilities'` |

### Section 3

| Item | Lean name |
| --- | --- |
| Def. 3.1 | `LineSystem.An`, `LineSystem.Dn`; the remark after it, that $\mathrm A_3$ is represented by the six diagonals of the cuboctahedron (a side claim, in Lean, `LineGraphs/SideClaims/Cuboctahedron.lean`): `LineSystem.cuboctahedronVertices` (the midpoints of the edges of the cube, with `LineSystem.cubeVertices`, `LineSystem.IsCubeEdge`, `LineSystem.cubeEdges`), the line system `LineSystem.cuboctahedron` and its diagonals `LineSystem.cuboctahedronDiagonals`; `LineSystem.cuboctahedron_eq_Dn`, the isomorphism `LineSystem.cuboctahedron.isoAn` and `LineSystem.nonempty_iso_cuboctahedron_An` |
| Def. 3.2 | `LineSystem.E₈viaA₈`, `LineSystem.E₈viaD₈`, `LineSystem.E₈viaSteiner`, and `LineSystem.E₈ := E₈viaD₈`; the isomorphisms of C3 are `LineSystem.E₈viaA₈.isoE₈` and `LineSystem.E₈viaSteiner.isoE₈` |
| Def. 3.3 | `LineSystem.E₇`, `LineSystem.E₆`; the cuts of model (iii) named for the counting argument, `LineSystem.T₇`, `LineSystem.T₆` (`LineGraphs/Computations/C2.lean`); the independence of the choice (errata Gap 5) is `LineSystem.E₈.nonempty_iso_E₇_orthogonalTo` and `LineSystem.E₈.nonempty_iso_E₆_orthogonalTo`, and in the other two models (`LineGraphs/LineSystem/ClassificationChoicesModels.lean`) `LineSystem.E₈viaA₈.nonempty_iso_E₇_orthogonalTo`, `LineSystem.E₈viaA₈.nonempty_iso_E₆_orthogonalTo`, `LineSystem.E₈viaSteiner.nonempty_iso_E₇_orthogonalTo` and `LineSystem.E₈viaSteiner.nonempty_iso_E₆_orthogonalTo`, with `LineSystem.T₇.nonempty_iso_E₇` and `LineSystem.T₆.nonempty_iso_E₆`. The singular names `…exists_isometry_of_ordered_star` and `…exists_isometry_of_root` carry a star or a root to the fixed one (of Definition 3.3, or of step `s3choiceSteiner` in model (iii)); the plural names `…exists_isometry_of_ordered_stars` and `…exists_isometry_of_roots` carry any one to any other; and C4's `E.exists_isometry_star` goes from the marked star to any star |
| Lemma 3.4 | `LineSystem.numLines_An`, `numLines_Dn`, `numLines_E₈`, `numLines_E₇`, `numLines_E₆` |
| Thm. 3.5 | `LineSystem.classification`, with the forward direction `LineSystem.exists_iso_rootType`; in Lean (`LineSystem/Classification.lean`) for any real inner product space, since the span of the finite root set is finite-dimensional, and with the forward proof shortened through the isomorphisms of `five_possibilities'` to the named models (steps `s335coords`, `s335orthogonal` not needed) |
| Thm. 3.6 | `LineSystem.classification_of_isMaximal`, with the form used in Section 4, `LineSystem.IsMaximal.exists_iso_rootType`; in Lean (`LineSystem/ClassificationMaximal.lean`), with the retained list stated as an explicit disjunction of the five families; the connected spanning criterion is `LineSystem.isIndecomposable_of_connected_spanning`, and the perpendicular choices are `LineSystem.E₈.nonempty_iso_E₇_orthogonalTo`, `E₈.nonempty_iso_E₆_orthogonalTo`, through `E₈.exists_isometry_of_ordered_star`, in the default model, which is all that Theorem 3.6 uses. The rest of Lemma (independence of the perpendicular choices) is in Lean as well (`LineGraphs/LineSystem/ClassificationChoicesModels.lean`): `LineSystem.E₈.exists_isometry_of_root`; `LineSystem.E₈viaA₈.exists_isometry_of_ordered_stars`, `E₈viaA₈.exists_isometry_of_roots`, `LineSystem.E₈viaSteiner.exists_isometry_of_ordered_stars`, `E₈viaSteiner.exists_isometry_of_ordered_star`, `E₈viaSteiner.exists_isometry_of_roots`, `E₈viaSteiner.exists_isometry_of_root`; and, for step `s3choiceSteiner`, `LineSystem.T₇_eq_orthogonalTo`, `T₆_eq_orthogonalTo`, `inner_t₇Normal_t₆Normal`. So are `T₇`, `T₆` with their counts `LineSystem.numLines_T₇`, `numLines_T₆`, and the bundles `Computations.C2.model_presentations`, `C2.line_counts` (`LineGraphs/Computations/C2.lean`) |
| Thm. 3.7 | `LineSystem.signedAdj_quadratic_An` and its analogues for `Dn`, `E₆`, `E₇`, `E₈`, from `LineSystem.frame_identity` (C6); a signing exists, indexed by `Fin S.numLines`, `LineSystem.nonempty_signing`, so the equations, which hold for every `LineSystem.Signing`, are not vacuous |
| Thm. 3.8 | `SimpleGraph.smith`, for the Smith graphs of §3; the second and third sentences of Corollary D, `SimpleGraph.smith_exists_gram` and `SimpleGraph.smith_gram_delete_basis`; the largest eigenvalue 2 of the Smith graphs (C17), `SimpleGraph.smithA_maxRayleigh`, `smithD_maxRayleigh`, `smithE₆_maxRayleigh`, `smithE₇_maxRayleigh`, `smithE₈_maxRayleigh`; and, for the paragraph before the theorem, `SimpleGraph.eigenvalue_le_two_of_gram_representation` and `SimpleGraph.largestEigenvalue_eq_two_of_gram_representation` |
| Def. 3.9 | `IsRootSet` |
| Thm. 3.10 | `LineSystem.isRootSet_tfae` |
| Rem. 3.11 | `IsRootSet.classification` (Theorem B of `remark311.tex`, the passage to Euclidean Root Systems), in Lean (`LineGraphs/RootSetClassification/Classification.lean`), with Theorem C, `IsRootSet.remark_lines`, and the `RootSetModel.*` declarations of `blueprint/sec3-remark311.tex` (`LineGraphs/RootSetClassification/`); Theorem A of `remark311.tex`, the classification of the finite-type Cartan matrices, is `Matrix.IsFiniteCartan.classification`, with `CartanMatrix.isFiniteTypeModel_iff` (the definition against the disjunction of §13 of remark311.tex) and `Matrix.IsFiniteCartan.classification_type_unique`. Some names of Theorem B depart from rule 1: theorems named like nouns (`RootSetModel.base`, `.cartanMatrix`, `.numLines`), the object before the conclusion (`RootSetModel.An_isRootSet`, `.An_ncard`), and `similarity_comp`, `similarity_symm` outside `IsSimilarity`. They are kept as they are, since the blueprint tags them. The matrix equations of Theorem C hold for every family of root representatives (`RootRepresentatives`, one root on each line); such a family exists, indexed by `Fin hΦ.numLines`, `IsRootSet.exists_rootRepresentatives` |
| Thm. 3.12 | `LineSystem.subset_rootSet_iff_bipartition`, for `S : Set (Submodule ℝ V)` of lines of finrank one with `HasAllowedAngles S` (the bundled `LineSystem` cannot hold lines at 45°); with `HasSquaredCosine`, `HasAllowedAngles`, `HasBipartition` (a colouring, either part may be empty; errata, Implicit hypothesis 8), `rootLines`, `integralSpanRoots` (the set Ψ(T) of `cgss/proofs/thm312/thm312.tex`), `finite_of_hasAllowedAngles`, `isRootSet_integralSpanRoots`, `exists_rootSet_of_hasBipartition`, and the bridges `hasAllowedAngles_rootLines`, `hasBipartition_rootLines` |

### Computations and tools of Section 3 in Lean

These names exist in `LineGraphs/`. `E` is one of `E₆`, `E₇`, `E₈`.

| Item | Lean name |
| --- | --- |
| integer models | `LineSystem.IntegerModel` (with `.equiv`, `.numLines_eq`, `.sum_Φ`, `.mem_iff_decode`, `.isStarClosed_of_checkStar`, `.isIndecomposable_of_parent`, `.hyp24`), `LineSystem.Iso.ofIntegerModels` |
| spans | `LineSystem.finrank_span_An`, `finrank_span_Dn`, `finrank_span_E₈`, `finrank_span_E₇`, `finrank_span_E₆` (and the other E₈ models) |
| reflections | `LineSystem.isometryGroup`, `LineSystem.rootReflection`, `rootReflection_mem_isometryGroup`; `Hyp24.orthGraphIsoOfIsometry`, `Hyp24.ΓaEquivOfIsometry`, `Hyp24.ΔEquivOfIsometry`; `IntegerModel.exists_isometry_of_tree`, `.exists_isometry_of_star` |
| C3 | `LineSystem.E₈viaA₈.nonempty_iso_E₈`, `LineSystem.E₈viaSteiner.nonempty_iso_E₈` (from the Sage maps `maps[0]`, `maps[1]` of `cgss/certificates/data/c03_maps.json`; Lean checks the root correspondence) |
| C4, models | `isStarClosed_An`, `isStarClosed_Dn`, `isStarClosed_E`, and for the E₈ models; `isIndecomposable_An` (1 ≤ n), `isIndecomposable_Dn` (4 ≤ n), `isIndecomposable_E`; `Iso.isStarClosed`, `Iso.isIndecomposable`; the bundle `Computations.C4.model_data` |
| C4, marked stars | `An.hyp24`, `Dn.hyp24`, `E.hyp24Simple` (the blueprint's star e₁−e₂, e₂−e₃) and `E.hyp24` (the star a′, b′), with `_a`, `_b`; `An.orthGraphIso : ⊥ ≃g _`, `Dn.orthGraphIso : friendship (n − 3) ≃g _`, `E.orthGraphIso`; `.card_Γa`, `E.card_Δ`, `E.orthGraph_isSRGWith`; the bundles `Computations.C4.marked_star_data`, `Computations.C4.exceptional_star_data` |
| C4, every star | `E.exists_isometry_star`; for `H : Hyp24` with `H.S = E`: `Hyp24.orthGraph_isSRGWith_of_S_eq_E`, `card_Γa_of_S_eq_E`, `card_Δ_of_S_eq_E`, `nonempty_orthGraph_iso_of_S_eq_E` |
| C4, graphs | `E₆.latticeGraphIso` (with L₂(3)), `E₇.triangularGraphComplIso` (with the complement of T(6)), `Hyp24.nonempty_latticeGraph_iso_of_S_eq_E₆`, `Hyp24.nonempty_triangularGraph_compl_iso_of_S_eq_E₇`; `SimpleGraph.friendship`, `SimpleGraph.completeBipartiteEdgeEquiv`, `SimpleGraph.completeGraphEdgeEquiv` (in `LineGraphs/Graphs/Basic.lean`) |
| C20 (LN6) | `LineSystem.N`, `finite_N`, `pairInv`; `An.card_N`, `Dn.card_N`, `E.card_N`; at the apex `E₈.c`: `E.c_mem`, `E.CEdge`, `E.cPairs` (with `_false`, `_true`), `E.pairInv_cPairs`, `E.N_c`, `E.card_N_c` |
| C21 | `E.simpleRoot`, `.gram_simpleRoot`, `.det_gram_simpleRoot`, `.simpleBasis`; `Computations.C21.e6_gram_det`, `e7_gram_det`, `e8_gram_det`; `E.gram_simpleRoot_eq_cartan` (the Gram matrix is `CartanMatrix.E k` up to the permutations `Computations.C21.e6Relabel`, `e7Relabel`, `e8Relabel`, with Mathlib's Bourbaki numbering), `Computations.C21.e6_gram_eq_cartan`, `e7_gram_eq_cartan`, `e8_gram_eq_cartan` |
| C5 | `LineSystem.IsometricInclusion` (with `.root`, `.IsProper`, `.isProper_of_ncard_lt`, `.ofLinearMap`, `.ofSubset`, `.ofRows`, `.trans`, `.orthGraphEmbedding`), `Hyp24.orthGraph_embedding_of_subset`, `LineSystem.not_isMaximal_of_proper_isometric_inclusion`; the inclusions by explicit coordinate rows `An.inclusionE₇`, `An.inclusionE₈` (not through C3), `Dn.inclusionE₈`, `An.inclusionE₈viaA₈`, with `_isProper`; `An.not_isMaximal_seven`, `An.not_isMaximal_eight`, `Dn.not_isMaximal_eight`; `Dn.exists_isometry_star`, `Hyp24.nonempty_orthGraph_iso_of_S_eq_Dn`, `Hyp24.card_Γa_of_S_eq_Dn`; the obstructions `LineSystem.not_embeds_An_Dn` (4 ≤ ℓ; errata Gap 13), `not_embeds_An_E₆` (no 4-coclique in the 3 × 3 grid, by pigeonhole), `not_embeds_Dn_E₆`, `not_embeds_Dn_E₇`; the bundle `Computations.C5.inclusions_and_obstructions` |
| C6 | `LineSystem.frameSum`, `LineSystem.IsFrame S t` (on the span), `isFrame_iff_gram`, `Iso.isFrame`; `Computations.C6.an_frame_matrix`, `dn_frame_matrix` (parametric), `e₈_frame_matrix`, `e₇_frame_matrix`, `e₆_frame_matrix`, `e₈viaA₈_frame_matrix`, `e₈viaSteiner_frame_matrix` (`decide +kernel`), the bundle `Computations.C6.coordinate_frame_matrices`; `isFrame_An n` (2(n+1)), `isFrame_Dn n` (4(n−1)), `isFrame_E₈` (60), `isFrame_E₇` (36), `isFrame_E₆` (24), and for the other E₈ models; `LineSystem.RootType` with `.model`, `.rank`, `.numLines_model`, `.isFrame_model`; `LineSystem.frame_identity`, `frame_identity_signing` (with the model's rank); `Signing`, `signedAdj`, `signedAdj_quadratic_of_frame`, `signedAdj_quadratic t`, and Theorem 3.7 as in §3. In `LineSystem/SpanTransport.lean` and `SpanExtension.lean`: `LineSystem.Iso.spanIsometry`, `restrictSpan`, `Iso.restrictSpan`, `exists_maximal_extension_span`|

### Section 4

| Item | Lean name |
| --- | --- |
| opening paragraph | `SimpleGraph.exists_representation_iff_posSemidef`, `SimpleGraph.IsRepresentation.isIndecomposable_of_connected`; "such a set of lines is contained in a root system", for a graph that need not be connected, is `SimpleGraph.IsRepresentation.latticeRoots` with `.isStarClosed_latticeRoots` and `.isRepresentedIn_latticeRoots` (`Seidel/LatticeRoots.lean`, written for Remark 4.14) |
| Thm. 4.1 | `SimpleGraph.isRepresentedIn_An_iff` |
| remark after 4.1 | `LineSystem.An.card_nonneg_subset_le` (the bound $\lfloor\frac14(n+1)^2\rfloor$), `LineSystem.An.nonneg_subset_maximal_iff` (the maximal sets are the $\Sigma_P$), `LineSystem.An.exists_nonneg_subset_card_eq` (the bound is attained, by some $\Sigma_P$ with $\lvert P\rvert=\lfloor\frac12(n+1)\rfloor$: the statement gives `∃ P, P.ncard = (n + 1) / 2 ∧ sigma = sigmaP P`), `LineSystem.An.isRepresentation_lineGraph_completeBipartite_sigmaP` (the vectors of $\Sigma_P$, indexed by the edges of $K_{m,n+1-m}$, represent $L(K_{m,n+1-m})$); blueprint `rem:4-after41` |
| $CP(m)$, $L(Y;a_1,\dots,a_m)$ | `SimpleGraph.cocktailParty`, `SimpleGraph.generalizedLineGraph`, `SimpleGraph.IsGeneralizedLineGraph` |
| Thm. 4.2 | `SimpleGraph.isRepresentedIn_Dn_iff` |
| remark after 4.2 | `LineSystem.Dn.card_nonneg_subset_le` (the bound $\frac12n(n-1)$, for $n\ge4$), `LineSystem.Dn.exists_isRepresentation_generalizedLineGraph_top_of_maximal` (a maximal set represents $L(K_m;a_1,\dots,a_m)$ with $\sum_i(1+a_i)=n$; named by rule 1, since "represents" is not a project predicate, the conclusion is existential and the complete graph is `⊤`), `LineSystem.Dn.exists_nonneg_subset_card_eq` (the bound is attained, by $\{\mathbf e_i+\mathbf e_j:i<j\}$, which the statement gives as the range of `(⊤ : SimpleGraph (Fin n)).lineGraphVector`, together with the representation of $L(K_n)$ by it); blueprint `rem:4-after42`, through `SimpleGraph.IsRepresentation.exists_normal_form_Dn` (Lemma (the normal form in $\mathrm D_n$), the proof of Theorem 4.2 with the coordinates kept; in snake case, as `HasTriangleProperty.normal_form_of_not_forall_adj`, rule 1) |
| Thm. 4.3 | `SimpleGraph.IsRepresentedIn.card_le_36`, `.degree_le_28`, `SimpleGraph.exists_isRepresentedIn_E₈_card_36` |
| Thm. 4.4 | `SimpleGraph.IsRepresentedIn.card_le_28_of_regular`, `.degree_le_16_of_regular`; in Lean also as `.card_le_28_of_regular_of_classification`, `.degree_le_16_of_regular_of_classification` (`Representation/Theorem44.lean`), with the classification of Theorem 3.6 in the nine-dimensional space of EQ2 as the hypothesis `hclass`; the settled names are proved in `Representation/Theorem44Unconditional.lean`, by discharging `hclass` with `LineSystem.IsMaximal.exists_iso_rootType`. The case (28, 17) is `SimpleGraph.not_regular_28_17_of_rank_le_seven` (trace and rank) |
| remark after 4.4 | `SimpleGraph.not_regular_28_16_isRepresentedIn_E₈`; in Lean as `SimpleGraph.not_regular_28_16_isRepresentedIn_E₈_of_classification` (EQ2 first, through `SimpleGraph.IsRepresentedIn.rank_le_seven_of_regular_of_classification`, then C24), with the same hypothesis; the settled name is proved in `Representation/Theorem44Unconditional.lean` in the same way |
| Exs. 4.5–4.9 | `SimpleGraph.changI_isRepresentedIn_E₈`, `changII_…`, `changIII_…`, `schlafli_…`, `shrikhande_…`, `clebsch_…`, `petersen_…`, with `…_isSRGWith`; the switching equivalences of Example 4.8, `SimpleGraph.clebsch_isSwitchingEquivalent_shrikhande` and `SimpleGraph.clebsch_isSwitchingEquivalent_lineGraph_completeBipartite`; the Petersen graph as the Kneser graph $K(5,2)$ (Example 4.9), `SimpleGraph.petersen.kneserIso`; the induced subgraphs of Examples 4.7 (the Shrikhande graph in the Chang graph I) and 4.8 (the Clebsch graph on the neighbours of $\mathbf e_5+\mathbf e_6$ in the Schläfli graph), `SimpleGraph.shrikhande.nonempty_iso_induce_changI` and `SimpleGraph.clebsch.nonempty_iso_induce_schlafli`, with the index maps `shrikhande.changIIndex`, `clebsch.schlafliIndex`, their kernel checks `…_checked` and the embeddings `shrikhande.changIEmbedding`, `clebsch.schlafliEmbedding` (`Computations/C9Subgraphs.lean`); the paper's "which are not line graphs", `SimpleGraph.seidelSeven_not_iso_lineGraph` (`Seidel/Seven.lean`), for every root graph |
| Thm. 4.10 | `SimpleGraph.hoffman` |
| Thm. 4.11 | `SimpleGraph.hoffman_rayChaudhuri` |
| Rem. 4.12 | `SimpleGraph.IsGeneralizedLineGraph.clawFree_iff` (assertion 3); `SimpleGraph.generalizedLineGraph_fourClawFree_iff` (assertion 5; not in the namespace `IsGeneralizedLineGraph`, since it is a criterion on the parameters of $L(Y;a_1,\dots,a_m)$ and cannot be stated from the predicate alone, rule 1) |
| Thm. 4.13 | `SimpleGraph.seidel` |
| Rem. 4.14 | `SimpleGraph.seidel_seven` |
| remarks after 4.4, 4.12, after the examples | `SimpleGraph.regular_28_12_and_27_16_isRepresentedIn_E₈`; `Computations.C24.trace_sq_gt`; Lemma (trace and rank) in the entrywise form of the blueprint, `Matrix.IsHermitian.trace_sq_le_rank_mul_sum_entry_sq` (`Representation/Theorem44.lean`), since the eigenvalue form `Matrix.IsHermitian.trace_sq_le_rank_mul_sum_sq` of `Spectral/Applications.lean` took the name first; `SimpleGraph.IsRegularOfDegree.posSemidef_centered`, `.rank_centered` (Mathlib's spelling, rule 1; the prose keeps "centred"), `.posSemidef_equiangular`, `.rank_equiangular`; `SimpleGraph.ClawFree`, `SimpleGraph.FourClawFree`, `SimpleGraph.IsClaw`, `SimpleGraph.IsFourClaw` (a claw at $u$ on a set $T$ of neighbours), `SimpleGraph.clawFree_iff_forall_not_isClaw`, `fourClawFree_iff_forall_not_isFourClaw`, `SimpleGraph.Iso.clawFree_iff`, `Iso.fourClawFree_iff` (Lemma (claws and stars): an induced `starGraph` against a claw, and invariance under isomorphism), `generalizedLineGraph_not_isClaw_petal`, `_isClaw_edge_iff`, `_isFourClaw_edge_iff`, `lineGraph_clawFree`, `cocktailParty_clawFree`, `generalizedLineGraph_clawFree_iff`, `SimpleGraph.hoffman_of_clawFree`; `SimpleGraph.hoffman_of_large`, `hoffman_rayChaudhuri_of_large`, `seidel_of_large` |
| Section 4 tools (`blueprint/sec4-leasteigenvalue.tex`) | `Matrix.rank_gram_eq_finrank_span`, `Matrix.PosSemidef.exists_gram_euclideanSpace` (a positive semidefinite matrix of rank at most r is a Gram matrix in ℝʳ); `SimpleGraph.IsRepresentation.induce`, `.switch`, `.of_isometricInclusion`, `.exists_isRepresentedIn_rootType`, `IsRepresentedIn.degree_le_of_card_N_le`, `lineGraph_isRepresentation`, `generalizedLineGraph_isRepresentedIn_Dn`, `generalizedLineGraph_degree_edge`, `_degree_petal`, `IsGeneralizedLineGraph.lineGraph_or_cocktailParty`, `lineGraph_isSRGWith_cases`, `IsRepresentation.exists_normal_form_Dn`; `Computations.C7.isRepresentedIn_E₈`, `Computations.C8.quadratic_bound`; `EuclideanSpace.inner_symSq`; `InnerProductSpace.card_le_relativeBound` (EQ1), `InnerProductSpace.card_le_fourteen_of_finrank_eq_eight` (EQ2); `LineSystem.IsNonnegSubset` (a subset of roots with nonnegative mutual inner products), `LineSystem.An.sigmaP` (the set $\Sigma_P$); `Matrix.PosSemidef.rank_add_allOnes_of_pos` (for Lemma (the matrices of a regular graph)) |
| SE2, SE3 (`cgss/proofs/clebsch/`) | the combinatorial graphs `SimpleGraph.foldedFiveCube` (on `{s : Finset (Fin 5) // Even s.card}`, adjacent when `(s.1 ∆ t.1).card = 4`) and `SimpleGraph.gq24` (on `Fin 2 × Fin 6 ⊕ {s : Finset (Fin 6) // s.card = 2}`, the double six), with `foldedFiveCube_isSRGWith` $(16,5,0,2)$, `gq24_isSRGWith` $(27,10,1,5)$, and `compl_foldedFiveCube_adj_iff`, `compl_gq24_adj_iff` for the complements (these replace the proposals `clebsch_adj_iff`, `schlafli_adj_iff`, since `clebsch` and `schlafli` are not defined as complements); the certificate isomorphisms of C9, `SimpleGraph.clebsch.foldedFiveCubeComplIso : clebsch ≃g foldedFiveCubeᶜ` and `SimpleGraph.schlafli.gq24ComplIso : schlafli ≃g gq24ᶜ` (defs, named as `LineSystem.E₆.latticeGraphIso`, rule 1; tagged in the statement of C9, `comp:C9` of `blueprint/sec4-leasteigenvalue.tex`; their Lean goes with the rest of C9 in `LineGraphs/Computations/C9*.lean`, with `foldedFiveCube` and `gq24`); `SimpleGraph.Iso.compl` (new; Mathlib has only `Embedding.complEquiv`); `SimpleGraph.IsSRGWith.hasTriangleProperty` (hypothesis `n + 3 = 3 * k`); `IsSRGWith.nonempty_iso_foldedFiveCube` $(16,5,0,2)$, `IsSRGWith.nonempty_iso_clebsch` $(16,10,6,6)$ (through the complement and the certificate), `IsSRGWith.nonempty_iso_gq24` $(27,10,1,5)$, `IsSRGWith.nonempty_iso_schlafli` $(27,16,10,8)$ (the same) |
| SE4 (for Rem. 4.14) | the regular graphs of valency at most 3 on 8 vertices, `cgss/proofs/reg8/reg8.tex`: `SimpleGraph.fourK2`, `cycleThreeFive`, `twoC4`, `twoK4`, `cubeGraph`, `wagnerGraph`, `truncatedK33Graph`, `twiceTruncatedK4Graph`, `twoDiamondsGraph` (on `Fin 8`, as an 8-cycle with chords, `cycleWithChords P`), `numFourCycles`; `IsRegularOfDegree.nonempty_iso_of_two_of_card_eq_eight`, `.nonempty_iso_of_three_of_card_eq_eight`, `SimpleGraph.cubic_eight_pairwise_not_iso` |
| Rem. 4.14 tools (`blueprint/sec4-remark414.tex`) | *switching:* `SimpleGraph.switch`, `switch_compl`, `Iso.switch`, `Iso.lineGraphSwitch`; *isomorphisms:* `SimpleGraph.Iso.compl`, `SimpleGraph.IsSRGWith.of_iso`; *parameters:* `IsRegularOfDegree.nonempty_iso_cocktailParty`, `IsSRGWith.params_of_det_two_add_adjMatrix_eq_zero`, `IsSRGWith.rank_two_add_adjMatrix_of_det_eq_zero`, `Computations.C18.srg_parameters`, `IsSRGWith.nonempty_iso_lineGraph_complete_or_completeBipartite`; *the root system of a representation:* `IsRepresentation.latticeRoots`, `.isStarClosed_latticeRoots`, `.isIndecomposable_latticeRoots`, `.span_latticeRoots`, `.isRepresentedIn_latticeRoots`, `IsRepresentation.apex`, `.inner_apex`, `.inner_apex_self`, `.inner_apex_mem_int`, `.apex_mem_span`, `InnerProductSpace.det_gram_mul_inner_self_mem_int`, `LineSystem.E₆/E₇/E₈.exists_isometry_apply_eq_c`, `IsRepresentation.nonempty_iso_lineGraph_switch`; *regular switchings:* `SimpleGraph.card_adj_lineGraph_switch_of_complete`, `Finset.two_mul_eq_of_forall_add_eq`, `IsRegularOfDegree.nonempty_iso_cycle_of_two_of_card_eq_five`, `.nonempty_iso_of_two_of_card_eq_six`, `Computations.C22.e6_switch_cycle5`, `e7_switch_cycle6`, `e7_switch_twoC3`, `e8_switch_fourK2`, `e8_switch_twoC4`, `e8_switch_cube`, `e8_switch_twoDiamonds`, `e8_switch_cycle8`, `e8_switch_wagner`, `e8_switch_twiceTruncatedK4`, `e8_switch_cycleThreeFive`, `e8_switch_truncatedK33`, `e8_switch_twoK4`, `e8_switch_empty`, `cliqueProfile_t8`, `cliqueProfile_changI`, `cliqueProfile_changII`, `cliqueProfile_changIII`, `cliqueCount_shrikhande`, `cliqueCount_lineGraph_completeBipartite`, `SimpleGraph.nonempty_iso_petersen_of_switch_triangular5`, `nonempty_iso_shrikhande_or_lineGraph_completeBipartite_of_switch_triangular6AddOne`, `nonempty_iso_triangular8_or_chang_of_switch_triangular8`; *the models of SE2 and SE3:* the row "SE2, SE3" above; `comp:414-models` keeps the parameters `foldedFiveCube_isSRGWith`, `gq24_isSRGWith` and cites C9 for the two certificate isomorphisms; *the seven graphs:* `SimpleGraph.seidel_seven_properties`, `seidel_seven_pairwise_not_iso`, `seidel_seven_classification` (`seidel_seven` of Rem. 4.14 is the conjunction of `seidel_seven_classification`, `seidel_seven_pairwise_not_iso` and `seidel_seven_properties`) |

### Section 5

| Item | Lean name |
| --- | --- |
| Lemma 5.1 | `SimpleGraph.IsRegularOfDegree.largestEigenvalue_eq` (the largest eigenvalue is the valency), `SimpleGraph.IsRegularOfDegree.multiplicity_eq_card_components` |
| Lemma 5.2 | `SimpleGraph.isRegular_iff_sum_sq_eigenvalues` |
| Lemma 5.3 | `SimpleGraph.IsRegularOfDegree.isBipartite_iff_neg_eigenvalue`; the multiplicity-one clause (SP3) is `SimpleGraph.IsRegularOfDegree.multiplicity_neg_eq_one` |
| Lemma 5.4 | `SimpleGraph.regular_or_semiregular_of_lineGraph_regular` (the toolkit's Theorem 6.4); the blueprint's form is `SimpleGraph.regular_or_isBiregularWith_of_lineGraph_regular` |
| Lemma 5.5 | `SimpleGraph.cospectral_of_lineGraph_cospectral` |
| Lemma 5.6 | `SimpleGraph.lineGraph_cospectral_bipartite` (the toolkit's Theorem 6.7), not in Lean; the blueprint's form, which is in Lean, is `SimpleGraph.lineGraph_cospectral_bipartite_forall_isBiregularWith` |
| Rem. 5.7 | `SimpleGraph.lineGraph_cospectral_bipartite_spectrum` (the toolkit's Corollary 6.8), not in Lean; the blueprint's form, which is in Lean, is `SimpleGraph.lineGraph_cospectral_bipartite_spectrum_of_not_isBipartite`; the spectrum of the block matrix $C$ of the remark is `Matrix.spectrumMultiset_fromBlocks_scalar_of_ne` |
| Thm. 5.8 | `Design.flagGraph_cospectral`; in Lean (`LineGraphs/LineGraphSpectra/Theorem58.lean`), on Hall–Connor's `Design`, with the real cast `Design.realIncMatrix` of its integer incidence matrix for the spectral statements |
| Cor. 5.9 | `SimpleGraph.lineGraph_completeBipartite_characterized` (Doob); in Lean (`LineGraphs/LineGraphSpectra/Corollaries.lean`), on Hall–Connor's `Design`, with the real cast `Design.realIncMatrix` of its integer incidence matrix for the spectral statements |
| Cor. 5.10 | `Design.IsSymmetric.flagGraphCharacterized` (Hoffman and Ray-Chaudhuri); in Lean (`LineGraphs/LineGraphSpectra/Corollaries.lean`), on Hall–Connor's `Design`, with the real cast `Design.realIncMatrix` of its integer incidence matrix for the spectral statements; the exception $(v,k,\lambda)=(4,3,2)$ is not characterized, in the sense of Implicit hypothesis 6, `Computations.C13.not_flagGraphCharacterized` (`Computations/C13Characterization.lean`) |
| Cor. 5.11 | `Design.flagGraphCharacterized_of_lam_eq_one` (Doob); in Lean (`LineGraphs/LineGraphSpectra/Corollaries.lean`), on Hall–Connor's `Design`, with the real cast `Design.realIncMatrix` of its integer incidence matrix for the spectral statements |
| Rem. 5.12 | `Design.flagGraphCharacterized_of_lam_lt_nineteen`; in Lean (`LineGraphs/LineGraphSpectra/Remark512.lean`), on Hall–Connor's `Design`, with the real cast `Design.realIncMatrix` of its integer incidence matrix for the spectral statements; the exception of the trivial design $(6,6,10,10,10)$, whose flag graph $L(K_{10,6})$ is cospectral with $L(L(K_6))$ and not characterized, in the namespace `Computations.TrivialDesignException` (`Computations/TrivialDesignException.lean`): `design`, the spectra `spectrum_flagGraph` and `spectrum_double_lineGraph` from the certificates `incidence_spectrum_checked` and `complete_spectrum_checked`, `flagGraph_cospectral_double_lineGraph`, `lineGraph_completeBipartite_cospectral_double_lineGraph`, `flagGraph_not_nonempty_iso_double_lineGraph` and `not_flagGraphCharacterized`; the identity it uses, the spectrum of $L(Y)$ from the signless Laplacian of $Y$ when $Y$ has at least as many edges as vertices, is `SimpleGraph.spectrumMultiset_lineGraph_of_card_le` (`Spectral/LineGraphSpectrum.lean`) |
| Ex. 5.13 | `Design.not_flagGraphCharacterized_of_resolvable`; in Lean (`LineGraphs/LineGraphSpectra/Example513.lean`), on Hall–Connor's `Design`, with the real cast `Design.realIncMatrix` of its integer incidence matrix for the spectral statements. Step `s5exnoiso` uses a clique bound in place of EX4 (Whitney), which the example then does not need: `Design.not_nonempty_iso_flagGraph_lineGraph_of_degree`, from `Design.exists_clique_flagGraph_card_replication` (an $r_1$-clique in every candidate flag graph) and `SimpleGraph.card_clique_lineGraph_le` (every clique of $L(H)$ has at most $\kappa$ vertices), with $r_1=(k-1)(2k+1)>\kappa=2k(k-1)\ge4$ (`LineGraphs/LineGraphSpectra/LineGraphCliques.lean`). *Named* by mathematical content (rules 4 and 1): `Design.nonbipartiteParameters_and_even_resolution_family` and `Design.Resolution.spectrumMultiset_graph_nonbipartite_form` (`Example513Parameters.lean`), `Design.spectrumMultiset_signlessLapMatrix_incidenceGraph_resolution_family` (`ResolutionLineGraph.lean`), and `SimpleGraph.Cospectral.change_instances` (`Example513.lean`) |
| C11 to C15 (`Computations/C11*` to `C15*`; tagged at the citing steps and remarks of `blueprint/sec5-spectral.tex`) | *C11 (Thm. 5.8):* `Computations.C11.parameter_equation`, `exists_positive_half_difference`, `two_mul_sq_mul_points`, `mul_blocks_sub_points`, `dvd_block_size`, `parameters`, `two_le_parameter`, `lambda_equation`, `lambda_remainder`, `parameter_dvd`, `two_mul_sub_one_le` (the corrected $s\ge2t-1$, errata Error 4), `nonprincipal_square`, `spectral_parameters`, `spectrum_of_parameters` (the substitution only; its input spectrum comes from Rem. 5.7 in the caller), `matrix_identity`, `hoffman_value`, `cube_diagonal_eq`, `triangle_diagonal`, `even_cube_diagonal`, `even_parameter_cube` (takes the integer cubic diagonal as a hypothesis), `even_mul_of_even_cube`; untagged: `points_eq`, `spectral_moments`. *C12 (Cor. 5.9):* `Computations.C12.full_block_parameters` (all of step `s559st`, $t\ge2$ and $c=t^2$ included, for integers $s\ge2$, $t\ge1$), `core`, `border`, `core_row_sum`, `core_mul`, `border_isHadamard`, `hadamard_border` (order $4t^2$, diagonal $-1$). *C13 (remark after Cor. 5.10):* `Computations.C13.graph1`, `graph2`, `spectrum_graph1`, `spectrum_graph2`, `cospectral`, `not_nonempty_iso`, `design`, `nonempty_iso_flagGraph` (for the ad hoc `Computations.C13.incidenceGraph`), `cube`, `cubeLineGraphIso`, `nonempty_iso_cube_lineGraph` (graph 1 is $L(Q_3)$, by an explicit isomorphism, `Computations/C13Cube.lean`), `representation_graph1`, `representation_graph2`, `isRepresentedIn_E₇_graph1`, `isRepresentedIn_E₇_graph2`; untagged: the Seidel spectra and `switching_equivalent`. *C14 (Rem. 5.12):* `Computations.C14.lambda_remainder`, `lambda_eq_two`, `lambda_ge_nineteen`, `t2_parameters`, `eq_three_or_five`; untagged: `nineteen_sharp`. *C15 (remark after Ex. 5.13):* `Computations.C15.flagGraph_cospectral_double_lineGraph`, `flagGraph_not_nonempty_iso_double_lineGraph`, `design`, `four_cliques_graph1`, `four_cliques_graph2`, `Computations.C15.petersen` (pentagon, pentagram, spokes; the certificate's model), `petersenIso`, `nonempty_iso_petersen` (`Computations/C15PetersenIso.lean`); the two settled statements are about `SimpleGraph.petersen.lineGraph.lineGraph`, through `petersenIso` |

### Section 6

| Item | Lean name |
| --- | --- |
| Hyp. 6.1 | `Matrix.IsHadamard.FourRowAgreement` |
| Thm. 6.2 | `Matrix.IsHadamard.not_fourRow_agree_sixteenths` |
| Section 6 tools (`blueprint/sec6-hadamard.tex`; in Lean in full, `LineGraphs/Hadamard/`: the components, `LineSystem.starClosure` (LN3), the decomposition, the $E_7$ exclusion and Theorem 6.2 as `Matrix.IsHadamard.component_rootType`, `component_cases`, `not_component_E₇`, `not_fourRow_agree_sixteenths`, with `_of_classification` forms) | `Matrix.HadamardPair`, `Matrix.hadamardRowProduct`, `Matrix.fourRowAgreeCount`, `Matrix.fourthRows`; `Matrix.hadamardSignedAdj H x` (the settled name now takes `x`); `Matrix.IsHadamard.hadamardSignedAdj_quadratic` (no Hypothesis 6.1 needed); `Matrix.IsHadamard.inner_hadamardPairs_self`, `_of_card_inter_eq_one`, `_of_disjoint`, `_one`, `.transpose_hadamardPairs_mul`, `.hadamardPairs_mulVec_one`, `.hadamardPairs_gram_sq`, `.hadamardPairs_orthogonal_of_mem`, `.eq_sum_inner_hadamardPairs`; `FourRowAgreement.hadamardSignedAdj_mem`, `.card_fourthRows`, `.dvd_card`; `.sixteen_dvd_of_agree_sixteenths`, `.lineSystem`, `.lineSystem_signedAdj`, `.card_adj_lineSystem`, `.card_component_row`, `.two_mul_card_component`, `.component_rootType`, `.component_cases`, `.not_component_E₇`; `LineSystem.An.not_card_pairwise_orthogonal`, `LineSystem.Dn.even_of_card_pairwise_orthogonal` |
| C16 (`Computations/C16*`; tagged in the remark at the end of `blueprint/sec6-hadamard.tex`) | `Computations.C16.h2`, `h4`, `h8`, `h16` (Sylvester), `h12` (Paley), with `h2_isHadamard`, ..., `h16_isHadamard`; the checker `Computations.C16.checkFourRowAgreement_sound`; `h12_fourRowAgreement` ($x=4$), `h2_fourRowAgreement`, `h4_fourRowAgreement`, `h8_fourRowAgreement`, `h16_fourRowAgreement` ($x=n$), bundled in `Computations.C16.fourRow_agreements`; `h12_transpose_hadamardPairs_mul` ($72I-6J$, from the general `Matrix.IsHadamard.transpose_hadamardPairs_mul`); the 66 lines of $H_{12}$: `h12_root_mem_hyperplane`, `h12_hyperplane_finrank`, `h12HyperplaneIsometry` ($\mathbf j^\perp\cong\mathbb R^{11}$), `h12_lines_injective`, `h12_numLines`, `h12_line_angles` ($90^\circ$ or $\arccos(1/3)$), `h12_inner_values_attained` |
| side claims of Section 6 (`LineGraphs/SideClaims/`; the remark after `lem:6-P` and the last remark of `blueprint/sec6-hadamard.tex`) | the spectra of $P^TP$ and $PP^T$ (`SideClaims/HadamardSpectra.lean`): `Matrix.IsHadamard.charpoly_transpose_hadamardPairs_mul`, `.charpoly_hadamardPairs_mul_transpose`, `.spectrumMultiset_transpose_hadamardPairs_mul`, `.spectrumMultiset_hadamardPairs_mul_transpose`, `.eigenvalueMultiplicity_…` and `.finrank_eigenspace_…` for the eigenvalues `zero` and `half_sq` ($\frac12n^2$); the Sylvester matrices (`SideClaims/Sylvester.lean`): `Matrix.sylvester` (the closed form $(-1)^{a\cdot b}$, reindexed from `Matrix.sylvesterZMod` by `Matrix.sylvesterEquiv`), `Matrix.sylvesterKronecker` and `Matrix.sylvesterKronecker_eq_sylvester`, `Matrix.sylvester_succ`, `Matrix.isHadamard_sylvester`, Hypothesis 6.1 with $x=n$ `Matrix.sylvester_fourRowAgreement`, the row products `Matrix.hadamardRowProduct_sylvester`, the Sylvester case `Matrix.sylvester_lines` (with `Matrix.image_hadamardRowProduct_sylvester`, `.card_image_…`, `.two_mul_card_filter_…`, `.inner_hadamardRowProduct_sylvester_of_ne`), and the matrices of C16, `Computations.C16.h2_eq_sylvester`, ..., `h16_eq_sylvester` |

### The note [Exc]

The names of the note `exceptional/note/exceptional.tex` follow the rules above; they are listed,
in the order of the note, in `LineGraphs/Exceptional/Audit.lean`.

| Item | Lean name |
| --- | --- |
| a canonical form exists | `SimpleGraph.CanonicalForm.ofChoice` (`Exceptional/CertificateExistence.lean`), so that Theorem 3.6 and the lists of Theorem C.1, which quantify over a `SimpleGraph.CanonicalForm`, are not vacuous |
