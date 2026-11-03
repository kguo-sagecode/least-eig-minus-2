# Prerequisites

This file lists every result from outside [CGSS] that the formalization needs. For each result
we give a statement in our notation, the place where a proof can be found, and what that proof
uses, followed down until only facts that Mathlib has, or that we prove ourselves, remain. The
blueprint cites the entries by their labels, such as SR3 or LN6.

This file is the summary of our working notes on the sources, which are not part of the
repository; where an entry says that we checked a claim numerically, the check was made there.
We wrote it before the blueprint and the Lean; they follow the routes chosen here (§13), and
`dependency-diagram.md`, at the top of the repository, gives the Lean declarations.

## 1. Conventions

### Sources

| Label | Source |
| --- | --- |
| [CGSS] | P. J. Cameron, J. M. Goethals, J. J. Seidel and E. E. Shult, Line graphs, root systems, and elliptic geometry, *J. Algebra* **43** (1976), 305–327 |
| [BCN] | A. E. Brouwer, A. M. Cohen and A. Neumaier, *Distance-Regular Graphs*, Springer, 1989 |
| [BvM] | A. E. Brouwer and H. Van Maldeghem, *Strongly Regular Graphs*, Cambridge University Press, 2022 |
| [HC54] | M. Hall and W. S. Connor, An embedding theorem for balanced incomplete block designs, *Canad. J. Math.* **6** (1954), 35–41 |
| [HR65] | A. J. Hoffman and D. K. Ray-Chaudhuri, On the line graph of a symmetric balanced incomplete block design, *Trans. Amer. Math. Soc.* **116** (1965), 238–252 |
| [LS73] | P. W. H. Lemmens and J. J. Seidel, Equiangular lines, *J. Algebra* **24** (1973), 494–512 |
| [S68] | J. J. Seidel, Strongly regular graphs with (−1,1,0) adjacency matrix having eigenvalue 3, *Linear Algebra Appl.* **1** (1968), 281–298 |
| [Sh59] | S. S. Shrikhande, The uniqueness of the L₂ association scheme, *Ann. Math. Statist.* **30** (1959), 781–798 |
| [Y25] | K. Yoshino, Enumeration of sets of equiangular lines with common angle arccos(1/3), *Discrete Math.* **348** (2025), 114647 |
| [C17] | P. J. Cameron, *Eigenvalues and root systems in finite geometry*, lecture notes, 2017, [PDF](https://cameroncounts.wordpress.com/wp-content/uploads/2017/06/fg.pdf) |

We cite each source by the numbers of its results and sections, and the journal articles also by
page. We checked every formula that we rely on against the printed source, with two exceptions.
We read [BvM] in the authors' revised version of 2024, whose section numbers agree with those of
the printed book, and [BCN] in a copy, without its figures, that we could not compare with the
printed book; §11 says where this matters.

### Tags

- **[M]** Mathlib has it. We give the name, checked against Mathlib at commit `082e2d37`
  (4 September 2026), the version pinned in `lake-manifest.json`.
- **[S]** A standard fact that we prove; the entry says how.
- **[P]** Proved in the source cited. We follow that proof, with the repairs listed.
- **[St]** Stated in the source cited, without a proof or with steps left out.
- **[new]** Our own argument, not found in any of the sources. Each is written out in full as a
  structured proof in the blueprint, and those that involve a computation were also checked
  numerically on the relevant examples.
- **[K]** A finite computation that the kernel checks; the numbers C1–C24 are those of the list
  in `cgss/certificates/README.md`, and §12 describes C20–C24.

### Notation

We follow `cgss/notation.md`. Graphs are $X$, $Y$, $Z$, with $n$ vertices, and a regular graph has
valency $k$ ([CGSS] writes $d$ in Theorem 4.4). A strongly regular graph has parameters
$(n,k,a,c)$, and its eigenvalues are $k>\theta_1>\theta_2$ with multiplicities $1$, $m_1$, $m_2$
([BvM] and [BCN] write $(v,k,\lambda,\mu)$, $r>s$ and $f,g$). We write $A=A(X)$ with entries
$A(u,w)$, $J$ for the all-ones matrix and $\mathbf j$ for the all-ones vector. A family
$(\mathbf x_u)$ of vectors *represents* $X$ if its Gram matrix is $2I+A$.

A set of lines at 60° and 90° is recorded, as in the blueprint, by the set $\Phi$ of vectors of
squared norm 2 on its lines, taken with both signs. For $\mathbf r\in\Phi$ we will write

$$
N_{\mathbf r}(\Phi)=\{\mathbf u\in\Phi:(\mathbf u,\mathbf r)=1\}.
$$

If $\Phi$ is star-closed, then $\mathbf u\mapsto\mathbf r-\mathbf u$ is an involution of
$N_{\mathbf r}(\Phi)$ without fixed points, and $(\mathbf u,\mathbf r-\mathbf u)=-1$; we will call
its orbits the *pairs* of $N_{\mathbf r}(\Phi)$. We write $T(m)=L(K_m)$, $L_2(m)=L(K_{m,m})$, and
$CP(m)$ for the cocktail party graph on $2m$ vertices. The design parameters $(v,k,b,r,\lambda)$
appear only in §8, as in Section 5 of [CGSS].

## 2. The answer in brief

We need nothing further for the core of the project. Every result that [CGSS] cites, calls well
known, or asserts is proved in one of the sources of §1, or is standard, or has a proof of ours;
each of our proofs that involves a computation has been checked numerically.

- **Proved in the sources**, with repairs of our own where noted:
  - the classification of generalized quadrangles with lines of size 3 ([BCN] Theorem 1.15.2),
    which together with Lemma 2.8 gives Lemma 2.10;
  - Smith's theorem ([BCN] Theorem 3.2.5) and the Perron–Frobenius facts behind it, which give
    Theorem 3.8;
  - the Hall–Connor embedding at $k=5$ ([HC54] Theorem 3.2, with the lemmas it takes from
    Connor (1952) reproved) and the even case of the Bruck–Ryser–Chowla theorem ([BvM]
    Theorem 8.3.1), which give Remark 5.12;
  - the relative bound for equiangular lines ([LS73] Theorem 3.6), used in Theorem 4.4.
- **Our own arguments**, needed because none of the sources has a complete proof:
  1. Theorem 4.4 cites [LS73] for two facts about lines at angle $\arccos\frac13$, one of which
     [LS73] does not state. Both follow from the relative bound and a cone construction through
     Theorem 3.5, which we take from [Y25] (EQ1–EQ3). The same argument proves the remark after
     Theorem 4.4, which [CGSS] does not prove (errata, Gap 7).
  2. Remark 4.14, Seidel's seven graphs. None of [S68], [BvM] and [BCN] gives a complete
     computer-free proof: Seidel cites Chang and his own 1967 paper, Brouwer and Van Maldeghem
     assume the uniqueness theorems, and [BCN] relies on a computer enumeration (Proposition
     3.11.2). We will follow the computer-free part of [BCN] (the proof of Theorem 3.12.2) in the
     language of line systems, and replace the enumeration by three short switching arguments
     (§7.3).
  3. Theorem 3.12 has no proof in [CGSS] or in any of the sources. We give one (RS3).
  4. Remark 3.11 needs the classification of the root systems with two root lengths. None of the
     sources contains it, and Mathlib has only its first step (RS1, RS2).
  5. The gaps in Lemma 2.10, Theorem 4.13 and Remark 4.12 (errata, Gaps 1–3 and 9).
- **Not needed**, although the paper or its sources lean on them: Chang's two papers; Seidel's
  1967 paper ([BCN] reference 652); Connor (1952); Hoffman (1963, 1965); the pillar theorems of
  [LS73] (an optional second route, EQ4); Yoshino's enumeration; the absolute bound and the Krein
  conditions (in the $E_8$ setting, Theorems 4.3 and 4.4 cover every use that [BvM] makes of
  them); and the two-graph theory of [BvM] §8.10.

Our choices of routes are recorded in §13. The side claims that would need further sources
(Norman's theorem, [CGSS] reference 17; the uniqueness of the Hadamard matrix of order 12;
Shult's characterization, [CGSS] reference 24) are outside the scope: they are results of other
papers, which [CGSS] mentions but neither proves nor uses.

## 3. Map from the paper to the prerequisites

| [CGSS] item | needs from outside the paper | entries | status |
| --- | --- | --- | --- |
| Lemmas 2.3–2.9, 2.12 | Gram matrices and isometries | LA1–LA3 | [M], [S] |
| Lemma 2.10 | quadrangles with lines of size 3 | GQ1–GQ3 | [P] [BCN] 1.15.2, with repairs |
| Def. 3.3, Thm. 2.13 | transitivity on roots | LN5 | [S] |
| Thms. 3.5–3.7 | nothing | | internal; C2–C6 |
| Thm. 3.8 | Smith's theorem; symmetric Perron–Frobenius | SM1–SM3 | [P] [BCN] 3.2.5, [S] |
| Def. 3.9, Thm. 3.10 | root pairings | RS1 | [M] |
| Rem. 3.11 | root systems with two root lengths | RS1, RS2 | [M] for the first step, [S] |
| Thm. 3.12 | nothing | RS3 | [new] |
| §4, opening | Gram representations; extension and star closure | LA3, LN1–LN4 | [M], [S] |
| Thm. 4.3 | the space of symmetric matrices | LA5 | [S] |
| Thm. 4.4 | two facts about equiangular lines | EQ1–EQ3 | [P] [LS73] 3.6, [new] |
| remark after Thm. 4.4 (in the core) | the same | EQ3 | [new] |
| Thms. 4.10, 4.11 | nothing | | internal |
| Rem. 4.12 | nothing | | our proof of "it is easy to see" |
| Thm. 4.13 | two counts | SR1, LG1 | [S], [P] [BCN] 3.12.4 |
| Rem. 4.14 | the classification of §7.3 | SR1–SR5, SW1–SW4, LN3–LN7, SE1–SE7 | [new] assembly after [BCN] 3.12.2 |
| Lemmas 5.1–5.4 | spectra of regular graphs | SP1–SP4 | [M], [S] |
| Lemmas 5.5, 5.6, Thm. 5.8 | $MM^T$ and $M^TM$ | SP5, DS1 | [M], [S] |
| remark after Thm. 5.8 | Fisher's inequality | DS3 | [S] |
| Cor. 5.10 | the exception, explicitly | HR1 | [K] C13 |
| Cor. 5.10, uniqueness of the exception | a local analysis | HR2 | [new]; side claim |
| Rem. 5.12 | no 2-(15,5,2) design | DS1, DS2, DS5, HC1–HC6 | [P] [HC54], [S] |
| Ex. 5.13 | resolvable designs; two known designs | EX1–EX4 | [S], [K] |
| Thm. 6.2 | nothing | HD1 | internal |
| Section 6, background | Norman [17]; the uniqueness of $H_{12}$ | | not among the sources; side claims, outside the scope |
| Rem. 2.11 | Shult [24] | | not among the sources; side claim, outside the scope |

## 4. General tools

### 4.1 Linear algebra

**LA1. The rank of a Gram matrix.** The Gram matrix of $\mathbf x_1,\dots,\mathbf x_n$ has rank
equal to the dimension of their span. [S] Write it as $B^TB$ for the coordinate matrix $B$ in an
orthonormal basis of the span, and use `Matrix.rank_transpose_mul_self` [M].

**LA2. Equal Gram matrices.** Two families with the same Gram matrix differ by a linear isometry
between their spans, and the isometry extends to the ambient spaces when these have the same
dimension. [S], with `LinearIsometry.extend` [M] (`Analysis/InnerProductSpace/PiL2.lean`
l. 1176). LN4 applies it to line systems.

**LA3. Gram representations.** A real positive semidefinite matrix of rank $\rho$ is the Gram
matrix of vectors in $\mathbb R^\rho$. [M] `Matrix.posSemidef_iff_eq_sum_vecMulVec`
(`Analysis/InnerProductSpace/Positive.lean` l. 573), with
`Matrix.IsHermitian.spectral_theorem` and `Matrix.IsHermitian.rank_eq_card_non_zero_eigs`. This
is the opening of [CGSS] Section 4, and [BCN] Proposition 3.5.2.

**LA4. Positive semidefinite matrices.** If $M\succeq0$ and $\mathbf x^TM\mathbf x=0$ then
$M\mathbf x=0$; principal submatrices of positive semidefinite matrices are positive
semidefinite, with nonnegative determinants. [M] `Matrix.PosSemidef.submatrix`,
`Matrix.PosSemidef.det_nonneg`, `Matrix.posSemidef_iff_dotProduct_mulVec`. Used in HC3 and HR2.

**LA5. Symmetric matrices.** The real symmetric $\ell\times\ell$ matrices form a space of
dimension $\ell(\ell+1)/2$, the traceless ones a space of dimension $\ell(\ell+1)/2-1$, and
$(P,Q)\mapsto\operatorname{tr}(PQ)$ is an inner product on them. [S] with a basis indexed by
`Sym2 (Fin ℓ)` and `Sym2.card` [M] (`Data/Sym/Card.lean` l. 162); we did not find the dimension in
Mathlib. Used in Theorem 4.3, and in our alternative proof of Theorem 4.4 (EQ4).

**LA6. Idempotents, determinants and integrality.** An idempotent matrix has rank equal to its
trace: `LinearMap.IsProj.trace` with `LinearMap.isProj_range_iff_isIdempotentElem` [M]. The matrix
determinant lemma, which gives $\det(\alpha I+\beta J)=\alpha^{\ell-1}(\alpha+\ell\beta)$:
`Matrix.det_one_add_replicateCol_mul_replicateRow` [M] (`LinearAlgebra/Matrix/SchurComplement.lean`
l. 418). A rational root of a monic integer polynomial is an integer:
`isInteger_of_is_root_of_monic` [M] (`RingTheory/Polynomial/RationalRoot.lean` l. 115). For a
nonsingular integer matrix $B$ and an integer vector $\mathbf a$, the number
$\det(B)\,\mathbf a^TB^{-1}\mathbf a=\mathbf a^T\operatorname{adj}(B)\,\mathbf a$ is an integer
[S].

### 4.2 Spectra of graphs

**SP1. Regular graphs** ([CGSS] Lemma 5.1, "well known"). If $X$ is $k$-regular, then $k$ is its
largest eigenvalue and its multiplicity is the number of components. [P] [BCN] Proposition 3.2.2,
through Perron–Frobenius. We will use the Laplacian $kI-A$ instead:
`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` [M].

**SP2. Regularity from the spectrum** ([CGSS] Lemma 5.2). $X$ is regular if and only if
$\sum_i\lambda_i^2=n\lambda_{\max}$. [P] [BCN] Lemma 3.2.1 and Proposition 3.2.2:
expand $\mathbf j$ in an orthonormal basis of eigenvectors. Only the spectral theorem [M] is used.

**SP3. Bipartite graphs** ([CGSS] Lemma 5.3). A connected $k$-regular graph is bipartite if and
only if $-k$ is an eigenvalue. [P] [BCN] Proposition 3.2.3, through Perron–Frobenius.
We will use the signless Laplacian $kI+A=MM^T$ instead.

**SP4. Line graphs** ([CGSS] Lemma 5.4). If $Y$ is connected without isolated vertices and
$L(Y)$ is regular, then $Y$ is regular or bipartite and semiregular. [S], by counting; the first
paragraph of the proof of [BCN] Theorem 3.12.2 has the same argument.

**SP5. Incidence matrices.** For the vertex–edge incidence matrix $M$ of $Y$ we have
$MM^T=D+A(Y)$ and $M^TM=2I+A(L(Y))$, and $MN$, $NM$ have the same nonzero spectrum.
`SimpleGraph.incMatrix_mul_transpose`, `SimpleGraph.incMatrix_transpose_mul_diag` and
`Matrix.charpoly_mul_comm'` [M]; the identity for $M^TM$ we will build.

### 4.3 Strongly regular graphs

The source is [BvM] §§1.1.1–1.1.4, which gives short proofs.

**SR1. Basic identities.** $A^2=kI+aA+c(J-I-A)$, $AJ=kJ$ and $k(k-a-1)=c(n-k-1)$. [M]
`SimpleGraph.IsSRGWith.matrix_eq` and `SimpleGraph.IsSRGWith.param_eq`; the latter uses truncated
subtraction, so we will cast to $\mathbb Z$ early. `IsSRGWith` admits the empty and the complete
graphs (`SimpleGraph.bot_strongly_regular`, `SimpleGraph.IsSRGWith.top`), which our hypotheses
will exclude.

**SR2. Complements.** The complement has parameters $(n,n-k-1,n-2k+c-2,n-2k+a)$ and eigenvalues
$-1-\theta_2>-1-\theta_1$. [M] `SimpleGraph.IsSRGWith.compl`.

**SR3. Idempotents and multiplicities.** The eigenvalues $\theta_1,\theta_2$ are the roots of
$x^2-(a-c)x-(k-c)$. The matrices

$$
E_0=\tfrac1nJ,\qquad
E_1=\frac{A-\theta_2I-\frac{k-\theta_2}{n}J}{\theta_1-\theta_2},\qquad
E_2=\frac{A-\theta_1I-\frac{k-\theta_1}{n}J}{\theta_2-\theta_1}
$$

are the spectral idempotents, $A=kE_0+\theta_1E_1+\theta_2E_2$, and $m_i=\operatorname{rk}E_i=
\operatorname{tr}E_i$ satisfy $1+m_1+m_2=n$ and $k+m_1\theta_1+m_2\theta_2=0$. [S] from SR1 and
LA6; the spectral theorem is not needed. [BvM] §1.1.4.

**SR4. Least eigenvalue $-2$.** If $\theta_2=-2$, then $a=c+\theta_1-2$ and $k=c+2\theta_1$, so
$\theta_1=a-c+2$ is an integer; moreover $m_1=(2n-k-2)/(\theta_1+2)$ and
$\operatorname{rk}(2I+A)=1+m_1$. [S] from SR3; [BvM], proof of Theorem 1.1.1.

**SR5. Lemma P: the parameters in the $E_8$ setting.** Let $X$ be a connected strongly regular
graph with $\theta_2=-2$, $n\le36$, $k\le16$ and $\operatorname{rk}(2I+A)\le8$. Then $(n,k,a,c)$
is one of the following 15 sets:
- $(2m,2m-2,2m-4,2m-2)$ for $2\le m\le7$, the parameters of $CP(m)$;
- $(9,4,1,2)$ and $(16,6,2,2)$, those of $L_2(3)$ and $L_2(4)$;
- $(10,6,3,4)$, $(15,8,4,4)$, $(21,10,5,4)$ and $(28,12,6,4)$, those of $T(5)$ to $T(8)$;
- $(10,3,0,1)$, $(16,10,6,6)$ and $(27,16,10,8)$.

[new], a finite search (computation C18): SR4, the integrality of $m_1$ and the counting condition
$2k-c\le n-2$ (two non-adjacent vertices have $2k-c$ neighbours between them, all among the
other $n-2$ vertices; without it $(21,16,12,12)$, with eigenvalues $16$, $2^6$, $(-2)^{14}$,
survives) leave 30 parameter sets with $n\le36$, of which 16 have $m_1\le7$, and $k\le16$
excludes $(28,18,12,10)$. The blueprint (`blueprint/sec4-remark414.tex`, the parameter lemma)
proves $k-2a+c=4$, $2k-c\le n-2$, $1\le c$ and $(a-c+4)(\operatorname{rk}(2I+A)-1)=2n-k-2$
without the spectral theorem.
The hypotheses hold when $X$ is represented in $E_8$, by Theorems 4.3 and 4.4 and LA1.

**SR6. Not needed: the absolute bound and the Krein conditions.** [BvM] Theorem 1.1.1
uses the absolute bound $n\le m_1(m_1+3)/2$ four times; [BvM] Proposition 1.3.14 only cites
Brouwer and Haemers for it. In the $E_8$ setting Theorems 4.3 and 4.4 exclude all four cases.
Should the general form of [BvM] Theorem 1.1.1 ever be wanted,
[BCN] Theorem 3.6.1 proves the bound for spherical two-distance sets with a short
polynomial argument, which can also be written as a rank bound.

### 4.4 Seidel switching

The sources are [BvM] §1.1.11 and [BCN] §3.8; Mathlib has none of this.

**SW1. Switching.** For $Y\subseteq V(X)$, the graph $X^Y$ keeps the pairs inside $Y$ and inside
$V\setminus Y$, and complements the pairs between them. Then $X^Y=X^{V\setminus Y}$,
$(X^Y)^Z=X^{Y\triangle Z}$, and $\sigma(X)^{\sigma(Y)}=\sigma(X^Y)$ for every bijection $\sigma$.
[S]

**SW2. The Seidel matrix.** $S(X)=J-I-2A$ satisfies $S(X^Y)=D_YS(X)D_Y$, where $D_Y$ is diagonal
with $-1$ on $Y$ and $1$ elsewhere. [S] ([CGSS] Corollary 5.10 uses $2A-J+I=-S(X)$.)

**SW3. Degrees after switching.** For $u\in Y$,
$\deg_{X^Y}(u)=\deg_X(u)-2\lvert N(u)\setminus Y\rvert+\lvert V\setminus Y\rvert$, and
symmetrically for $u\notin Y$. [S] For regular $X$ this is the criterion of [BvM] §1.1.11.

**SW4. Switching by vectors.** If $\lvert\mathbf h\rvert^2=2$ and $(\mathbf h,\mathbf x_u)=1$ for
all $u$, then replacing $\mathbf x_u$ by $\mathbf h-\mathbf x_u$ for $u\in Y$ gives a family
representing $X^Y$. [S] This is how [CGSS] switches in Examples 4.5, 4.7 and 4.9, and how §7.3
uses switching.

### 4.5 Line systems

**LN1. Finiteness.** If a set of lines at 60° and 90° in a space of dimension $\ell$ contains a
basis $\mathbf b_1,\dots,\mathbf b_\ell$ of the space, then $\mathbf x\mapsto((\mathbf x,
\mathbf b_i))_i$ is injective into $\{-2,\dots,2\}^\ell$, so the set is finite. In the same way,
the ℤ-span of finitely many vectors with integral inner products contains only finitely many
vectors of bounded norm. [S]

**LN2. Extension inside the span.** Every set of lines at 60° and 90° in a space $V$ lies in a
maximal one in $V$, which is star-closed by Lemma 2.3. [S] from LN1. This is the first paragraph
of [CGSS] Section 4 (p. 315), in the form that keeps the ambient space.

**LN3. Star closure.** Let $\Sigma$ be a finite set of vectors of squared norm 2 with pairwise
inner products in $\{0,\pm1\}$. The smallest star-closed set $R\supseteq\Sigma\cup-\Sigma$ is
finite, is a set of lines at 60° and 90°, lies in the ℤ-span of $\Sigma$, spans the same space as
$\Sigma$, and is indecomposable if the graph of nonzero inner products on $\Sigma$ is connected.
[S] Here $\lvert\mathbf r+\mathbf s\rvert^2=2$ when $(\mathbf r,\mathbf s)=-1$; inner products stay
integral, and by Cauchy–Schwarz the value $\pm2$ occurs only for $\pm$ the same vector; LN1 gives
finiteness; and an orthogonal splitting of a star-closed set splits it into star-closed parts.

**LN4. Isometries.** An isomorphism of line systems extends to a linear isometry of their spans
(LA2), so it preserves ranks, the sets $N_{\mathbf r}$ and their pairs.

**LN5. Transitivity on roots.** If $\Phi$ is star-closed and indecomposable, its isometries act
transitively on $\Phi$. [S] For $(\mathbf r,\mathbf s)=1$, the reflection in $\mathbf r-\mathbf s$
maps $\mathbf r$ to $\mathbf s$; for $(\mathbf r,\mathbf s)=-1$, compose the reflections in
$\mathbf r+\mathbf s$ and in $\mathbf s$; reflections in vectors of $\Phi$ preserve $\Phi$ ([CGSS]
Theorem 3.10); and indecomposability joins any two vectors by a chain of non-orthogonal ones.
[BCN] Proposition 3.10.1 is the same argument for root lattices. LN5 fills Gap 5 of the
errata (the choice of line in Definition 3.3), and §7.3 uses it.

**LN6. Counts in the models.** [K] (computation C20) In $A_\ell$, $D_\ell$, $E_6$, $E_7$ and
$E_8$, every vector $\mathbf r$ has $\lvert N_{\mathbf r}\rvert=2(\ell-1)$, $4(\ell-2)$, 20, 32 and
56, that is, $\ell-1$, $2(\ell-2)$, 10, 16 and 28 pairs; these are the diagonal of $C^2$ in
Theorem 3.7 (with 28 for $E_8$, Error 1 of the errata). Take the model of [CGSS] Definition 3.2
(ii), whose vectors are $\pm\mathbf e_i\pm\mathbf e_j$ and $\frac12\sum_i\epsilon_i\mathbf e_i$
with $\epsilon_i=\pm1$ and $\prod_i\epsilon_i=1$ (as in [BCN] §3.10, (iii)), and put
$\mathbf c=\frac12\sum_{i=1}^8\mathbf e_i$, $E_7=E_8\cap(\mathbf e_7-\mathbf e_8)^\perp$ and
$E_6=E_7\cap(\mathbf e_6-\mathbf e_7)^\perp$. These are the systems of Definition 3.3, orthogonal
to a line and to a star, and they contain $\mathbf c$. Then the pairs of
$N_{\mathbf c}$ are the pairs
$\{\mathbf e_i+\mathbf e_j,\ \mathbf c-\mathbf e_i-\mathbf e_j\}$, where $\{i,j\}$ runs over
the edges of $K_8$ for $E_8$, over the edges of $K_6$ together with $\{7,8\}$ for $E_7$, and
over the edges of $K_5$ for $E_6$. We checked all of these numerically, and computation C20
checks them in the kernel.

**LN7. Simple roots.** [K] (computation C21) Each of the models $E_6$, $E_7$, $E_8$ of LN6
contains a basis of its span that consists of roots and has Gram matrix of determinant 3, 2 and 1
respectively; up to order these Gram matrices are `CartanMatrix.E 6`, `CartanMatrix.E 7` and
`CartanMatrix.E 8` [M] (`LinearAlgebra/Matrix/Cartan.lean`; the names `CartanMatrix.E₆` and so on
are deprecated aliases). [BCN] §3.10, (iii)–(v), gives such bases
for its own models, together with the dual lattices. We found bases in our models
(computation C21).

### 4.6 Designs

The sources are [BvM] §6.2 and §8.3.1, and [HC54]. Mathlib has no designs (only projective planes, in
`Combinatorics/Configuration.lean`).

**DS1. Designs with repeated blocks.** A 2-$(v,k,\lambda)$ design will be an incidence structure
whose blocks are labels rather than sets, since [CGSS] Corollary 5.9 uses the trivial design with
repeated blocks. Then $bk=vr$ and $r(k-1)=\lambda(v-1)$, and the incidence matrix satisfies
$NN^T=(r-\lambda)I+\lambda J$, $JN=kJ$ and $NJ=rJ$. [S], double counting.

**DS2. Complements.** The complement of a 2-$(v,k,\lambda)$ design with $b$ blocks and
replication number $r$ is a 2-$(v,v-k,b-2r+\lambda)$ design. [S] [BvM] §8.5 (under
"Complement") states this for quasi-symmetric designs. [CGSS] Remark 5.12 uses it for $(15,10,21,14,9)$.

**DS3. Fisher's inequality.** If $r>\lambda$ then $b\ge v$: $\det(NN^T)=rk(r-\lambda)^{v-1}\ne0$
by LA6, so $v=\operatorname{rk}(NN^T)\le\operatorname{rk}N\le b$. [S] It is not in [BvM]. Used in
the remark after Theorem 5.8.

**DS4. Incidence and flag graphs.** $I(D)$, and $F(D)=L(I(D))$, as in [CGSS] p. 323, on top of
SP5.

**DS5. The instance of Bruck–Ryser–Chowla.** There is no integer $22\times22$ matrix $M$ with
$MM^T=5I+2J$: $\det(M)^2=\det(5I+2J)=5^{21}\cdot49$, whose 5-adic valuation is odd. [P] [BvM]
Theorem 8.3.1 (the even case is sketched right after the statement), with `Matrix.det_mul`,
`Matrix.det_transpose`, LA6, `padicValNat.mul` and `padicValNat.pow` [M]. Computation C19.

## 5. Section 2: generalized quadrangles with lines of size 3

Lemma 2.8 shows that the graph on $\Gamma_a$ has the triangle property: every edge lies in a
triangle, and every further vertex is adjacent to exactly one vertex of that triangle. The
triangles are then the lines of a generalized quadrangle with lines of size 3, possibly
degenerate, and Lemma 2.10 is the classification of these.

**GQ1. Parameters.** The collinearity graph of a generalized quadrangle of order $(2,t)$ is
strongly regular with parameters $(3(2t+1),2(t+1),1,t+1)$. Conversely, every strongly regular
graph with these parameters is such a collinearity graph, with the triangles as lines. [St]
[BCN] Lemma 1.15.1 ("Proof. Straightforward."). [S] For the converse: since $a=1$, each
edge lies in exactly one triangle, and a vertex off a triangle is adjacent to at most one of its
vertices; the $3(k-2)=n-3$ edges leaving a triangle then reach every other vertex exactly once.

**GQ2. The classification.** A generalized quadrangle with lines of size 3 is a coclique, a set of
$2m+1$ points on $m$ lines through one point, or one of $Q_1$, $Q_2$, $Q_4$, of orders $(2,1)$,
$(2,2)$ and $(2,4)$, with 9, 15 and 27 points. [P] [BCN] Theorem 1.15.2 gives four
proofs:
- the first builds $Q_1\subset Q_2\subset Q_4$ by hand, and its labelling figure is
  missing from our copy;
- the second studies an auxiliary graph whose components are copies of $K_{3,3}$;
- the third (after Cameron) labels the points by vectors in $\{0,1\}^{t+1}$, and obtains
  finiteness first; it says that a certain graph is "a triangle-free double cover of $K_4$ and
  hence $K_{4\times2}$", but the triangle-free double cover of $K_4$ is the cube, $K_{4,4}$ minus a
  perfect matching, whereas $K_{4\times2}$ contains triangles (a slip, or an error of our copy);
- the fourth uses quadratic forms over $\mathbb F_2$ and classical geometry.

Each of them leaves steps to the reader. The blueprint uses our repair of Lemma 2.10 instead
(errata, Gaps 1–3); the third proof, written out in full, would also do. Both are [new] in their
details, and both were checked on the three quadrangles.

**GQ3. What depends on it.** Lemma 2.10, with Lemma 2.8. Through GQ1 and SR2, also the uniqueness
of the strongly regular graphs with parameters $(9,4,1,2)$, $(15,6,1,3)$ and $(27,10,1,5)$, and so
of $L_2(3)$, of $T(6)$ (the complement of $(15,6,1,3)$), and of the Schläfli graph (the complement
of $(27,10,1,5)$; SE3). [BCN] §3.10 ("Another proof of the classification") uses GQ2 to reprove
the classification of root lattices, in the style of [CGSS]. The Petersen graph, which appears inside the proof of
Lemma 2.10 for $k=5$, is SE1.

## 6. Section 3

### 6.1 Theorem 3.8: the graphs with largest eigenvalue 2

[CGSS] derives Theorem 3.8 from the root systems: "From the realizations ... we easily write down
the possible sets of vectors" (p. 313). This hides an enumeration (errata, Gap 6). We use
Smith's argument, as given in [BCN], instead (decision 4 of §13).

**SM1. Monotonicity.** If $X$ is connected and $Y$ is a proper subgraph of $X$ (fewer vertices or
fewer edges), then $\lambda_{\max}(Y)<\lambda_{\max}(X)$; and a connected graph has a positive
eigenvector for its largest eigenvalue. [P] [BCN] Theorem 3.1.1 (v) and Proposition
3.2.4. The proof there is for general nonnegative matrices and uses compactness. For
symmetric matrices we will prove it from the Rayleigh quotient: if $\mathbf x$ is a unit
eigenvector of $Y$ for $\lambda_{\max}(Y)$, then $\lvert\mathbf x\rvert$, extended by zeros, has
Rayleigh quotient at least $\lambda_{\max}(Y)$ for $X$, and equality forces it to be a positive
eigenvector of $X$. [S], with `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
the rest of `Analysis/InnerProductSpace/Rayleigh.lean` [M]. Mathlib has no Perron–Frobenius
theorem.

**SM2. The Smith graphs.** The cycles $\tilde A_\ell$ and the graphs $\tilde D_\ell$, $\tilde E_6$,
$\tilde E_7$, $\tilde E_8$ have eigenvalue 2, with the positive eigenvectors of [BCN] 3.2.5 (the
figure is missing from our copy; compare [CGSS] Figure 1). [K] Computation C17.

**SM3. Smith's theorem.** [P] [BCN] Theorem 3.2.5: the connected graphs with largest
eigenvalue 2 are the Smith graphs. Its proof reduces to the claim that every connected graph
either contains a Smith graph as a subgraph or is a subgraph of one, which "by considering the
possible valencies ... it is easy to show". We will write this step out [S]: a connected graph
with no subgraph $\tilde A_\ell$ or $\tilde D_\ell$ is a tree with no vertex of degree 4 or more
and at most one of degree 3; if it also contains none of $\tilde E_6$, $\tilde E_7$, $\tilde E_8$,
its arms are those of $A_\ell$, $D_\ell$, $E_6$, $E_7$ or $E_8$, and each of these is a proper
subgraph of a Smith graph (compare `Mathlib/NumberTheory/ADEInequality.lean`). SM1 then finishes
the proof.

### 6.2 Remark 3.11 and Theorem 3.12

**RS1. Root pairings.** Mathlib's `RootPairing`, with `RootPairing.IsRootSystem`,
`IsCrystallographic`, `IsReduced` and `IsIrreducible` [M], provides the
bridge of Definition 3.9 and Theorem 3.10. The pairing is built by hand from the finite set Φ
(`cgss/proofs/remark311/remark311.tex`, Lemma 9.1): `RootPairing.ofBilinear` takes all reflective
vectors of a form, which over ℝ is every nonzero vector, not a given finite Φ. Mathlib also proves that a reduced irreducible
crystallographic root system has roots of at most two lengths
(`RootPairing.InvariantForm.exists_apply_eq_or` and `RootPairing.forall_pairing_eq_swap_or`, in
`LinearAlgebra/RootSystem/Finite/Lemmas.lean`), it has the Cartan matrices of all types
(`CartanMatrix.B`, `CartanMatrix.C`, `CartanMatrix.F₄`, `CartanMatrix.G₂`, and so on), and it
treats $G_2$ in `LinearAlgebra/RootSystem/Finite/G2.lean`.

**RS2. Two root lengths.** Remark 3.11 says that the results of [CGSS] complete the
classification of the Root Systems of Definition 3.9, that is, of the root systems of Lie theory,
including those with two root lengths. It lists the new ones as sets of lines: $B_\ell$ and
$C_\ell$ (which give the same lines), $F_4$ and $G_2$, each with its number of lines and its
matrix equation. The only argument given is that the roots of each length form a Root System,
and so a sum of systems of types $A$, $D$, $E$ by Theorem 3.10, after which "This readily leads to
the remaining indecomposable Root Systems". None of the sources proves the classification ([BCN]
§3.10 treats one root length only, and [C17] §3.5 sketches the argument of [CGSS]). Mathlib has
much of the standard proof: the existence of a base (`RootPairing.nonempty_base`), the Cartan
matrix of a base, the fact that it is a finite-type Cartan matrix
(`RootPairing.Base.cartanMatrix_isFiniteCartan`, with `Matrix.IsFiniteCartan`), and the fact that
a root system is determined by its Cartan matrix (`RootPairing.Base.equivOfCartanMatrixEq`),
besides RS1. What it lacks is the list of the connected finite-type Cartan matrices. The choice of
route is decision 5 of §13; the explicit part of the remark (the four systems, their numbers of
lines and their matrix equations) is a computation in any case. The proof is
`cgss/proofs/remark311/remark311.tex`.

**RS3. Theorem 3.12.** [new] Neither [CGSS] ("we can prove the following theorem") nor any of
the sources has a proof. We propose the following one; it does not use RS2.
- *If.* Given the partition $\mathcal P\cup\mathcal Q$, take vectors of squared norm 2 on the lines
  of $\mathcal P$ and of squared norm 4 on the lines of $\mathcal Q$. The angle conditions make
  every inner product an integer: $(\mathbf p,\mathbf p')\in\{0,\pm1\}$,
  $(\mathbf p,\mathbf q)\in\{0,\pm2\}$ and $(\mathbf q,\mathbf q')\in\{0,\pm2\}$, which are even
  whenever a vector of $\mathcal Q$ is involved. Let $\Phi$ be the closure of these vectors under
  the reflections $\tau_{\mathbf r}$ of Definition 3.9 (c). By induction, $\Phi$ lies in the
  ℤ-span $L$ of the given vectors, its vectors have squared norm 2 or 4, and each vector of squared
  norm 4 in $\Phi$ has even inner product with every vector of $L$. Thus $\Phi$ satisfies (a) of
  Definition 3.9, it satisfies (b) since $\sqrt2$ is irrational, and it is finite by LN1. Adding
  a system $A_1\oplus\dots\oplus A_1$ on the orthogonal complement of its span gives a Root
  System in $\mathbb R^n$ whose lines contain the given ones.
- *Only if.* Suppose the lines lie among those of a Root System, and take the root on each line.
  Condition (a) of Definition 3.9 forces roots on lines at 60° to have equal lengths, and roots on
  lines at 45° to have lengths in ratio $\sqrt2$. Thus, on each component of the graph whose edges
  are the pairs of lines at 60° or 45°, the squared lengths are $\beta2^j$ for a fixed
  $\beta$ and integers $j$; put the lines with $j$ even in one part and those with $j$ odd in the
  other.

Both directions are written out in `cgss/proofs/thm312/thm312.tex`, which replaces the closure under
reflections by an explicit set of vectors of the ℤ-span, and checks the result on the systems
$B_\ell$, $C_\ell$ and $F_4$.

## 7. Section 4

### 7.1 Theorem 4.4 and the remark after it

The proof of Theorem 4.4 in [CGSS] (pp. 317–318) combines Theorem 3.7, a positive semidefiniteness
inequality, and two facts that it takes from [LS73]: that $\mathbb R^8$ holds at most 28 lines at
angle $\arccos\frac13$, which we call (B8), and that any 28 such lines span only 7 dimensions,
which we call (F). As printed ("any set of 28 equiangular lines lies in $\mathbb R^7$"), (F) is
false: a single full pillar in the sense of [LS73] gives 28 lines at $\arccos\frac13$ that span
$\mathbb R^{15}$ (the one-pillar construction in the proof of [LS73] Theorem 4.5, pp. 505–506,
with $r=15$). It is true for lines in $\mathbb R^d$ with $d\le14$, in particular
in $\mathbb R^8$, where [CGSS] uses it. [LS73] states (B8) (Theorem 4.5), but not (F).

**EQ1. The relative bound.** Lines in $\mathbb R^\ell$ at angle $\arccos\alpha$, with
$\alpha^2\ell<1$, number at most $\ell(1-\alpha^2)/(1-\alpha^2\ell)$. For $\alpha=\frac13$ this is
16 in $\mathbb R^6$ and 28 in $\mathbb R^7$. [P] [LS73] Theorem 3.6, from
$(\operatorname{tr}M)^2\le\operatorname{rk}(M)\operatorname{tr}(M^2)$ for the Gram matrix $M$ of
unit vectors on the lines [S].

**EQ2. Lines spanning 8 dimensions.** [new] If lines at angle $\arccos\frac13$ span a space $U$ of
dimension 8, there are at most 14 of them. Take unit vectors $\mathbf v_i$ on the lines, and in
$U\oplus\mathbb R\mathbf e$ put $\mathbf r=\sqrt2\,\mathbf e$ and
$\mathbf u_i=\sqrt{3/2}\,\mathbf v_i+\mathbf e/\sqrt2$. These vectors have squared norm 2, and
$(\mathbf u_i,\mathbf r)=1$ and $(\mathbf u_i,\mathbf u_j)\in\{0,1\}$ for $i\ne j$; together they
span 9 dimensions. Their star closure (LN3) is indecomposable of rank 9, so it is isomorphic to
$A_9$ or $D_9$ by Theorem 3.5, and the $\mathbf u_i$ lie in distinct pairs of $N_{\mathbf r}$, of which
there are 8 or 14 (LN6). The idea is the switching root of [Y25] §4, where EQ2 is implicit in
Theorem 6.1; [Y25] rests on the classification of root lattices, for which Theorem 3.5 stands in
here.

**EQ3. (B8), (F) and the remark.** By EQ1 and EQ2, lines at $\arccos\frac13$ in $\mathbb R^8$
number at most 28, and 28 of them span 7 dimensions. The proof of Theorem 4.4 in [CGSS] is then
complete as written, once Theorem 3.7 is read with $(C-28I)$ for $E_8$, "Lemma 3.7" as Theorem
3.7, and "contained in $E_7$ or $D_7$" as "in $A_7$, $D_7$ or $E_7$", which changes nothing since
$A_7\subset E_7$. The remark "There is no regular graph with $n=28$, $d=16$ contained in $E_8$"
follows as well. For such a graph, a trace and Cauchy–Schwarz computation shows that
$\operatorname{rk}(2I+A)=8$, so the matrix $I+\frac23A-\frac13(J-I)$ of [CGSS] gives 28 lines at
$\arccos\frac13$ that span 8 dimensions, which EQ2 forbids (computation C24). [new]. By decision
2 of §13, the remark is in the core. In the blueprint (the remark after Theorem 4.4) the rank $\operatorname{rk}(2I+A)=8$ comes from the trace form of C24, $(\operatorname{tr}N)^2\le\operatorname{rk}N\sum N(u,w)^2$ for $N=2I+A-\frac9{14}J$, and needs no eigenvalue multiplicities.

**EQ4. Other routes, not needed.**
- The pillar argument of [LS73] Theorem 4.5 proves (B8), and with one further
  equality step of ours it proves (F) for $d\le14$; it avoids Theorem 3.5.
- [Y25] Theorem 6.1 with Lemma 5.5 contains EQ2, but relies on the classification of root
  lattices (cited from Ebeling) and on a corollary of Cao, Koolen, Munemasa and Yoshino (2021),
  neither among our sources.
- Our traceless argument, through LA5, proves Theorem 4.4
  without (B8) and (F), except for $(n,k)=(28,16)$. By decision 1 of §13 we do not use it.
- [BCN] Theorem 3.12.2 implies Theorem 4.4 and the remark, by the lattice argument that
  §7.3 uses.

### 7.2 Theorem 4.13

**LG1. The line graph case.** Two steps of the proof need filling (errata, Gap 9).
- "Since this number is a constant, it must be 2." Let $Y$ be connected, triangle-free and regular
  of valency $h\ge3$, and suppose that every two disjoint edges of $Y$ are joined by exactly $c$
  edges. If $c=0$, then $L(Y)$ is a connected strongly regular graph with $c=0$, and so complete,
  which is impossible. If $c=1$, count the edges disjoint from a fixed edge: there are
  $2(h-1)^2$ of them, so $\lvert E(Y)\rvert=2h^2-2h+1$, and $\lvert V(Y)\rvert=4h-4+2/h$ is not an
  integer. [new] count; [St] the proof of [BCN] Theorem 3.12.4 says only "if $\mu=1$ then
  $\Delta$ has girth $\ge5$ and must be the pentagon". Then $c=2$ forces $Y=K_{h,h}$, as
  in the same proof ("a maximal $K_{m,n}$ subgraph of $\Delta$ agrees with $\Delta$").
- The bipartite case, "by similar reasoning": [P] the proof of [BCN] Theorem 3.12.4.

The printed count "$v-2$ or $v-1$ according as $\{j,k\}$ is an edge or not" is reversed (errata,
Error 7); the argument is unaffected.

### 7.3 Remark 4.14: Seidel's seven graphs

[CGSS] Remark 4.14 says: "Seidel [19] determined the graphs under (ii), not (i), to be the seven graphs
defined in 4.5, 4.6, 4.7, 4.8, 4.9." As a theorem:

> **(4.14)** Let $X$ be a connected strongly regular graph with least eigenvalue $-2$ that is
> represented by a subset of $E_8$, and suppose that $X$ is isomorphic to none of $L(K_m)$,
> $L(K_{m,m})$ and $CP(m)$. Then $X$ is isomorphic to one of the Chang graphs I, II and III
> (Example 4.5), the Schläfli graph (4.6), the Shrikhande graph (4.7), the Clebsch graph (4.8)
> and the Petersen graph (4.9). Conversely, these seven graphs have these properties, and they are
> pairwise non-isomorphic.

**What the literature provides.** None of the sources has a complete computer-free proof.
- [S68] Theorem 14 derives the parameters and treats $L_2(n)$ for $n\ne4$, $T(n)$ for
  $n\ne8$ and the Clebsch graph, with two steps that "readily follow". For $(16,6,2,2)$ it cites
  [Sh59], for $(28,12,6,4)$ it cites Chang, and it cites Seidel's 1967 paper three times,
  including for the uniqueness of the Schläfli graph. §11 lists the printing errors in §§4–6
  of [S68].
- [BvM] Theorem 1.1.1 derives the parameters, and its proof begins "We shall assume the
  classification of the graphs with the parameters of the examples". [BvM] §10 states each
  uniqueness theorem it needs, and proves none of them.
- [BCN] Theorem 3.12.4 (i) follows from Theorem 3.12.2, whose proof is computer-free,
  and from Proposition 3.11.2, whose proof is "By inspection of the tables in Bussemaker
  et al.", a computer enumeration of 187 graphs. [BCN] adds: "It would be interesting to have a
  geometric, computer free proof of this proposition".

Thus the books replace Chang's papers only by citation. For the graphs that (4.14) needs, the
argument below is such a computer-free proof.

**The route** (decision 3 of §13). We will follow the proof of [BCN] Theorem 3.12.2 in the
language of line systems, and replace Proposition 3.11.2 by switching. Let $X$ be as in (4.14), represented by
$\Sigma=\{\mathbf x_u\}\subseteq E_8$.

- ⟨1⟩1. *Parameters.* $(n,k,a,c)$ is one of the 15 sets of SR5, since Theorems 4.3 and 4.4 give
  $n\le36$ and $k\le16$, and $\operatorname{rk}(2I+A)\le8$.
- ⟨1⟩2. *Cocktail party parameters.* If $(n,k,a,c)=(2m,2m-2,2m-4,2m-2)$, the complement of $X$ is
  1-regular, so $X\cong CP(m)$. [S]
- ⟨1⟩3. *$X$ is not a generalized line graph.* Otherwise Theorem 4.11 makes $X$ a line graph or a
  cocktail party graph, and the proof of Theorem 4.13, with LG1, puts $X$ in case (i).
- ⟨1⟩4. *The root system of $X$.* Let $R$ be the star closure of $\Sigma$ (LN3). It lies in $E_8$,
  it is indecomposable since $X$ is connected, and it spans $\operatorname{span}\Sigma$, of
  dimension $1+m_1$ (SR4). By Theorem 3.5, $R$ is isomorphic to $A_\ell$, $D_\ell$, $E_6$, $E_7$ or
  $E_8$, and by Theorems 4.1 and 4.2 and ⟨1⟩3 it is one of $E_6$, $E_7$, $E_8$, with
  $1+m_1\in\{6,7,8\}$. This excludes $(9,4,1,2)$ and $(10,6,3,4)$, which have $m_1=4$.
- ⟨1⟩5. *The apex.* Put $\mathbf w=\frac1{k+2}\sum_u\mathbf x_u$. Then $(\mathbf w,\mathbf x_u)=1$
  for every $u$, $\lvert\mathbf w\rvert^2=\nu:=n/(k+2)$, and $(\mathbf w,\mathbf y)$ is an integer
  for every $\mathbf y\in R$, since $R$ lies in the ℤ-span of $\Sigma$.
- ⟨1⟩6. *Integrality.* Let $B$ be the Gram matrix of a basis of simple roots of $R$ (LN7, carried
  over by LN4). Writing $\mathbf a$ for the vector of inner products of $\mathbf w$ with this basis,
  we have $\nu=\mathbf a^TB^{-1}\mathbf a$, so $\det(B)\,\nu$ is an integer (LA6): $3\nu$, $2\nu$,
  $\nu$ for $E_6$, $E_7$, $E_8$. This excludes $(15,8,4,4)$ ($E_6$, $\nu=\frac32$) and
  $(21,10,5,4)$ ($E_7$, $\nu=\frac74$). [BCN] states the finer facts about the dual lattices in
  §3.10, (iv) and (v).
- ⟨1⟩7. *When $\nu=2$, the apex is a root.* This is the case for $(10,3,0,1)$, $(16,6,2,2)$ and
  $(28,12,6,4)$, where $R$ is $E_6$, $E_7$ and $E_8$. These are maximal (Theorem 3.6), and
  $(\mathbf w,\mathbf y)$ is an integer with $\lvert(\mathbf w,\mathbf y)\rvert\le2$ for
  $\mathbf y\in R$, so $\mathbf w\in R$ by Definition 2.2.
- ⟨1⟩8. *A transversal.* Then $\Sigma\subseteq N_{\mathbf w}(R)$, and $\Sigma$ contains at most one
  vector of each pair, since the two vectors of a pair have inner product $-1$. There are 10, 16
  and 28 pairs (LN6), which is $n$ in each case; so $\Sigma$ contains exactly one vector of each
  pair.
- ⟨1⟩9. *Switching.* By LN5 we may take $\mathbf w=\mathbf c$ in the models of LN6. Since
  $(\mathbf c-\mathbf e_i-\mathbf e_j,\mathbf e_k+\mathbf e_l)=1-\lvert\{i,j\}\cap\{k,l\}\rvert$ and
  $(\mathbf c-\mathbf e_i-\mathbf e_j,\mathbf c-\mathbf e_k-\mathbf e_l)=\lvert\{i,j\}\cap\{k,l\}
  \rvert$, $X$ is obtained from $T(5)$, from $T(6)$ with an isolated vertex, or from $T(8)$ by
  switching with respect to the set $Y$ of pairs whose vector in $\Sigma$ has the form
  $\mathbf c-\mathbf e_i-\mathbf e_j$ (SW4).
- ⟨1⟩10. *Regular switchings.* SW3 turns regularity of $X$ into a condition on the graph $H$ with
  edge set $Y$, as follows.
  - $E_6$: $T(5)^Y$ is 3-regular if and only if $H$ is a 5-cycle; then $X$ is the Petersen graph.
  - $E_7$: after replacing $Y$ by its complement we may assume that the isolated vertex is not in
    $Y$. Then the switched graph is 6-regular if and only if $H$ is a 2-regular graph on 6
    vertices. The hexagon gives the Shrikhande graph and $2K_3$ gives $L(K_{4,4})$.
  - $E_8$: $T(8)^Y$ is 12-regular if and only if $H$ is regular. Up to complementation and the
    symmetric group, $H$ is one of 11 graphs of valency at most 3 (SE4), and $T(8)^Y$ is isomorphic
    to $T(8)$ for $H=\emptyset$ and $2K_4$; to Chang I for $4K_2$, $2C_4$, the cube and one further
    cubic graph; to Chang II for $C_8$, the Wagner graph and one further cubic graph; and to Chang
    III for $C_3+C_5$ and the remaining cubic graph.

  [new]; computation C22. We also checked the first two cases by listing all transversals (10
  and 16 pairs), and the third on all 11 graphs.
- ⟨1⟩11. *When $\nu\ne2$.* The parameter sets $(16,10,6,6)$ ($E_6$, $\nu=\frac43$) and
  $(27,16,10,8)$ ($E_7$, $\nu=\frac32$) remain; SE2 and SE3 identify them.
- ⟨1⟩12. *Q.E.D.* $L(K_{4,4})$ and $T(8)$ lie in case (i). For the converse, computation C9
  checks the representations of Examples 4.5–4.9 and the parameters, and SE6 separates the seven
  graphs from one another and from case (i).

The uniqueness theorems that the route uses:

**SE1. The Petersen graph.** A strongly regular graph with parameters $(10,3,0,1)$ is the
Petersen graph. [S] Fix a vertex; each non-neighbour is adjacent to exactly one of its three
neighbours, and the three matchings between the resulting pairs are forced. [St] [BvM] §10.3.
The route above obtains the
Petersen graph in ⟨1⟩10 and does not need SE1; we list it because it is short and does not depend
on $E_8$. (Our repair of Lemma 2.10 identifies the Petersen graph directly, as the graph of the
2-subsets of a 5-set with disjointness as adjacency.)

**SE2. The Clebsch graph.** A strongly regular graph with parameters $(16,10,6,6)$ is the Clebsch
graph; equivalently (SR2), one with parameters $(16,5,0,2)$ is the folded 5-cube. [S] Fix a vertex
of the complement: its 5 neighbours are pairwise non-adjacent, its 10 non-neighbours correspond
to the 2-subsets of its neighbourhood, and adjacency among these is disjointness
([C17] Theorem 2.2). [S68] §6, case 5 (pp. 295–296), sketches a
matrix proof. [St] [BvM] §10.7. [BCN] §3.11 (iii) prints the parameters of the
complement as $(16,5,0,1)$; they are $(16,5,0,2)$.

**SE3. The Schläfli graph.** A strongly regular graph with parameters $(27,16,10,8)$ is the
Schläfli graph: its complement has parameters $(27,10,1,5)$, so it is a generalized quadrangle of
order $(2,4)$ by GQ1, and it is unique by GQ2. [St] [BvM] §10.10; [S68] §6, case 6,
defers to Seidel's 1967 paper.

**SE4. Regular graphs of small valency on 8 vertices.** Up to isomorphism, the 1-regular graph on
8 vertices is $4K_2$, the 2-regular graphs are $C_8$, $C_3+C_5$ and $2C_4$, and the 3-regular
graphs are $2K_4$ and five connected graphs, among them the cube and the Wagner graph. [S], a
structured case split (`cgss/proofs/reg8/reg8.tex`). Only the case
$E_8$ of ⟨1⟩10 needs it.

**SE5. The certificates.** [K] Computation C22: explicit isomorphisms from the 11 switched graphs
of ⟨1⟩10 to $T(8)$ and the three Chang graphs, and from the switched graphs of the cases $E_6$ and
$E_7$ to the Petersen graph, the Shrikhande graph and $L(K_{4,4})$. Each is a check on at most 28
vertices.

**SE6. Non-isomorphism.** [K] $T(8)$ and $L(K_{4,4})$ contain no induced $K_{1,3}$, while the
Chang and Shrikhande graphs do. Chang I, II and III contain 128, 160 and 160 induced copies of
$K_{1,3}$, and II and III are separated by their maximal cliques: 32, 24 and 8 of sizes 4, 5 and 6
in I; 48 and 48 of sizes 4 and 5 in II; 75, 30 and 3 of sizes 4, 5 and 6 in III. Their
automorphism groups have orders 384, 96 and 360. [BvM] §10.11 (the table under "Cliques and
cocliques") numbers II and III the other way round. The other sporadic graphs differ from the
graphs in (i) in their parameters.

**SE7. Other routes, not needed.** These give the classical form of the classification, for all
$n$ and without $E_8$, should it ever be wanted.
- Shrikhande's theorem for the parameters $(m^2,2(m-1),m-2,2)$: [P] [Sh59] Theorem 1
  for $m\ne4$ and §7 (pp. 788–797) for $m=4$, a long hand analysis (in our working notes, a short
  argument of ours replaces it). We found no mathematical errors in it; the appeal in case (i) of
  §7 (p. 789) needs only the easy half of Shrikhande's lemma, and §7 leaves about a dozen routine
  checks to the reader.
- $T(m)$ for $m\ne8$: a second-subconstituent induction [new], on top of the
  claw lemmas that [BvM] proves inside the proof of Theorem 1.1.1.
- Chang's theorem through the regular two-graph on 28 points and SE3 [new], ending in the same
  11 cases.
- The Schläfli and Clebsch graphs as the common neighbours of an edge and of a triangle in the
  graph on the roots of $E_8$, as in the proof of [BCN] Theorem 3.12.2; this needs transitivity on
  edges and triangles, which LN5 does not give directly.

## 8. Section 5

### 8.1 Corollary 5.10

**HR1. The statement.** It needs nothing from [HR65]. The "unless" clause needs a graph that is
cospectral with the flag graph of the $(4,3,2)$ design and not isomorphic to it, and [CGSS] gives
one by explicit vectors in $E_7$ (computation C13).

**HR2. The exception is unique** (a side claim). [P] with gaps: [HR65], end of §8 (the case
$k=3$, $\lambda=2$ of the proof of the Theorem, pp. 250–252).
The printed argument has an unjustified step ("impossible unless $c$ and $d$ are adjacent"), a
misdrawn figure in its first case, and an unproved final claim (that the graph of the second case
satisfies the hypotheses); two printed eigenvectors (for $G_5$ and $H_8$) are wrong. We have a
gap-free elementary proof [new] from $A^3=4A+4J$ and $2I+A\succeq0$, with no root systems and no
search, in our working notes. We checked the conclusion against the complete list of the 1544
connected 4-regular graphs on 12 vertices.

### 8.2 Remark 5.12: there is no 2-(15,5,2) design

[CGSS] cites Hall's book [8, p. 291], which we do not have. We use [HC54] instead
(`cgss/proofs/hallconnor/hallconnor.tex`). Here $(v,k,b,r,\lambda)=(15,5,21,7,2)$, and $Z$ is the graph on
the blocks in which two blocks are adjacent when they meet in one point.

**HC1.** Two distinct blocks meet in 1 or 2 points, and each block meets 10 others in one point
and 10 in two. [S] A second moment count: $\sum_i(i-1)(i-2)n_i=0$. This is [HC54] Lemma 4.1,
which [HC54] takes from Connor (1952) without proof.

**HC2.** Adjacent blocks have exactly 5 common neighbours in $Z$. [S] From $(N^TN)^2$; this is
the part of [HC54] Lemma 4.2 (also from Connor) that is used.

**HC3. Connor's matrix.** $C=35I-7N^TN+10J$ satisfies $C^2=35C$ and $CN^T=0$, so $C$ is positive
semidefinite of rank at most 6. Thus its principal submatrices are positive semidefinite, and
those on 7 or more blocks are singular. [S] This is Connor's Theorem 3.1, which [HC54] cites and
which we did not consult; our reconstruction is in `cgss/proofs/hallconnor/hallconnor.tex`. At $k=5$
the rank half is essential, since the relevant $7\times7$ minors are positive.

**HC4. Local lemmas.** $Z$ has no induced $K_{1,3}$, and [HC54] Lemma 4.5 holds, by explicit
vectors $\mathbf x$ with $\mathbf x^TC_U\mathbf x<0$; two $7\times7$ submatrices are nonsingular,
by explicit inverses. [K] (computation C19.) At $k=5$, [HC54] Lemmas 4.3 and 4.4
reduce to the absence of claws.

**HC5. The embedding.** [P] [HC54] Theorem 3.2, and Theorem 2.1 in the direction "if", at $k=5$:
the 6-cliques of $Z$ form seven sets satisfying the conditions of Theorem 2.1, which gives a
$22\times22$ matrix $N^*$ with $N^*N^{*T}=5I+2J$. The uniqueness claimed in Lemma 5.1 of [HC54],
and the family of all $(k+1)$-cliques that §6 there takes for granted, need fills, which
`cgss/proofs/hallconnor/hallconnor.tex` gives.

**HC6.** DS5 shows that no such matrix exists. There is no search: the largest explicit matrices
are $7\times7$, and the $22\times22$ identities are symbolic. Computation C19.

### 8.3 Example 5.13

**EX1. Resolvable designs for $k=2^d$.** Let $\mathcal O$ be a regular hyperoval (a conic with its
nucleus) in $PG(2,q)$, $q=2^{d+1}=2k$. Take as points the $k(2k-1)$ lines that miss $\mathcal O$,
and as blocks the $4k^2-1$ points off $\mathcal O$. This is a 2-$(k(2k-1),k,1)$ design with $2k+1$
blocks on each point, and the lines through a fixed point of $\mathcal O$ give a resolution into
$2k+1$ parallel classes. [S], over `GaloisField 2 (d+1)` [M].

**EX2. $k=3$.** An explicit Kirkman triple system on 15 points. [K]

**EX3. The two known designs.** The design $(6,3,10,5,2)$ is the unique 2-(6,3,2) design, given
explicitly. The design $(28,21,36,27,20)$ is the complement of the residual of the $(37,9,2)$
biplane whose blocks are the translates of the fourth powers modulo 37,
$\{1,7,9,10,12,16,26,33,34\}$. [K] Computation C23.

**EX4. The cospectral mate is not a flag graph.** $L(H)$ has the spectrum of $F(D_1)$, by Lemma 5.5
and the computation in the proof of Theorem 5.8, and it is not the flag graph of any design $D_2$:
the star closures of the standard representations of $L(H)$ and of $F(D_2)$ are $D_\ell$ and
$A_\ell$ with $\ell=s(s+2)$ (LN3, since $H$ is connected and not bipartite), and isomorphic graphs
have isometric representations (LA2). [S] Whitney's theorem on line graphs would also do, but Mathlib does not
have it. For $k=3$, $D_1$ does not exist, by Remark 5.12.

## 9. Section 6

**HD1. Theorem 6.2.** Its proof needs the fact that $n-1$ mutually orthogonal lines occur in
$D_{n-1}$ only when $n-1$ is even, and never in $A_{n-1}$ [S] (the coordinates of Definition 3.1
suffice; Theorem 3.6 is not needed: `blueprint/sec6-hadamard.tex`), and the indecomposability
argument of errata Gap 17. The proof assumes
$n>9$. The remaining orders are vacuous: if $16\nmid n$, then $n/16$ and $3n/16$ are not integers,
so every four rows agree in exactly $n/8$ places; then $A=0$ and $PP^T=nI$, which contradicts
$\operatorname{rk}(PP^T)=n-1<\binom n2$. So only $n\ge16$ matters.

## 10. Side claims

| Claim | Where | What formalizing it needs | Effort |
| --- | --- | --- | --- |
| the exception in Corollary 5.10 is unique | proof of Corollary 5.10 | HR2 | M |
| Norman's theorem | Section 6 | Norman [CGSS 17], not among the sources | M |
| the uniqueness of $H_{12}$ | Section 6 | a classification of the Hadamard matrices of order 12, not among the sources (C16 needs one explicit $H_{12}$) | M |
| Shult's characterization | Remark 2.11 | Shult [CGSS 24], not among the sources; [C17] Chapter 4 | XL |

The remark after Theorem 4.4 is in the core (§13). The four rows are results of other papers,
which [CGSS] mentions but neither proves nor uses, and they are outside the scope; the first
would need no further source (HR2).

## 11. Problems found in the sources

These matter when a structured proof follows the source. The problems in [CGSS] itself are in
`cgss/errata.md`.

- **[BCN].** In the third proof of Theorem 1.15.2, "$K_{4\times2}$" should be the cube (GQ2). In
  3.11 (iii), the complement of the Clebsch graph has parameters $(16,5,0,2)$, not $(16,5,0,1)$
  (SE2). Theorem 3.2.5 leaves its combinatorial step to the reader (SM3). Theorem 3.12.4 (i)
  depends on the computer-based Proposition 3.11.2. We could not compare our copy with the printed
  book, so the first two may be errors of the copy.
- **[BvM].** In the last paragraph of the proof of Theorem 1.1.1, "For $\mu=8$ we find the
  Schläfli graph" is wrong: that branch is infeasible, and the Schläfli graph arises in the next
  one. In §10.10 (under "Construction: in the regular two-graph on 28 points"), the
  descendant of the two-graph of $\overline{T(8)}$ is the complement of the Schläfli graph, not the
  Schläfli graph. The table in §10.11 ("Cliques and cocliques") numbers Chang II and III the other
  way round from [CGSS]. [BvM] states, and does not prove, every uniqueness theorem of §7.3. We
  found these in the authors' revised version of 2024, and have not compared them with the
  printed book.
- **[S68].** "$A_{12}=J-I$, $A_{13}=A_{23}=-\mathbf j$" (§6, case 3, p. 294) should be $A_{12}=J-2I$
  and $A_{13}=-A_{23}=\pm\mathbf j$; "$4J-2I$" (§6, case 5, p. 295) should be $4I-2J$;
  "$\lvert\rho_1-\rho_2\rvert$" (proof of Theorem 12, p. 289) should be $\lvert\rho_0-\rho_2\rvert$;
  "$-v+3-3\rho_2+\rho_0$" (§6, case 4, p. 295) should have 2 in place of 3; "any subgraph which is an
  8-circuit" (Example 5) is false for some 8-circuits; and the "pseudolattice graph" on
  $X'\cup X''\cup Y'\cup Y''$ (§6, case 6, p. 297) is the Clebsch graph. We confirmed these against
  the printed paper.
- **[HC54].** The uniqueness in Lemma 5.1 is asserted, and the global family of cliques is never
  defined; "(k−1)(k−2) twos and hence 2(k−1) ones" is justified only as an inequality at that stage;
  the minimum in (4.3) is an infimum.
- **[Sh59].** In case (i) of §7 (p. 789), "as in the proof of Theorem 1" appeals to a lemma that
  fails for $s=4$; only its easy half is needed.
- **[HR65].** The eigenvalues in the statement of the Theorem are misprinted; the $(4,3,2)$ case
  has the defects listed in HR2.
- **[LS73].** (F) is not stated; "at most $4\times2=8$" hides a pairing; two cases of Theorem 4.5
  are left to the reader.
- **[Y25].** $N_{1/3}(d)$ is attributed to [LS73] Theorem 3.6, but it is Theorem 4.5; Lemma 5.3
  uses the evenness of the lattice without saying so.

## 12. New computations

The computations C1–C24 are listed, with their SageMath checks, in `cgss/certificates/README.md`; C18 is
Lemma P (SR5). The entries of this file give rise to the last five.

| | Where | Computation | Lean method |
| --- | --- | --- | --- |
| C20 | LN6, EQ2, §7.3 | $\lvert N_{\mathbf r}\rvert$ for every vector of the models of $A_9$ (90 vectors), $D_9$ (144), $E_6$ (72), $E_7$ (126) and $E_8$ (240); the pairs of $N_{\mathbf c}$ in $E_6$, $E_7$, $E_8$ | `decide +kernel`, or parametric for $A_\ell$ and $D_\ell$ |
| C21 | LN7, ⟨1⟩6 | bases of simple roots of $E_6$, $E_7$, $E_8$ with Gram determinants 3, 2, 1 | `decide`, `Matrix.det` on integer matrices |
| C22 | ⟨1⟩10, SE5, SE6 | the switched graphs: Petersen; Shrikhande and $L(K_{4,4})$; $T(8)$ and the Chang graphs from the 11 graphs of SE4, with isomorphism certificates and the invariants of SE6 | `decide` on at most 28 vertices |
| C23 | EX1–EX3 | the designs of Example 5.13 for $d=1,2$; a Kirkman triple system; the $(37,9,2)$ biplane and the design $(28,21,36,27,20)$ | `decide` |
| C24 | EQ3 | for $(n,k)=(28,16)$: $(2m-16)^2>(27-m)(192-4m)$ for $21\le m\le27$, which forces $\operatorname{rk}(2I+A)=8$ | `decide`, `nlinarith` |

## 13. Decisions

We decided the following.

1. **Theorem 4.4.** We complete the paper's proof, with EQ1–EQ3 in place of [LS73]. We do not use
   our traceless argument.
2. **The remark after Theorem 4.4** is in the core (EQ3).
3. **Remark 4.14.** We follow the route of §7.3. The routes of SE7, which prove the
   classification without $E_8$, are not needed.
4. **Theorem 3.8.** We use Smith's argument (SM1–SM3).
5. **Remark 3.11.** We take the second option below: the textbook route on top of Mathlib,
   with our own write-up of the classification of the finite-type Cartan matrices (Smith's
   argument with weights). The ordinary proof is `cgss/proofs/remark311/remark311.tex`, and the
   blueprint gives its structured version.
6. **Side claims.** Norman's theorem, the uniqueness of $H_{12}$, Shult's characterization and the
   uniqueness of the exception in Corollary 5.10 are results of other papers, which [CGSS]
   mentions but neither proves nor uses; they are outside the scope. The last needs no further
   source (HR2).

**The options that were considered for Remark 3.11.** The remark claims the classification of the
Root Systems with two root lengths (RS2), which none of the sources proves and which nothing else in
the paper uses. There were three ways to treat it.
- *Our own proof, as [CGSS] suggests.* The short roots and the long roots each form a sum of
  systems $A$, $D$, $E$, and we determine how two such sums can be glued. This follows the paper,
  but the case analysis is new work. Effort L.
- *The textbook proof, on top of Mathlib.* Mathlib already reduces the classification to the list
  of connected finite-type Cartan matrices (RS2). That list is Smith's argument with weights: if
  $DM$ is positive definite for a Cartan matrix $M$ and a positive diagonal $D$, then
  $D^{1/2}MD^{-1/2}=2I-B$, where $B$ is the adjacency matrix of a graph with edge weights $1$,
  $\sqrt2$ and $\sqrt3$, and $B$ has largest eigenvalue less than 2. So SM1–SM3, extended to
  weighted graphs, give it (compare Humphreys, *Introduction to Lie Algebras and Representation
  Theory*, §11). This reuses decision 4, and the list of finite-type Cartan matrices is missing
  from Mathlib, so it would be a natural contribution there. Effort L.
- *Leave it as a side claim.* Formalize only the explicit part (the systems $B_\ell$ and $C_\ell$,
  $F_4$ and $G_2$ as sets of lines, with their numbers of lines and their matrix equations), and
  quote the classification. Effort S.

We chose the second.

A further source, not needed: Seidel's 1967 paper ([BCN] reference 652, *Indag. Math.*
**29** (1967), 188–196), for comparison with the switching argument of §7.3.
