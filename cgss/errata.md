# Errata for [CGSS]

This file is the permanent record of the problems that we have found in

> P. J. Cameron, J. M. Goethals, J. J. Seidel and E. E. Shult, *Line graphs, root systems,
> and elliptic geometry*, J. Algebra **43** (1976), 305–327,

cited as [CGSS], and of the repairs that the project makes. The entries marked **new** were not
on our first list of problems; we found them while checking that list against the paper, or later
in the formalization. A step of the blueprint that fills a gap is tagged **[repair]** and points to
an entry of this file.

## How to read this file

There are three kinds of entries: errors in the printed paper, gaps in the arguments, and
hypotheses that the statements leave implicit. The entries of each kind are numbered, as *Error n*,
*Gap n* and *Implicit hypothesis n*, and the new entries continue each list. Other files cite
"Error 1" and "Gap 10"; these are the entries below with the same numbers. We give every quotation
and every correction against the published text.

Each entry gives the following.

- **Where.** The item of [CGSS] and the page of the journal. Every quotation below comes from the
  published paper.
- **Printed.** A quotation, in the paper's notation.
- **Correct** or **Missing.** What should be there.
- **Evidence.** How we know: a computation, a counterexample, or the printed text. Scratch
  computations are named as such; they are not kept, and they are outside the trust base. The
  computations C1–C24 are listed in `cgss/certificates/README.md`, and `dependency-diagram.md` gives their
  kernel-checked Lean theorems; an entry says so when a kernel-checked certificate also proves its
  claim.
- **Repair.** Where the repair lives. The blueprint in `blueprint/` gives structured proofs of
  every numbered result of [CGSS], so that "blueprint, Theorem 5.8" names the place of the repair
  there, and step labels such as `210gram` are those of the blueprint. Every numbered result
  except Remark 2.11 is in Lean (see `dependency-diagram.md`); an entry names the Lean
  declaration when the repair concerns a Lean statement. Entries of `cgss/prerequisites.md` are
  cited by label (LG1, EQ3), and computations by their numbers C1–C24.

We quote the paper as printed, so the quotations use $G$ for a graph. Our own text uses $X$, $Y$,
$Z$ (see `cgss/notation.md`), except that an entry which discusses a quoted statement keeps the
statement's names for its objects, such as $G_1$ and $G_2$ in Lemma 5.6 and Theorem 5.8.

## Index

| Entry | Item of [CGSS] | Problem | Repair |
| --- | --- | --- | --- |
| Error 1 | Theorem 3.7 | $E_8$: $(C-18I)$ should be $(C-28I)$ | C6, LN6 |
| Error 2 | Example 4.6 | coefficient $\frac13$ should be $\frac12$ | C9 |
| Error 3 | Lemma 2.10 | entry $(3,1)$ of the block-sum matrix is 0, not 2 | C1 |
| Error 4 | Theorem 5.8 | $s\le 2t-1$ should be $s\ge 2t-1$ | C11 |
| Error 5 | Theorem 3.6 | coclique of $T(6)$ should be clique | C5 |
| Error 6 | Defs. 3.2, Thm. 2.13, proofs of 4.3, 4.4, 5.8 | labels; $\Delta$ counted by lines | blueprint |
| Error 7 | Theorem 4.13 | the count $v-2$, $v-1$ is reversed | LG1 |
| Error 8 | Theorem 4.4 | "28 equiangular lines lie in $\mathbb R^7$" is false as stated | EQ1–EQ3 |
| Error 9 (new) | Section 6 | $xAJ=-nJ$ and $AJ=-dJ$ fail in general | blueprint, C16 |
| Error 10 (new) | Definition 3.9 (b) | $S$ should be $\Sigma$ | `remark311.tex` |
| Error 11 (new) | Remark 3.11 | four statements need qualification | `remark311.tex` |
| Error 12 (new) | Lemma 2.12 | "the unique strongly regular graphs on 9, 15, 27 vertices" | GQ1–GQ2 |
| Error 13 (new) | several | further slips | blueprint |
| Error 14 (new) | Remark 5.7 | the eigenvalues for α = vw, and the sum of two multiplicities | `cgss/proofs/spectraltools/`, Corollary 6.8 |
| Error 15 (new) | Theorem 4.4 | "I + ½A has rank ≤ 7" fails for (n, d) = (28, 12) | blueprint, case split d ≤ 12 or d > 12 |
| Error 16 (new) | Theorem 5.8 | false without b ≥ v | blueprint, hypothesis b ≥ v |
| Error 17 (new) | Corollary 5.9 | the exception must be unordered | blueprint |
| Gap 1 | Lemma 2.10 | the case $k=4$ | blueprint, GQ1–GQ3 |
| Gap 2 | Lemma 2.10 | uniqueness of the three graphs | blueprint, GQ2 |
| Gap 3 | Lemma 2.10 | regularity | blueprint |
| Gap 4 | Theorem 2.13 | numbers of lines and dimensions not derived | C4 |
| Gap 5 | Definition 3.3, Lemma 3.4, Corollary 5.10 | "any one" line or star; labelling of $S(3,4,8)$ | LN5 |
| Gap 6 | Theorem 3.8 | the enumeration is hidden | SM1–SM3, C17 |
| Gap 7 | Theorem 4.4 and the remark after it | [15] does not state one of the two facts cited; the remark is unproved | EQ1–EQ3, C24 |
| Gap 8 | Lemmas 5.1–5.4 | quoted as well known | SP1–SP4 |
| Gap 9 | Theorem 4.13, Remark 4.12 | "it must be 2"; the bipartite case; "easy to see" | LG1 |
| Gap 10 | Theorem 6.2 | the proof assumes $n>9$ | HD1 |
| Gap 11 | Remark 3.11, Theorem 3.12 | no proofs | RS1–RS3, `remark311.tex` |
| Gap 12 | Remark 4.14 | cited; "seven" presupposes non-isomorphism | §7.3, C22 (4-clique profiles) |
| Gap 13 (new) | Theorem 3.6 | $A_n\not\subset D_n$ is not shown | blueprint, C5 |
| Gap 14 (new) | Theorems 4.3, 4.4 | valency bound from Theorem 3.7 needs a pairing | LN6, C20 |
| Gap 15 (new) | Theorem 5.8 | the cocktail party case is not excluded | blueprint |
| Gap 16 (new) | Corollary 5.11 | the designs with one block | blueprint |
| Gap 17 (new) | Theorem 6.2 | indecomposability not shown; for $n=16$ it needs an argument | blueprint, a count of stars |
| Gap 18 (new) | Theorem 4.11 | "$H$, which is connected" is not justified and can fail | blueprint, a split on the vertices with $a_i>0$ |
| Gap 19 (new) | Theorem 4.2 | "a unique maximal set of pairs" is asserted, not proved | blueprint, Lemma (the normal form in $D_n$) |
| Implicit hypothesis 1 | Theorem 4.10; Section 1 | $X$ connected | Lean statement |
| Implicit hypothesis 2 | Theorem 4.13 | a note on how we read "least eigenvalue $-2$"; nothing is missing | Lean statement, as printed |
| Implicit hypothesis 3 | Lemmas 5.4, 5.5 | no isolated vertices; an edge | SP4 |
| Implicit hypothesis 4 (new) | Hypothesis 2.4 | at least two lines | blueprint, Theorem 3.5 |
| Implicit hypothesis 5 (new) | Lemma 5.6 | $G_2$ without isolated vertices | Lean statement |
| Implicit hypothesis 6 (new) | Section 5 | meaning of "characterized by its spectrum" | Lean statements |
| Implicit hypothesis 7 (new) | Definition 2.2 | maximal within the span of the lines | blueprint, Lean definition |
| Implicit hypothesis 8 (new) | Theorem 3.12 | either part of the partition may be empty | `cgss/proofs/thm312/`, Lean statement |

## Errors in the printed paper

### Error 1. Theorem 3.7, the constant for $E_8$

- **Where.** Theorem 3.7; p. 312.
- **Printed.** "$E_8$: $(C+2I)(C-18I)=0$".
- **Correct.** $(C+2I)(C-28I)=0$.
- **Evidence.** Take one vector of squared norm 2 on each of the 120 lines of $E_8$. These
  vectors form a tight frame in $\mathbb R^8$, $\sum\mathbf v\mathbf v^T=30I$, so the Gram matrix
  $2I+C$ satisfies $(2I+C)^2=30(2I+C)$, and $C$ has eigenvalues $28$ and $-2$ with multiplicities 8
  and 112. Equivalently, each line of $E_8$ is at 60° to $56=2\cdot28$ others, and the trace
  argument that the paper gives for $D_n$ yields $\gamma_1+\dots+\gamma_8=224$, so each
  $\gamma_i$ is 28. We checked the eigenvalues numerically for $E_6$, $E_7$ and $E_8$; the printed
  values 10 and 16 for $E_6$ and $E_7$ are correct. `cgss/proofs/remark311/remark311.tex` (§ "Lengths,
  lines, and the matrix equations") derives all five constants from the frame identity; for $E_8$,
  $N/n=15$ gives $2N/n-2=28$.
- **Consequence.** The bound 28 on the valency in Theorem 4.3 is this constant (see Gap 14). With
  the printed 18 the same argument would give 18, which the example in Theorem 4.3 contradicts.
- **Repair.** Blueprint, Theorem 3.7, with computation C6 ($\sum\mathbf v\mathbf v^T=\frac{2N}nI$
  on the span of the roots, over one vector per line; in coordinates, $\frac{2N}n$ times the
  orthogonal projection onto the span, since the models of $A_n$, $E_7$, $E_6$ and the first model
  of $E_8$ do not span their coordinate spaces); the diagonal of $C^2$ is LN6 (computation C20).

### Error 2. Example 4.6, the Schläfli graph

- **Where.** Example 4.6; p. 319.
- **Printed.** "$\{\frac13\Sigma e_k-e_i-e_7;\ i\in T(6,1)\}$".
- **Correct.** $\frac12\sum_{k=1}^8\mathbf e_k-\mathbf e_i-\mathbf e_7$, as in the third family.
- **Evidence.** With $\frac13$ these vectors have squared norm $14/9$, so they do not lie in the
  model (ii) of $E_8$. With $\frac12$ the 27 vectors lie in $E_8$ and represent a strongly regular
  graph with parameters $(27,16,10,8)$; computation C9.
- **Repair.** Blueprint, Example 4.6; computation C9.

### Error 3. Lemma 2.10, the matrix of block sums

- **Where.** Proof of Lemma 2.10; p. 309.
- **Printed.** The third row of the $5\times5$ matrix of block sums is
  "$2\quad 0\quad k^2+k\quad k^2-k\quad k^2-k$".
- **Correct.** Its first entry is 0. The block of the first matrix that it sums, the inner
  products of the vertices of $K$ with $u$, is $0$, since the vertices of $K$ are adjacent to $u$;
  as printed, the second matrix is not even symmetric.
- **Evidence.** Symmetry, and a direct computation of the block sums of the first matrix. The
  determinant that the proof uses is that of the matrix with its first row and column deleted,
  which does not contain the wrong entry; it is $2k^5(5-k)$, as stated (SymPy, scratch). The
  argument is unaffected.
- **Repair.** Blueprint, Lemma 2.10: step `210gram` computes the block sums (its substeps
  `210blocks` and `210sums`), and its closing step corrects the entry; step `210det` is
  computation C1. In Lean the block-sum matrix `Computations.C1.blockSumMatrix` has the entry 0,
  and `LineSystem.Hyp24.gram_blockSumVectors` shows that it is the Gram matrix of the block sums.

### Error 4. Theorem 5.8, the direction of an inequality

- **Where.** Proof of Theorem 5.8; p. 323.
- **Printed.** "$k\leqslant v$ implies $s\leqslant 2t-1$".
- **Correct.** $s\ge 2t-1$, as in the statement, case (iii).
- **Evidence.** Here $k=st$ and $v=\frac12s(s+1)$ with $s,t>0$ (the Remark after Theorem 5.8), so
  $k\le v$ if and only if $t\le\frac12(s+1)$, that is, $s\ge 2t-1$.
- **Repair.** Blueprint, Theorem 5.8; computation C11.

### Error 5. Theorem 3.6, clique and coclique

- **Where.** Proof of Theorem 3.6; p. 312.
- **Printed.** "$A_7\subset E_7$ since a 5-coclique is imbeddable in the triangular graph on 6
  symbols".
- **Correct.** The argument mixes the two graphs on $\Gamma_a$. In the graph of Section 2, where
  adjacency is orthogonality, $\Gamma_a$ of $A_7$ is a coclique on 5 vertices, and $\Gamma_a$ of
  $E_7$ is the complement of $T(6)$, with parameters $(15,6,1,3)$. The inclusion needs a 5-coclique
  of the complement of $T(6)$, that is, a 5-clique of $T(6)$: the five pairs through a fixed
  symbol. $T(6)$ itself has no coclique on more than 3 vertices. The conclusion stands.
- **Evidence.** The definitions; computation C5.
- **Repair.** Blueprint, Theorem 3.6; computation C5.

### Error 6. Minor inconsistencies of labels and counts

- **Where and printed.**
  - Definition 3.2 labels its second model "(i)" (p. 311). Later references
    call it (ii): "We use Definition 3.2(ii) for $E_8$" (p. 318).
  - Theorem 2.13 gives "$|\Delta|=36$", "$|\Delta|=15$", "$|\Delta|=6$" (p. 310). These count lines. As defined in Hypothesis 2.4, $\Delta$ is a set of vectors
    closed under negation, with 72, 30 and 12 elements. The line counts are the ones for which
    $3+3|\Gamma_a|+|\Delta|$ is 120, 63 and 36.
  - The proofs of Theorems 4.3 and 4.4 cite "Lemma 3.7" for Theorem 3.7 (pp. 317 and 318).
  - The proof of Theorem 5.8 cites "Theorem 5.6" for Lemma 5.6 (p. 323).
- **Repair.** The blueprint uses the correct labels and names the three models of $E_8$ (i), (ii),
  (iii). In Theorem 2.13 it writes $|\Delta|/2$ for the number of lines (step
  `213exceptional`); in Lean, $\Delta$ is a set of vectors.

### Error 7. Theorem 4.13, a reversed count

- **Where.** Proof of Theorem 4.13; p. 320.
- **Printed.** "If $\{i,j\}$ and $\{i,k\}$ are edges of $H$, then the number of vertices of $L(H)$
  adjacent to both is $v-2$ or $v-1$ according as $\{j,k\}$ is an edge or not."
- **Correct.** It is $v-1$ if $\{j,k\}$ is an edge and $v-2$ otherwise.
- **Evidence.** The common neighbours of $\{i,j\}$ and $\{i,k\}$ in $L(H)$ are the $v-2$ other
  edges on $i$, together with $\{j,k\}$ when it is an edge. The argument uses only that the two
  values differ, so it is unaffected.
- **Repair.** Blueprint, Theorem 4.13; `cgss/prerequisites.md` §7.2 (LG1).

### Error 8. Theorem 4.4, 28 equiangular lines

- **Where.** Proof of Theorem 4.4; p. 318.
- **Printed.** "But any set of 28 equiangular lines lies in $\mathbb R^7$, hence the multiplicity
  of 0 as an eigenvalue actually is $\geqslant n-7$. This implies that $I+\frac12A$ has rank
  $\leqslant 7$, hence the set of vectors we started with is contained in $E_7$ or $D_7$."
- **Correct.** The first sentence is false as stated: 28 lines at angle $\arccos\frac13$ can span
  $\mathbb R^{15}$. It is true for lines in $\mathbb R^m$ with $m\le14$, in particular in
  $\mathbb R^8$, which is the case used, but [15] does not state it (Gap 7). The last clause should
  also allow $A_7$ and the smaller systems; since $A_7\subset E_7$, every indecomposable
  star-closed set of rank at most 7 lies in $E_7$ or $D_7$, and nothing changes.
- **Evidence.** A single full pillar in the sense of [LS73] gives 28 lines at $\arccos\frac13$
  spanning $\mathbb R^{15}$ (`cgss/prerequisites.md` §7.1).
- **Repair.** EQ1–EQ3: the relative bound of [LS73] and the cone construction through Theorem 3.5
  (decision 1 of `cgss/prerequisites.md` §13); blueprint, Theorem 4.4.

### Error 9 (new). Section 6, the row sums of $A$

- **Where.** Section 6, before Theorem 6.2; p. 326.
- **Printed.** "$(xA+nI)(xA-\frac12n(n-2)I)=0$, $\quad xAJ=-nJ$, hence $x$ divides $n$" and
  "$(A+dI)(A-\frac12d(n-2)I)=0$, $\quad AJ=-dJ$".
- **Correct.** The quadratic equations hold; the equations $xAJ=-nJ$ and $AJ=-dJ$ do not hold in
  general. Since $PP^T=nI+xA$, the equation $xAJ=-nJ$ says that $PP^T\mathbf j=0$, that is,
  $P^T\mathbf j=0$. The entry of $P^T\mathbf j$ at a column $c$ is $\frac12(\sigma(c)^2-n)$, where
  $\sigma(c)$ is the sum of column $c$ of $H_n$. Thus $xAJ=-nJ$ holds if and only if every column
  sum of $H_n$ is $\pm\sqrt n$. This depends on the signs of the rows of $H_n$, and it fails for
  every choice of signs unless $n$ is a square. The conclusion that $x$ divides $n$ is true for
  another reason: as the paper says next, $d^2=(n/x)^2$ is the number of fourth rows that agree
  with three given rows in $\frac18(n\pm x)$ places, so $n/x$ is a rational number whose square is
  an integer. (For a fixed row $i$, the $n-1$ vectors $H_i\circ H_j$ form an orthogonal basis of
  $\mathbf j^\perp$, and expanding $H_k\circ H_l$ in this basis gives the count.) The claim needs
  $n\ge3$. For $n=1$ and $n=2$ the matrix has fewer than four rows, so Hypothesis 6.1 holds for
  every $x$, and $x$ need not divide $n$ (take $n=2$ and $x=3$); there is no Hadamard matrix of
  order 3. Thus the Lean statement, `Matrix.IsHadamard.FourRowAgreement.dvd_card`, assumes
  $n\ge3$. It also assumes $x>0$, which costs nothing: for $n\ge4$ and $x=0$ we would have
  $PP^T=nI$, of rank $\binom n2>n$, whereas $P$ has only $n$ columns.
- **Evidence.** For the Paley matrix $H_{12}$, the row sums of $xA$ are $-60$ and $36$, and no
  choice of row signs makes every column sum $\pm\sqrt{12}$. For the Sylvester matrix of order 8,
  every row sum of $xA$ is $24=\frac12n(n-2)$, so $\mathbf j$ is an eigenvector of $PP^T$ for
  $\frac12n^2$, not for 0 (NumPy, scratch). The same check confirms Hypothesis 6.1 for $H_{12}$
  with $x=4$.
- **Consequence.** None for Theorem 6.2, whose proof uses only the quadratic equation, the fact
  that the lines lie in $\mathbf j^\perp$, and the orthogonality of the lines through a fixed row.
- **Repair.** Blueprint, Section 6: the background states the quadratic equation, and derives
  $x\mid n$ from the count; computation C16. A shorter route: for $n>2$ the eigenvalue $-n/x$ of the integer matrix $C_H$ has
  multiplicity $\frac12(n-1)(n-2)>0$, so it is an integer by the rational root theorem
  (`cgss/proofs/spectraltools/spectraltools.tex`, Theorem 9.6, used in its Theorem 10.4).

### Error 10 (new). Definition 3.9 (b), $S$ for $\Sigma$

- **Where.** Definition 3.9 (b); p. 314.
- **Printed.** "$\forall_{r\in\Sigma}\forall_{\lambda\in\mathbb R}((\lambda r\in S)\Rightarrow
  (\lambda\in\{1,-1\}))$".
- **Correct.** $\lambda r\in\Sigma$. The letter $S$ names the set of lines of Section 2.
- **Evidence.** The printed text, and the sense of the definition. Read with $\Sigma$, condition (b) also
  excludes $0$ from $\Sigma$ (if $0\in\Sigma$, then $\lambda0\in\Sigma$ for $\lambda=2$).
- **Repair.** `cgss/proofs/remark311/remark311.tex`, §2 and § "Interpretations and corrections of the
  sources", item 2.

### Error 11 (new). Remark 3.11, statements that need qualification

- **Where.** Remark 3.11; p. 314. The findings are those of
  `cgss/proofs/remark311/remark311.tex`, § "Interpretations and corrections of the sources", items 3–6.
- **Printed.** "Let $r,s\in\Sigma$ be not perpendicular. Since $4(r,s)^2/(r,r)(s,s)$ is a positive
  integer $<4$, ..."; "the subset of a Root System consisting of vectors of any fixed length is
  itself a Root System, necessarily one of those described by Theorem 3.10"; "$B_n$ and $C_n$: a set
  of $n^2$ lines in $\mathbb R^n$ with angles 90°, 60°, 45°, and equation
  $(C+2I)(C-2(n-1)I)=0$", and the similar lines for $F_4$ and $G_2$.
- **Correct.**
  1. The roots $r$ and $s$ must also be non-proportional; for $s=\pm r$ the quotient is 4.
  2. The roots of one length form a Root System in their own span, which need not be the whole
     space and need not be indecomposable: the long roots of $B_2$ form $A_1\oplus A_1$, and the
     roots of length 1 in $\{\pm\mathbf u_1,\pm2\mathbf u_2\}$ span a line.
  3. The matrix $C$ is defined before Theorem 3.7 only for vectors of one length. For two root
     lengths we take unit vectors on the lines, as the columns of a matrix $U$, and put
     $C=2U^TU-2I$; then the three printed equations hold.
  4. The listed angles are the angles allowed: for $B_2=C_2$ the angle 60° does not occur.
- **Evidence.** `remark311.tex`, Lemma "angles" and Theorem C, with its checks.
- **Repair.** `cgss/proofs/remark311/remark311.tex` (decision 5 of `cgss/prerequisites.md` §13);
  blueprint, Remark 3.11.

### Error 12 (new). Lemma 2.12, "the unique strongly regular graphs on 9, 15, 27 vertices"

- **Where.** Lemma 2.12; p. 310.
- **Printed.** "... the void graph on $n$ vertices, the graph consisting of $n$ triangles meeting
  at one vertex, the unique strongly regular graphs on 9, 15, 27 vertices."
- **Correct.** There are other strongly regular graphs on these numbers of vertices: $T(6)$ on 15
  and the Schläfli graph on 27 (the complements of the intended graphs), and the degenerate $3K_3$
  and $K_{3,3,3}$ on 9. The intended graphs are those of Lemma 2.10, which are strongly regular with
  parameters $(9,4,1,2)$, $(15,6,1,3)$ and $(27,10,1,5)$. The paper proves only that they are
  regular. Strong regularity takes two further observations, in the notation of Lemma 2.10:
  adjacent vertices have exactly one common neighbour, the third vertex of their triangle; and
  nonadjacent vertices $u$, $v$ have the $k$ common neighbours in $K$.
- **Evidence.** $T(6)$ has parameters $(15,8,4,4)$ and the Schläfli graph $(27,16,10,8)$.
- **Repair.** Blueprint, Lemmas 2.10 and 2.12, which name the graphs by their parameters, or as the
  collinearity graphs of the generalized quadrangles of orders $(2,1)$, $(2,2)$, $(2,4)$ (GQ1,
  GQ2).

### Error 13 (new). Further slips

None of these affects an argument; the blueprint uses the corrected forms.

1. Lemma 3.4: "$|A|=\frac12n(n+1)$" for $|A_n|$ (p. 311).
2. Definition 3.2 (ii): "$\epsilon_i=\pm1$" appears twice in the display (p. 311).
3. Theorem 3.12: "two lines in different subsets are at angles 90° and 45°" for "90° or 45°"
   (p. 315).
4. Section 4: "is and orthonormal basis" (p. 315); "by delecting a one-factor" (p. 316); "whose
   lines from a subset of $D_n$" (p. 316); Corollary 5.10: "The graphs ar switching equivalent"
   (p. 324).
5. The representation of the generalized line graphs, and the proof of Theorem 4.2: "$1\leqslant\alpha
   \leqslant\alpha_i$" for $1\le\alpha\le a_i$ (pp. 316 and 317).
6. Proof of Theorem 4.4: "The projections onto the lines spanned by these vectors are elements of
   $\mathbb R^{28}$ and have Gram matrix $(1-\frac{d+2}{2n})^2I+\cdots$" (p. 317).
   These vectors have squared norm $1-\frac{d+2}{2n}$, and the displayed matrix is the Gram matrix
   of the rank-one matrices $\mathbf p\mathbf p^T$, not of the projections, whose Gram matrix is the
   displayed one divided by $(1-\frac{d+2}{2n})^2$. The conclusion is the same.
7. Proof of Theorem 4.4: "for each eigenvalue $\alpha\ne d$ of $A$" should read "for each
   eigenvalue $\alpha$ of $A$ with an eigenvector orthogonal to $\mathbf j$" (p. 318). The
   two readings differ only when the graph is disconnected; then $d$ is also an eigenvalue on
   $\mathbf j^\perp$, the inequality holds for it, and the sum over $\alpha_1,\dots,\alpha_7$ needs
   it.
8. Remark 5.7: "two eigenvalues $\delta:=\gamma-\frac12(v+w)$ and $\delta:=\gamma'-\frac12(v+w)$"
   for $\delta':=\gamma'-\frac12(v+w)$ (p. 322).

### Error 14 (new). Remark 5.7, the eigenvalues of $A(G_2)$

- **Where.** Remark 5.7; pp. 322–323.
- **Printed.** "To each eigenvalue $\alpha\neq0$ of $B_1B_1^T$ there correspond ... two eigenvalues
  $\delta:=\gamma-\frac12(v+w)$ and $\delta:=\gamma'-\frac12(v+w)$ of $A(G_2)$" (the second
  $\delta$ is the misprint of Error 13, item 8) and "For an eigenvalue 0 of $A(G_1)$ the
  corresponding eigenvalues of $A(G_2)$ are $\pm\frac12(v-w)$. Their multiplicities need not be
  equal, add up to $q-p$".
- **Correct.** (a) For $\alpha=vw$ the roots of $(\gamma-v)(\gamma-w)=\alpha$ are $v+w$ and 0, and
  0 is not an eigenvalue of $M_2M_2^T$, which is nonsingular; thus only $\frac12(v+w)$ occurs, not
  $-\frac12(v+w)$. (b) The multiplicities of $\pm\frac12(v-w)$ are $p-\rho$ and $q-\rho$ with
  $\rho=\operatorname{rk}B_1$ (we write $\rho$, since $r$ is a parameter of the designs of
  Theorem 5.8); their *difference* is $q-p$, and their sum is $p+q-2\rho$.
- **Evidence.** $G_1=K_{6,10}$ and $G_2=T(6)$: $L(K_{6,10})$ and $L(T(6))$ both have spectrum
  $14^1\,8^5\,4^9\,(-2)^{45}$, $G_2$ is 8-regular and not bipartite, and $|G_1|=|G_2|+1$; the
  eigenvalues $\pm2$ of $T(6)$ have multiplicities 5 and 9, which add up to $14\ne q-p=4$. This is
  the situation of Corollary 5.9 and Remark 5.12, where $B_1=J$ has rank 1. We checked it by
  hand, and a kernel-checked certificate also proves it: the spectra of $L(K_{10,6})$, the flag graph of the trivial design
  $(6,6,10,10,10)$, of $L(L(K_6))=L(T(6))$ and of $T(6)$ are
  `Computations.TrivialDesignException.spectrum_flagGraph`, `.spectrum_double_lineGraph` and
  `.spectrum_triangular`, and the cospectrality is `.flagGraph_cospectral_double_lineGraph`
  (`LineGraphs/Computations/TrivialDesignException.lean`).
- **Consequence.** None for Theorem 5.8, which does not use these statements.
- **Repair.** The spectral toolkit, Corollary 6.8 (`cgss/proofs/spectraltools/spectraltools.tex`), states the
  correct spectrum; blueprint, Remark 5.7; in Lean,
  `SimpleGraph.lineGraph_cospectral_bipartite_spectrum_of_not_isBipartite`.

### Error 15 (new). Theorem 4.4, the rank of $I+\frac12A$ when $d=12$

- **Where.** Proof of Theorem 4.4; p. 318.
- **Printed.** The matrix $I+\frac23A-\frac13(J-I)$ "has the simple eigenvalue
  $1+\frac23d-\frac13(n-1)>0$", and later "This implies that $I+\frac12A$ has rank $\leqslant7$,
  hence the set of vectors we started with is contained in $E_7$ or $D_7$."
- **Correct.** For $n=28$ the eigenvalue on $\mathbf j$ is $\frac13(2d-24)$, which is 0 when
  $d=12$, and $(n,d)=(28,12)$ is the case of $T(8)$ and the Chang graphs, which lie in $E_8$. For
  $T(8)$ (spectrum $12^1\,4^7\,(-2)^{20}$) the matrix $I+\frac23A-\frac13(J-I)$ has eigenvalues
  $0$, $4^7$, $0^{20}$, so rank 7, while $I+\frac12A$ has eigenvalues $7$, $3^7$, $0^{20}$, so
  rank 8. Thus the sentence is false for $d=12$. The conclusion $d\le16$ stands, since
  $12\le16$.
- **Evidence.** Checked by hand from the spectrum of $T(8)$.
- **Repair.** Blueprint, Theorem 4.4: split into $d\le12$ (nothing to prove for the bound) and
  $d>12$, where the eigenvalue on $\mathbf j$ is positive and the rank argument goes through.

### Error 16 (new). Theorem 5.8 needs $b\ge v$

- **Where.** Theorem 5.8 and the remark after it; pp. 323–324.
- **Printed.** "Let $D_1$ be a 2-design with parameters $v,k,b,r,\lambda$ ... Then one of the
  following holds", with the cases (i) $v+b\le9$, (ii) $G_2=F(D_2)$, (iii) $v=\frac12s(s+1)$,
  $b=\frac12(s+1)(s+2)$, ....
- **Correct.** The statement fails without $b\ge v$. Take the trivial design $v=k=10$,
  $b=r=\lambda=6$: its flag graph $L(K_{10,6})$ is cospectral with $L(T(6))$ (Error 14). (i) fails
  ($v+b=16$); (ii) fails, since the only design with these parameters has flag graph
  $L(K_{10,6})$, and $T(6)$ is not bipartite; (iii) fails, since $v=10$ forces $s=4$ and then
  $b=15$. The dual design ($v=6$, $b=10$) satisfies (iii) with $s=3$, $t=2$. The paper's remark
  after the theorem ($s,t>0$ when $\lambda<r$; otherwise pass to the dual) is the intended
  hypothesis; every corollary meets it.
- **Evidence.** Checked by hand from the spectra in Error 14. A kernel-checked
  certificate proves that $L(K_{10,6})$ and $L(T(6))=L(L(K_6))$ are cospectral and not
  isomorphic: `Computations.TrivialDesignException.lineGraph_completeBipartite_cospectral_double_lineGraph`
  and `.flagGraph_not_nonempty_iso_double_lineGraph`, the latter for the flag graph of the dual
  design $(6,6,10,10,10)$, which is $L(K_{10,6})$ again.
- **Repair.** Blueprint, Theorem 5.8, with the hypothesis $b\ge v$; in Lean,
  `Design.flagGraph_cospectral`, whose hypothesis `hvb` is $v\le b$.

### Error 17 (new). Corollary 5.9, the exception is unordered

- **Where.** Corollary 5.9; p. 324.
- **Printed.** "the graph $L(K_{m,n})$ is characterized by its spectrum, unless $m=2t^2+t$,
  $n=2t^2-t$, and there exists a symmetric Hadamard matrix with constant diagonal of order
  $4t^2$."
- **Correct.** The exception must read $\{m,n\}=\{2t^2+t,2t^2-t\}$: for $(m,n)=(6,10)$ the
  printed condition does not apply, but $L(K_{6,10})=L(K_{10,6})$ is not characterized (it is
  cospectral with $L(T(6))$; $t=2$).
- **Evidence.** The pair of Error 14. A kernel-checked certificate proves
  that the flag graph $L(K_{10,6})$ of the trivial design $(6,6,10,10,10)$ is cospectral with
  $L(L(K_6))=L(T(6))$, is not isomorphic to it, and is not characterized by its spectrum in the
  sense of Implicit hypothesis 6: `Computations.TrivialDesignException.flagGraph_cospectral_double_lineGraph`,
  `.flagGraph_not_nonempty_iso_double_lineGraph` and `.not_flagGraphCharacterized`.
- **Repair.** Blueprint, Corollary 5.9, stated for unordered $\{m,n\}$ and reduced to $m\ge n$
  by symmetry; in Lean, `SimpleGraph.lineGraph_completeBipartite_characterized`, whose exception
  `SimpleGraph.HasCompleteBipartiteHadamardException` is symmetric in $m$ and $n$.

## Gaps in the arguments

### Gap 1. Lemma 2.10, the case $k=4$

- **Where.** Proof of Lemma 2.10; p. 309.
- **Printed.** "For $k=4$ each vertex of $K$ is in 2 triangles with third edge in $N$. However,
  since $|N|=7$ there must be a vertex in $K$ whose triangles have an edge in common. This is
  impossible."
- **Missing.** The second sentence does not follow as written.
- **Repair.** Blueprint, Lemma 2.10 [repair] (steps `210dK` and `210exclude`), by the
  following argument. For $x\in K$ let
  $x'\in L$ and $x''\in M$ be the third vertices of the triangles on $\{x,u\}$ and $\{x,v\}$, and
  for $w\in N$ let $d_K(w)=|\Gamma_1(w)\cap K|$. The triangle property gives $d_K(w)\in\{k-2,k\}$;
  since $\sum_{w\in N}d_K(w)=k(2k-4)$ and $|N|=3k-5$, exactly $\frac12(k-2)(5-k)$ vertices of $N$
  have $d_K=k$, and a vertex with $d_K=k$ forces $k-2=1$. Thus $k\ne4$. Alternatively, for $k=4$ the
  graph would be strongly regular with parameters $(21,8,1,4)$ (Error 12), and its eigenvalue $-4$
  would have multiplicity $28/5$. See also GQ1–GQ3 of `cgss/prerequisites.md`.

### Gap 2. Lemma 2.10, uniqueness

- **Where.** Proof of Lemma 2.10; pp. 309–310.
- **Printed.** "For $k=2,3,5$ we have $|N|=1,4,10$ and $N$ consists of one vertex, a 3-claw, and a
  Petersen graph, respectively. In each case $\Gamma_a$, which has 9, 15, 27 vertices,
  respectively, is a uniquely determined graph."
- **Missing.** Proofs of the structure of $N$ and of uniqueness.
- **Repair.** Blueprint, Lemma 2.10 [repair] (steps `210two`, `210three`, `210five`), with
  the invariant $d_K$ of Gap 1: for $k=2$, $N$ is
  a vertex with $d_K=0$; for $k=3$, a claw whose centre has $d_K=3$ and whose leaves have $d_K=1$;
  for $k=5$, $d_K=3$ on all of $N$, and $w\mapsto K\setminus\Gamma_1(w)$ is a bijection from $N$
  to the 2-subsets of $K$ under which adjacency becomes disjointness, so $N$ is the Petersen graph.
  In each case every adjacency between $N$ and $K\cup L\cup M$ is forced. The alternative is GQ2
  ([BCN] Theorem 1.15.2).

### Gap 3. Lemma 2.10, regularity

- **Where.** Proof of Lemma 2.10; p. 309.
- **Printed.** "The graph on $\Gamma_a$ is regular. Indeed, the valencies of the nonadjacent $u$
  and $v$ both are $2k$, and so is the valency of every further vertex, since no $x\in K$ is
  adjacent to all of $L$, $M$, $N$."
- **Missing.** The argument needs expanding. The computation for $u$ and $v$ applies to every
  nonadjacent pair, so both vertices of a nonadjacent pair have the same valency. Every vertex of
  $L$, $M$ or $N$ is nonadjacent to $u$ or to $v$. A vertex $x\in K$ is adjacent to exactly one
  vertex of $L$, namely $x'$, and $k\ge2$, so $x$ has a non-neighbour in $L$.
- **Repair.** Blueprint, Lemma 2.10 [repair] (step `210regular`, by a different
  propagation argument).

### Gap 4. Theorem 2.13, the numbers of lines and the dimensions

- **Where.** Theorem 2.13; p. 310.
- **Missing.** The numbers of lines and the dimensions are not derived in Section 2.
- **Repair.** They follow from the uniqueness in Lemma 2.12 together with the models of Section 3
  (computation C4: the graphs on $\Gamma_a$ and $(|\Gamma_a|,|\Delta|)=(9,6),(15,15),(27,36)$,
  counting lines). The blueprint states Theorem 2.13 in Section 2 with these facts as inputs (the
  paragraph "Inputs from Section 3" of `sec2-lines.tex`, which records them as deferred
  dependencies), and Section 3 proves them; in Lean, `LineSystem.five_possibilities'` discharges
  them by `LineSystem.modelInputs`.

### Gap 5. Definition 3.3, and the labelling of $S(3,4,8)$

- **Where.** Definition 3.3 (p. 311), the proof of Lemma 3.4 (p. 311) and the proof of
  Corollary 5.10 (p. 324).
- **Printed.** "The root system $E_7$ is the subsystem of $E_8$ consisting of the lines orthogonal
  to any one of its lines. The root system $E_6$ is the subsystem of $E_8$ consisting of the lines
  orthogonal to any one of its stars."
- **Missing.** (a) Independence of the choice of line or star needs an argument. (b) Lemma 3.4
  uses that $\{5,6,7,8\}$ is a block of $S(3,4,8)$, and Corollary 5.10 that $\{1,2,5,6\}$,
  $\{1,2,7,8\}$ and their images under $(1\,2\,3\,4)(8\,7\,6\,5)$ are blocks, whereas Section 3
  defines $S(3,4,8)$ only as "the set of the blocks of the 3-design $(8,4,14,7,3)$".
- **New observation.** These nine blocks and $\{1,2,3,4\}$ extend to an $S(3,4,8)$ in exactly one
  way, by $\{1,3,5,7\}$, $\{1,3,6,8\}$, $\{2,4,5,7\}$, $\{2,4,6,8\}$ (exhaustive scratch check). So
  the labelling that the blueprint fixes is forced.
- **Repair.** For (a), LN5 (transitivity on roots) for the lines; for stars, transitivity on
  ordered pairs of roots with inner product $-1$ (blueprint, Lemma (independence of the
  perpendicular choices) in Section 3). For (b), the blueprint fixes the labelling above.

### Gap 6. Theorem 3.8

- **Where.** The paragraph before Theorem 3.8; p. 313.
- **Printed.** "From the realizations of Definitions 3.1, 3.2, 3.3 we easily write down the
  possible sets of vectors, thus obtaining the list of the graphs with largest eigenvalue 2 given in
  [15]."
- **Missing.** A real enumeration of the sets of roots with pairwise inner products 0 and $-1$.
  The citation is correct: [LS73] Theorem 5.1 lists these graphs. The note after Figure 1 ("if a
  suitable vector (such as the indicated one) is deleted, we obtain a basis for $\mathbb R^n$")
  holds for any one vector, with $\mathbb R^n$ read as the span, of dimension one less than the
  number of vertices (`remark311.tex`, Corollary D). The labels in Figure 1 are $A_n$, $D_n$,
  $E_6$, $E_7$, $E_8$, without tildes (see `cgss/notation.md`).
- **Repair.** Smith's argument, SM1–SM3 (decision 4 of `cgss/prerequisites.md` §13), and
  `remark311.tex`, Corollary D; computation C17.

### Gap 7. Theorem 4.4 and [15]

- **Where.** Proof of Theorem 4.4; p. 318.
- **Printed.** "It is well known [15] that this implies $n\leqslant 28$." and the sentence quoted in
  Error 8; at the end of the proof, "There is no regular graph with $n=28$, $d=16$ contained in
  $E_8$."
- **Missing.** [15] ([LS73]) states the first fact (Theorem 4.5 there) but not the second. The
  paper gives no proof of the last sentence (the remark after Theorem 4.4); the argument before
  it gives only $d\leqslant16$ when $n=28$, which allows $d=16$.
- **Repair.** EQ1–EQ3, proved from Theorem 3.5; decision 1 of `cgss/prerequisites.md` §13. For
  the remark, EQ3 with C24: the rank of $2I+A$ is 8, so the 28 equiangular lines span
  $\mathbb R^8$, against EQ2; blueprint, the remark after Theorem 4.4.

### Gap 8. Lemmas 5.1–5.4

- **Where.** Lemmas 5.1–5.4; p. 321.
- **Printed.** "The following Lemmas 5.1 through 5.4 about graphs $G$ and line graphs $L(G)$ are
  well known, cf. [3, 9]."
- **Missing.** Proofs.
- **Repair.** SP1–SP4 of `cgss/prerequisites.md`.

### Gap 9. Theorem 4.13 and Remark 4.12

- **Where.** Proof of Theorem 4.13 and Remark 4.12; p. 320.
- **Printed.** "Since this number is a constant, it must be 2 and $H$ is complete bipartite.
  Secondly, let $H$ be bipartite. By similar reasoning it follows that $H$ must be $K_{n,n}$ or
  $K_{1,n}$." Remark 4.12: "it is easy to see that a connected generalized line graph contains no
  3-claws if and only if ...".
- **Missing.** The values 0 and 1 must be excluded; the bipartite case needs its own argument; the
  claims of Remark 4.12 need full arguments.
- **Repair.** LG1: the value 0 makes $L(Y)$ complete, and the value 1 is excluded by counting the
  edges disjoint from a fixed edge; the value 2 and the bipartite case follow the proof of [BCN]
  Theorem 3.12.4. Remark 4.12 in the blueprint, as an optional remark.

### Gap 10. Theorem 6.2, small orders

- **Where.** Proof of Theorem 6.2; p. 326.
- **Printed.** "The set is indecomposable, and $n>9$, hence the set is contained in the root system
  $A_{n-1}$ or $D_{n-1}$."
- **Missing.** The proof assumes $n>9$. The other orders are vacuous. If $16\nmid n$, then $n/16$
  and $3n/16$ are not integers, so the hypothesis requires any four rows to agree in exactly $n/8$
  places (which is impossible outright if $8\nmid n$); then $A=0$ and $PP^T=nI$, which contradicts
  $\operatorname{rk}(PP^T)=n-1<\frac12n(n-1)$. Thus only the orders $n\ge16$ with $16\mid n$ matter.
  In particular, $n=8$ is not a genuine case.
- **Repair.** HD1 of `cgss/prerequisites.md`; blueprint, Theorem 6.2. See Gap 17 for the order 16.

### Gap 11. Remark 3.11 and Theorem 3.12

- **Where.** Remark 3.11 and Theorem 3.12; pp. 314–315.
- **Printed.** "This readily leads to the remaining indecomposable Root Systems, cf. [4, 1]" and
  "More generally we can prove the following theorem."
- **Missing.** Remark 3.11 only sketches the classification of the Root Systems with two root
  lengths, and Theorem 3.12 has no proof.
- **Repair.** RS1–RS2 and `cgss/proofs/remark311/remark311.tex` for Remark 3.11 (decision 5); RS3 for
  Theorem 3.12. See also Error 11.

### Gap 12. Remark 4.14

- **Where.** Remark 4.14; p. 321.
- **Printed.** "Seidel [19] determined the graphs under (ii), not (i), to be the seven graphs
  defined in 4.5, 4.6, 4.7, 4.8, 4.9."
- **Missing.** No proof is given, and none of the sources of `cgss/prerequisites.md` has a
  complete computer-free one. "The seven graphs" presupposes that the three Chang graphs are pairwise non-isomorphic, which
  the paper does not show. Brouwer and Van Maldeghem number the Chang graphs II and III the other
  way round (see `cgss/notation.md`).
- **Repair.** The route of `cgss/prerequisites.md` §7.3 (decision 3), in Lamport style in
  `blueprint/sec4-remark414.tex`; for the non-isomorphism, computation C22 with the profiles of
  4-cliques through a vertex (Chang I $\{32^4,36^{24}\}$, Chang II $\{34^{24},36^4\}$, Chang III
  $\{33^{10},35^{18}\}$, $T(8)$ $\{40^{28}\}$), in place of SE6's counts of maximal cliques; the
  Shrikhande graph has no 4-clique and $L(K_{4,4})$ has 8.

### Gap 13 (new). Theorem 3.6, the inclusion $A_n\subset D_n$

- **Where.** Proof of Theorem 3.6; p. 312.
- **Printed.** "Apart from the obvious $A_8\subset E_8$, $D_8\subset E_8$ the only further
  inclusion (up to isometry) between sets of the same dimension is $A_7\subset E_7$. Indeed, by
  Lemma 2.7 the sets of lines are completely determined by their subgraph on $\Gamma_a$. Using
  Lemma 2.12 we observe: ... $A_6\not\subset E_6$ ...; $D_7\not\subset E_7$ and $D_6\not\subset
  E_6$ since the valencies of the corresponding graphs on $\Gamma_a$ do not fit."
- **Missing.** The proof considers only inclusions in $E_6$, $E_7$, $E_8$. It does not exclude
  $A_n\subset D_n$ for $n\ge4$, where counting lines does not help, since $\frac12n(n+1)<n(n-1)$.
  (The other inclusions in the same dimension are excluded by counting lines.) Nor does it say why
  an indecomposable set that is not maximal lies in a larger indecomposable star-closed set of the
  same dimension.
- **Fill.** Choose $\mathbf a,\mathbf b$ in $A_n$ with $(\mathbf a,\mathbf b)=-1$; for instance
  $\mathbf a=\mathbf e_1-\mathbf e_2$, $\mathbf b=\mathbf e_2-\mathbf e_3$, for which
  $\Gamma_a=\{\mathbf e_j-\mathbf e_3:4\le j\le n+1\}$. The graph on $\Gamma_a$ of $A_n$ is a
  coclique on $n-2$ vertices. It is an induced subgraph of the graph on $\Gamma_a$ of $D_n$ for the
  same $\mathbf a,\mathbf b$, which consists of $n-3$ triangles on a common vertex and has no
  coclique on more than $n-3$ vertices. (The signed permutations act transitively on the ordered
  pairs of roots of $D_n$ with inner product $-1$, so this graph does not depend on the pair.) For
  the second point, a set of lines at 60° and 90° spanning $\mathbb R^n$ lies in a maximal one
  (LN2), which is star-closed by Lemma 2.3, and which is indecomposable if the smaller set is, since
  an orthogonal splitting of the larger set would split the smaller one.
- **Repair.** Blueprint, Theorem 3.6 [repair]; computation C5, extended by $A_n\not\subset D_n$.

### Gap 14 (new). Theorems 4.3 and 4.4, the valency bound from Theorem 3.7

- **Where.** Proofs of Theorems 4.3 and 4.4; pp. 317 and 318.
- **Printed.** "The maximum valency cannot exceed 28 because of Lemma 3.7." and "Now Lemma 3.7
  implies $d\leqslant16$".
- **Missing.** Theorem 3.7 gives the diagonal of $C^2$: each line is at 60° to $2\theta$ others,
  where $\theta$ is the second constant (56 others in $E_8$, 32 in $E_7$). The bound on the valency
  needs one more step: the vectors $\mathbf u$ of the root system with $(\mathbf u,\mathbf r)=1$
  fall into $\theta$ pairs $\{\mathbf u,\mathbf r-\mathbf u\}$ with
  $(\mathbf u,\mathbf r-\mathbf u)=-1$, and a set of vectors with nonnegative inner products
  contains at most one vector of each pair. Thus the valency is at most $\theta$: 28 in $E_8$, and
  16, 10, 6 in $E_7$, $D_7$, $A_7$.
- **Repair.** LN6 (the sets $N_{\mathbf r}$ and their pairs; computation C20); blueprint, Theorems
  4.3 and 4.4.

### Gap 15 (new). Theorem 5.8, the cocktail party case

- **Where.** Proof of Theorem 5.8; p. 323.
- **Printed.** "In addition $G_2$ is regular, by Lemma 5.2, and $G_1$ is connected. Hence $G_2$ is
  a line graph."
- **Missing.** The step rests on Theorem 4.11, which also allows a cocktail party graph, and the
  proof does not exclude it. (That $G_2$ is connected follows from Lemma 5.1, since the largest
  eigenvalue of $G_1$ is simple.)
- **Fill.** A graph with the spectrum of $CP(m)$ is regular of valency $2m-2$ on $2m$ vertices, by
  Lemma 5.2, so its complement is 1-regular and the graph is $CP(m)$. Thus, if $G_2$ were a
  cocktail party graph, then $F(D_1)$ would be regular of valency two less than its number of
  vertices, that is, $r+k-2=vr-2$. With $k\le v$ this forces $v=2$ and $k=r=b=2$, so that
  $v+b=4\le9$.
- **Repair.** Blueprint, Theorem 5.8 [repair]. The fill above lands in case (i), which also needs a
  representation in $E_8$; the blueprint closes the case through (ii) instead: $X_1$ and $X_2$ are
  both $CP(m)$, so $D_2=D_1$.

### Gap 16 (new). Corollary 5.11, the designs with one block

- **Where.** Proof of Corollary 5.11; p. 325.
- **Printed.** "Since (i) only occurs for $(v,k,\lambda)=(3,2,1)$, the theorem holds without
  exceptions".
- **Missing.** Case (i) of Theorem 5.8, $v+b\le9$, also occurs for the designs with a single block
  containing every point, $(v,k,b,r,\lambda)=(v,v,1,1,1)$ with $2\le v\le8$. These satisfy the
  standing assumptions $v>1$, $k>1$, $b>0$ of Section 5, and have $\lambda=1$. Their flag graph is
  $L(K_{1,v})=K_v$, which is characterized by its spectrum, since a cospectral graph is regular of
  valency $v-1$ on $v$ vertices. So the conclusion stands. (There are no further cases: a design
  with $\lambda=1$ has no repeated blocks, and for $k<v$ Fisher's inequality leaves only
  $(3,2,1)$.) The proof also leaves to the reader that the hexagon, the flag graph for $(3,2,1)$, is
  characterized by its spectrum; a cospectral graph is 2-regular and connected, by Lemmas 5.1 and
  5.2. The same remark applies to Corollary 5.10.
- **Repair.** Blueprint, Corollaries 5.10 and 5.11 [repair].

### Gap 17 (new). Theorem 6.2, indecomposability

- **Where.** Proof of Theorem 6.2; p. 326.
- **Printed.** "The set is indecomposable, and $n>9$, hence the set is contained in the root system
  $A_{n-1}$ or $D_{n-1}$."
- **Missing.** No argument is given that the $\frac12n(n-1)$ lines are indecomposable, and for
  $n=16$ counting the components does not give one.
- **Analysis.** Let $\ell_{ij}$ be the line spanned by $H_i\circ H_j$, and split the lines into the
  components of their non-orthogonality graph, with spans $U_C\subseteq\mathbf j^\perp$. For a fixed
  row $i$, the $n-1$ lines $\ell_{ij}$ are mutually orthogonal and span $\mathbf j^\perp$, so each
  component $C$ contains exactly $m_C=\dim U_C$ of them, and thus $\frac12n\,m_C$ lines in all. The
  star closure of $C$ is indecomposable of rank $m_C$, so by Theorem 3.5 and Lemma 3.4 it is $A_m$
  with $\frac12nm\le\frac12m(m+1)$, that is $m\ge n-1$; or $D_m$ with $\frac12nm\le m(m-1)$, that
  is $m\ge\frac12n+1$; or $E_6$, $E_7$, $E_8$, which need $n\le12$, $n\le18$, $n\le30$. By Gap 10
  only multiples of 16 matter. For $n\ge32$ every component has rank more than $\frac12(n-1)$, so
  there is one component and the printed argument applies. For $n=16$ the count also allows two
  components, of types $E_8$ and $E_7$, with 64 and 56 lines; the printed proof does not exclude
  this.
- **Evidence.** For $n=16$ the hypothesis says that no four rows have a constant Hadamard product;
  for a matrix with its first row and column all $+1$, it says that the 16 rows, read as binary
  vectors, have pairwise distinct sums. An exhaustive search (a scratch C program, not kept in the
  repository and outside the trust base) found no Hadamard matrix of order 16 with this property.
  It fixed two rows by permuting columns and enumerated the other 13 rows (21.8 million nodes); a
  second run that also normalized a third row (about $1.6\times10^5$ nodes) agreed, and the same
  program without the condition finds Hadamard matrices at once. Thus Theorem 6.2 is true for
  $n=16$, but its printed proof does not prove it.
- **Repair.** A count of stars excludes the decomposition of type $E_8\oplus E_7$, with no search
  (written out in the blueprint of Section 6, `blueprint/sec6-hadamard.tex`, Lemmas `lem:6-components`, `lem:6-decomposition` and `lem:6-E7`,
  in a signed form: the $3136$ ordered pairs of vectors of the component at inner product $-1$
  inject into the $14\cdot32=448$ pairs $(\mathbf t,\mathbf u)$ with $\mathbf t$ one of the 14
  vectors of $R$ outside the component and $\mathbf u\in N_{\mathbf t}$). Let $n=16$, and suppose that one component $C$ has star closure $R$ of
  type $E_7$; then $C$ has $\frac12\cdot16\cdot7=56$ of the 63 lines of $R$.
  1. Each line $\ell_{ij}$ is at 60° to exactly $2n-4$ others: the quadratic equation
     $(A+2I)(A-(n-2)I)=0$ holds (Error 9), so the diagonal of $A^2$ is $2(n-2)$. Lines in different
     components are orthogonal, so these $2n-4=28$ lines lie in $C$, and $C$ has
     $\frac12\cdot56\cdot28=784$ pairs of lines at 60°.
  2. If $\ell_{ij}$ and $\ell_{kl}$ are at 60°, then $(H_i\circ H_j,H_k\circ H_l)=\epsilon\frac n2$
     with $\epsilon=\pm1$, and the third line of their star is spanned by
     $H_i\circ H_j-\epsilon H_k\circ H_l$. This vector has entries $0$ and $\pm2$, and exactly
     $\frac n4$ of them are nonzero, whereas the vectors $H_i\circ H_j$ have no zero entry. Thus the
     third line lies in $R$ but not in $C$: it is one of the 7 lines of $R\setminus C$.
  3. Each line of $E_7$ is at 60° to 32 others (Theorem 3.7, $\theta=16$), so it lies in exactly 16
     stars, and a star through a line of $R\setminus C$ contains at most one pair of lines of $C$.
     By 2, each of the 784 pairs of 1 lies in its own such star. Thus $784\le7\cdot16=112$, a
     contradiction.

  The same count gives a second proof that the type $A_{n-1}$ does not occur: there $R=C$, and
  step 2 leaves no room for the third line of any star. We checked the counts of $E_7$ and $E_8$
  numerically (scratch). With this, the printed proof of Theorem 6.2 is complete once the
  components are counted as above.

### Gap 18 (new). Theorem 4.11, "$H$, which is connected"

- **Where.** Proof of Theorem 4.11; p. 320.
- **Printed.** "Hence $H$, which is connected, either has no vertex $i$ with $a_i\ne0$ ... or ...".
- **Missing.** No reason is given, and the claim can fail: a vertex $i$ of $H$ that is isolated
  and has $a_i=0$ contributes nothing to $L(H;a_1,\dots,a_m)$, so $G$ can be connected while $H$
  is not. The argument needs only the vertices with $a_i>0$ and the edges of $H$.
- **Repair.** Blueprint, Lemma (regular generalized line graphs) in Section 4: a split on the
  vertices with $a_i>0$; the triples closed under adjacency exhaust $X$ by its connectivity, and
  an edge $\{i,j\}$ with $a_j>0$ gives $2a_j+v_j=0$ against $v_j\ge1$ (computation C10).

### Gap 19 (new). Theorem 4.2, the unique maximal set of pairs

- **Where.** Proof of Theorem 4.2; pp. 316–317.
- **Printed.** "Hence any two vectors of $\Sigma$ such as $e_1+e_2$ and $e_1-e_2$ are contained in a
  unique maximal set of pairs $e_1\pm e_\mu$", and the choice of signs that follows.
- **Missing.** The uniqueness and maximality of the set of pairs, and the choice of signs, are
  asserted without proof.
- **Repair.** Blueprint, Lemma (the normal form in $D_n$), `lem:4-Dnform` (the pairs, centres and
  petals, and the signs; it is the body of Theorem 4.2's proof, so that the
  remark after Theorem 4.2 can use the coordinates), where the proof sketch carries `\repair` with this
  entry.

## Implicit hypotheses

The Lean statements state these explicitly. Entry 2 is a note on how we read a phrase of
the paper, not a hypothesis that the paper leaves out; it keeps its number, which other files
cite.

### Implicit hypothesis 1. Theorem 4.10 needs $X$ to be connected

- **Where.** Theorem 4.10; p. 319. The claim of the introduction that the lines of such a graph
  lie in one of the root systems needs the condition too; p. 306.
- **Printed.** "If $G$ is a graph with least eigenvalue $-2$, then either (i) $G$ is a generalized
  line graph; or (ii) $G$ is represented by a subset of $E_8$." In the introduction: "Any graph
  with least eigenvalue $-2$ may be viewed as a set of lines at $60^\circ$ and $90^\circ$. As a
  consequence of the main theorem, this set is contained in one of the root systems."
- **Evidence.** Two disjoint copies of the Petersen graph have least eigenvalue $-2$ and do not
  form a generalized line graph. Their matrix $2I+A$ has rank $12>8$, so they are not represented
  in $E_8$ either. Thus their lines lie in none of the root systems $A_n$, $D_n$, $E_6$, $E_7$,
  $E_8$: subsets of $A_n$ and $D_n$ represent generalized line graphs (Theorems 4.1 and 4.2), and
  $E_6$, $E_7$ and $E_8$ span at most 8 dimensions. Section 4 states the condition (p. 315).
- **Repair.** The Lean statement, `SimpleGraph.hoffman`, assumes `X.Connected`. So does the Lean
  form of the claim of the introduction,
  `SimpleGraph.IsRepresentation.exists_isRepresentedIn_rootType` (blueprint, Lemma (a root system
  containing the lines), `lem:4-rootsystem`).

### Implicit hypothesis 2. Theorem 4.13 and "least eigenvalue $-2$"

- **Where.** Theorem 4.13; p. 320. The phrase also occurs in Theorems 4.10 and 4.11 (pp. 319 and
  320).
- **Printed.** "If $G$ is a connected strongly regular graph with least eigenvalue $-2$, then
  either ..."
- **Note.** Nothing is missing from the printed theorem. Read literally, "least eigenvalue $-2$"
  says that the least eigenvalue is $-2$, so that $-2$ is an eigenvalue, and the paper uses the
  phrase in this sense: "the least eigenvalue of $L(G;a_1,\dots,a_m)$ is $-2$ if the number of
  vertices exceeds $n$" (p. 316), and the proof of Theorem 4.13 ends with
  "$K_n=L(K_{1,n})$ and $C_5=L(C_5)$ do not have $-2$ as an eigenvalue". Thus Theorem 4.13 is
  correct as printed. In Theorems 4.10 and 4.11 we read the phrase as the lower bound
  $\lambda_{\min}\ge-2$, that is, $2I+A\succeq0$, which makes these two theorems stronger.
  Theorem 4.13 is false under that reading: for $n>36$, $K_n$ is strongly regular in Mathlib's
  sense (`IsSRGWith`) and has least eigenvalue $-1$, but it is none of the graphs in (i) or (ii).
- **Repair.** None is needed. The Lean statement `SimpleGraph.seidel` assumes the lower bound and,
  as a second hypothesis, that $-2$ is an eigenvalue; together these say that the least eigenvalue
  is $-2$, by the bridge lemma `SimpleGraph.leastEigenvalue_eq_neg_two_iff`, so the
  Lean states the printed theorem.

### Implicit hypothesis 3. Lemmas 5.4 and 5.5

- **Where.** Lemmas 5.4 and 5.5; p. 321.
- **Evidence.** Lemma 5.4 needs $X$ to have no isolated vertices: $K_2$ together with an isolated
  vertex is a counterexample. Lemma 5.5 needs at least one edge, since all edgeless graphs have the
  same line graph.
- **Repair.** SP4; blueprint, Lemma 5.5.

### Implicit hypothesis 4 (new). Hypothesis 2.4 needs two lines

- **Where.** The text after Hypothesis 2.4; p. 307.
- **Printed.** "Without loss of generality we assume that $S$ contains lines $\langle a\rangle$ and
  $\langle b\rangle$ whose spanning vectors $a$ and $b$ have the inner product $(a,b)=-1$."
- **Missing.** This is possible exactly when $S$ has at least two lines: an indecomposable set with
  two or more lines contains two lines at 60°, since otherwise all its lines would be mutually
  orthogonal, and a choice of signs gives $(\mathbf a,\mathbf b)=-1$. A single line is an
  indecomposable star-closed set, namely $A_1$, and for it $\Gamma_a$, $\Delta$ and $\Sigma$ are
  not defined. Thus Lemma 2.12, Theorem 2.13 and Theorem 3.5 need the case of one line separately;
  the first line of Theorem 2.13 with $n=1$ is this case. The empty set must be excluded, as
  `LineSystem.classification` does (`hne`).
- **Repair.** Blueprint, Theorems 2.13 and 3.5, a case split on the number of lines; in Lean the
  structure `Hyp24` carries $\mathbf a$ and $\mathbf b$.

### Implicit hypothesis 5 (new). Lemma 5.6 needs $G_2$ without isolated vertices

- **Where.** Lemma 5.6; p. 321.
- **Printed.** "Let $G_1$ be connected bipartite such that $L(G_1)$ is regular. Let $G_2$ be such
  that $\operatorname{spec}(L(G_1))=\operatorname{spec}(L(G_2))$. Then either (i) ... or (ii)
  $G_1$ is not regular; $G_2$ is regular, not bipartite; $|G_1|=|G_2|+1$."
- **Evidence.** Take $G_1=K_{1,3}$, and let $G_2$ be a triangle together with an isolated vertex.
  Then $L(G_1)=L(G_2)=K_3$, but $G_2$ is neither bipartite nor regular. The proof applies Lemma 5.4
  to $G_2$, which needs no isolated vertices (Implicit hypothesis 3); it also uses that $L(G_2)$ is
  regular and connected, which follows from Lemmas 5.1 and 5.2. Theorem 5.8 is unaffected, since
  there the graph $H$ with $G_2=L(H)$ can be chosen without isolated vertices.
- **Repair.** The blueprint and the Lean statement of Lemma 5.6 assume that $G_2$ has no isolated
  vertices.

### Implicit hypothesis 6 (new). The meaning of "characterized by its spectrum"

- **Where.** Corollaries 5.9–5.11, Remark 5.12 and Example 5.13; pp. 324–325.
- **Printed.** For instance, "The flag graph of a 2-design with $\lambda=1$ is characterized by its
  spectrum."
- **Missing.** The paper does not define the phrase. Its proofs show, through Theorem 5.8 (ii),
  that every graph with the spectrum of $F(D_1)$ is $F(D_2)$ for some 2-design $D_2$ with the same
  parameters, and this is the sense of Hoffman and Ray-Chaudhuri [14] and of Doob [6, 7]. Read as
  "determined up to isomorphism by its spectrum", Corollaries 5.10 and 5.11 and Remark 5.12 are
  false. The spectrum of $F(D)$ depends only on the parameters, since $NN^T=(r-\lambda)I+\lambda J$
  (proof of Theorem 5.8), whereas $F(D)=L(I(D))$ determines $I(D)$ by Whitney's theorem, and so
  determines $D$ up to duality. Thus the two Steiner triple systems on 13 points have cospectral,
  non-isomorphic flag graphs (against Corollary 5.11), and the five symmetric designs with
  parameters $(15,7,3)$ give at least three (against Corollary 5.10 and Remark 5.12, with
  $\lambda=3$). For Corollary 5.9 the two readings agree, since the trivial design with given
  parameters is unique.
- **Repair.** The blueprint and the Lean statements define the phrase in this sense: every graph
  with the spectrum of $F(D_1)$ is isomorphic to $F(D_2)$ for some 2-design $D_2$ with the
  parameters of $D_1$. On the paper's route, the "not characterized" of Example 5.13 is then EX4
  of `cgss/prerequisites.md`, a case of Whitney's theorem; the Lean proof,
  `Design.not_flagGraphCharacterized_of_resolvable`, avoids EX4 by a clique bound (blueprint,
  Example 5.13).

### Implicit hypothesis 7 (new). Definition 2.2 means maximal within the span

- **Where.** Section 2, first paragraph, and Definition 2.2; p. 306.
- **Printed.** "Without loss of generality the lines are taken to pass through the origin of
  $\mathbb R^n$ and to span $\mathbb R^n$." and "A set of lines at 60° and 90° in $\mathbb R^n$ is
  maximal if any line of $\mathbb R^n$ belongs to the set whenever it has angles 60° or 90° with
  all lines of the set."
- **Missing.** Maximality is meant relative to the space that the lines span. Theorem 3.6 needs
  this reading: it calls $A_7$ and $A_8$ non-maximal because $A_7\subset E_7$ and $A_8\subset E_8$
  in the same dimension, and $A_n$ is defined in Definition 3.1 in $\mathbb R^{n+1}$, where
  $\mathbf e_1+\mathbf e_2$ is at 60° or 90° to all its lines, so that no $A_n$ would be maximal
  in its ambient space. [BCN] works with root lattices and does not use the notion.
- **Repair.** The Lean definition `LineSystem.IsMaximal` and Definition 2.2 of the blueprint ask
  for maximality within $\operatorname{span}(\Phi)$. Lemma 2.3 is unchanged, since the sum of two roots
  lies in the span.

### Implicit hypothesis 8 (new). Theorem 3.12: a part may be empty

- **Where.** Theorem 3.12; p. 315.
- **Printed.** The lines can be "partitioned into two subsets".
- **Missing.** Either subset may be empty. With both nonempty the theorem is false: a single line
  lies in a Root System but cannot be split into two nonempty parts, and two lines of $A_2$ at 60°
  must lie in the same part.
- **Repair.** The partition is a colouring $b:S\to\mathrm{Bool}$, not necessarily surjective; the
  empty set of lines is allowed. `cgss/proofs/thm312/thm312.tex` proves the theorem in this form, and
  the docstrings of
  `LineSystem.subset_rootSet_iff_bipartition` and `LineSystem.HasBipartition` say so.

## Problems in the other sources

The problems that we found in the sources that the paper relies on ([BCN], [BvM], [S68], [HC54],
[Sh59], [HR65], [LS73], [Y25]) are listed in `cgss/prerequisites.md` §11, next to the entries
that use them. We do not repeat them here.
