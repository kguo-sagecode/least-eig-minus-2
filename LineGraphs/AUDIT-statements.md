# The statement audit: [CGSS] and [Exc] against the final Lean

**About this record.** This file is the summary of an audit of 9 October 2026, which compared the
Lean statements of this library, statement by statement, with [CGSS] (P. J. Cameron,
J. M. Goethals, J. J. Seidel and E. E. Shult, *Line graphs, root systems, and elliptic geometry*,
J. Algebra 43 (1976), 305–327) and with the note [Exc], *A database of exceptional graphs with
least eigenvalue ≥ −2* (`exceptional/note/exceptional.tex`). Language-model agents carried out
the audit, as the acknowledgements of the note say. The record describes the
library as of that date, and so do the line numbers that it gives for the files of the repository
and of Mathlib; some of its findings were acted on the same evening (the last section below), and
the library has changed since. We note the following about how to read it.

- [CGSS] is cited by the pages of the journal ("p. N").
- The README that the record cites is the working README of the project on that date, which this
  repository does not include. Its lists of the errors, gaps and implicit hypotheses of [CGSS] are
  kept, with the same numbers, in `cgss/errata.md`.
- The dependency diagram that the record cites is now `dependency-diagram.md`, at the top of the
  repository; the rows and sections that the record names are those of that date.
- The detailed reports of the audit, one for each part, are not included in this repository;
  this file gives their counts and their High and Medium findings.
- The result numbers of [Exc] are those of the version of the note of that day, which the author
  has since renumbered. Sections 2 and 3 of that version are Sections 2 and 3 of the present one,
  and Lemma 3.1 to Theorem 3.6 keep their numbers. A new Lemma 2.1, on the vectors of norm 2 of
  the lattice, has been added, so Lemmas 2.1 to 2.4 and Proposition 2.5 of that version are now
  Lemmas 2.2 to 2.5 and Proposition 2.6; Theorem 3.7, on the files of the database, is now
  Theorem C.1 of Appendix C; and Proposition 3.8, on the maximal exceptional graphs, is now
  Proposition 3.7.

Earlier reviews compared the Lean with the blueprint. This audit compares the final Lean with the
paper itself. For every definition, numbered result, remark that makes a claim, and computation
of [CGSS], and for every definition and result of Sections 2 and 3 of the note [Exc]
(`exceptional/note/exceptional.tex`), a read-only Claude Opus auditor quoted the source and the
Lean statement side by side. It then sorted every difference into three kinds: a repair recorded
in `cgss/errata.md`, a convention of the formalization, or a defect.

## Verdict

No Lean statement says something other than the paper without a recorded reason, and no
definition is wrong or makes a theorem vacuous. The findings are of three kinds:

- claims of the paper that are neither formalized nor recorded as left out;
- theorems that quantify over a structure the library never constructs (a canonical form, a
  signing), so that the library does not show them non-vacuous;
- documentation: docstrings, tags, the errata's wording, and names in `cgss/notation.md`.

## Counts

Each detailed report gave one row per item, with the Lean declarations and the verdict.

| Part | Items | Same | Equiv. | Stronger | Weaker | Different | High | Medium | Low |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Section 2 | 21 | 6 | 10 | 2 | 0 | 0 | 0 | 1 | 11 |
| Section 3 | 37 | 9 | 12 | 8 | 1 | 0 | 0 | 0 | 19 |
| Section 4 to Ex. 4.9 | 33 | 15 | 7 | 5 | 6 | 0 | 1 | 1 | 6 |
| Section 4 from Thm. 4.10 | 20 | 11 | 4 | 2 | 1 | 1 | 0 | 1 | 9 |
| Section 5 | 37 | 26 | 7 | 1 | 2 | 0 | 0 | 2 | 11 |
| Sections 6 and 1 | 49 | 5 | 28 | 4 | 6 | 3 | 0 | 1 | 7 |
| [Exc], Sections 2 and 3 | 31 | | | | | | 0 | 4 | 9 |

The remaining items of a row are not formalized by the author's decision (Remark 2.11, C23, the
side claims), have no counterpart in the paper (Theorems A, B and C of Remark 3.11, and their
lemmas), or were forwarded to another part. "Different" means a recorded repair: Theorem 4.10
adds connectedness (implicit hypothesis 1); in Section 6, the false identities of Error 9 are
rightly absent, and Gap 17 replaces a step of a proof.

## The High and Medium findings

| Finding | What |
| --- | --- |
| sec4a H1 | The subgraph claims of Examples 4.7 (Shrikhande in Chang I) and 4.8 (Clebsch in Schläfli, the neighbours of e₅+e₆) have no Lean statement, although the README's C9 row lists them. |
| sec4a M1 | "which are not line graphs" (p. 318) is neither formalized nor recorded. |
| sec2 M1 | Theorem 2.13 is stated for some star; the paper's is the fixed, arbitrary star. |
| sec4b M1 | The errata's implicit hypothesis 2 says the printed Theorem 4.13 lacks "−2 is an eigenvalue", but "least eigenvalue −2", read literally, includes it; the Lean is exactly the printed statement. |
| sec5 M1 | Remark 5.12's claim that L(L(K₆)), the flag graph of the design (6,6,10,10,10), is an exception, cospectral with L(T(6)), is formalized nowhere and not recorded; the same pair is the evidence for Errors 14, 16 and 17. |
| sec5 M2 | The exception of Corollary 5.10 is shown cospectral and non-isomorphic, but not "not characterized" in the project's sense (implicit hypothesis 6). |
| sec6 M1 | Four background claims of Section 6 (the eigenvalues of PᵀP, and of PPᵀ with multiplicities; the Sylvester case; the Sylvester family for every 2^s) are neither formalized nor recorded. |
| [Exc] M1 | No `CanonicalForm` is constructed, so Theorem 3.6 and the list theorems of Theorem 3.7 (now Theorem C.1) are not shown non-vacuous. |
| [Exc] M2 | The Lean proof of `prop:types` (3) uses [CGSS] Theorem 3.6 and C5, which the note does not list. |
| [Exc] M3 | `lem:snf` uses Mathlib's `Basis.SmithNormalForm`, whose coefficients carry no divisibility chain. |
| [Exc] M4 | The note said "The results of this note are not in Lean". |

Also from the Low findings, for the same reason as [Exc] M1: no lemma shows that a signing
(`LineSystem.Signing`) or a `RootRepresentatives` family exists, which [CGSS] Theorem 3.7 and the
matrix equations of Remark 3.11 quantify over (sec3 L6).

## The Low findings

Each report also lists Low findings: docstrings that cite the toolkit's or the README's numbers as
the paper's, comments, unused instance arguments, missing docstrings, blueprint tags, and small
points of wording in the errata and in `cgss/notation.md`.

## Follow-up, 9 October 2026, evening

At the author's request, what [CGSS] only cites is outside the scope, as citations, not gaps:
Remark 2.11 (Shult's characterization), the uniqueness of the exception in Corollary 5.10
(Hoffman and Ray-Chaudhuri), Norman's theorem, the uniqueness of $H_{12}$, and the existence of
the designs of Example 5.13 for every $k=2^d$ and for $k=3$. The claims that the paper makes
itself and that the Low findings sec2 L5 and L9, sec3 L4, L5, L16 and L18, sec4a L1, L3, L4 and
L5, sec5 L3 and L4, and sec6 L4 found with no Lean statement of their own are now in Lean, with
C23, the paper's two instances of Example 5.13: `LineGraphs/PaperClaims/` and
`LineGraphs/Computations/C23.lean`, printed by the consolidated audit
`LineGraphs/Audit.lean` (see the dependency diagram, section "The paper's own small
claims").
