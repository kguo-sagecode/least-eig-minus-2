# Graphs with least eigenvalue −2: a Lean formalization and a database of the exceptional graphs

This repository holds two pieces of work.

- **A formalization of [CGSS] in Lean 4**, on top of Mathlib, where [CGSS] is
  P. J. Cameron, J. M. Goethals, J. J. Seidel and E. E. Shult, *Line graphs, root systems, and
  elliptic geometry*, J. Algebra **43** (1976), 305–327,
  [doi:10.1016/0021-8693(76)90162-9](https://doi.org/10.1016/0021-8693(76)90162-9).
  Every numbered result of [CGSS] is in Lean, apart from Remark 2.11, which only points to a
  characterization proved in another paper. So are the computations of the paper, the results of
  other papers that it uses, and the claims that it makes in passing, apart from what it only
  cites.
- **The note *A database of exceptional graphs with least eigenvalue ≥ −2*** (K. Guo), which
  proves that there are exactly 54,732,619 exceptional graphs, that is,
  connected graphs with least eigenvalue at least −2 that are not generalized line graphs, and the
  **database** of all of them, one for each isomorphism class, with the programs that produced
  and checked it. The mathematics of the note is in Lean as well, but note that the computation is not.

## Contents

| Path | Content |
| --- | --- |
| [`LineGraphs/`](LineGraphs) | The Lean library: 632 modules, about 82,500 lines. |
| [`LineGraphs/Exceptional/`](LineGraphs/Exceptional) | The Lean of Sections 2 and 3 of the note. |
| [`dependency-diagram.md`](dependency-diagram.md) | The results of [CGSS] and of the note, how they depend on each other, and their Lean declarations. |
| [`blueprint/`](blueprint) | Structured proofs, in the style of Lamport, of every result of [CGSS], with the Lean name of each step ([`blueprint.pdf`](blueprint/blueprint.pdf)). |
| [`cgss/errata.md`](cgss/errata.md), [`cgss/errors.pdf`](cgss/errors.pdf) | The errors that we found in [CGSS], and their repairs. |
| [`cgss/notation.md`](cgss/notation.md) | The dictionary from the notation of [CGSS] to the blueprint and to the Lean names. |
| [`cgss/prerequisites.md`](cgss/prerequisites.md) | The results from outside [CGSS] that the formalization needs, and where they are proved. |
| [`cgss/proofs/remark311/`](cgss/proofs/remark311), [`cgss/proofs/thm312/`](cgss/proofs/thm312), [`cgss/proofs/hallconnor/`](cgss/proofs/hallconnor), [`cgss/proofs/clebsch/`](cgss/proofs/clebsch), [`cgss/proofs/reg8/`](cgss/proofs/reg8), [`cgss/proofs/spectraltools/`](cgss/proofs/spectraltools) | Ordinary proofs behind parts of the blueprint: the classification behind Remark 3.11, Theorem 3.12, the nonexistence of a 2-(15,5,2) design, the Clebsch and Schläfli graphs, the regular graphs of valency at most 3 on 8 vertices, and a spectral toolkit; with their check scripts. |
| [`cgss/certificates/`](cgss/certificates) | The SageMath scripts that found the certificates of the computations of [CGSS], with the certificates, which the Lean checks. |
| [`LineGraphs/AUDIT-statements.md`](LineGraphs/AUDIT-statements.md) | The statement audit: every Lean statement compared with [CGSS] and with the note, with each difference and its reason (as of 9 October 2026). |
| [`exceptional/note/`](exceptional/note) | The note, its source and [PDF](exceptional/note/exceptional.pdf). |
| [`exceptional/database/`](exceptional/database) | The database of the exceptional graphs and its programs; see its [README](exceptional/database/README.md). |

## Building the Lean

Install [elan](https://github.com/leanprover/elan). Then, at the root of the repository,

```
lake exe cache get
lake build
lake build LineGraphs.Audit LineGraphs.Exceptional.Audit
```

The first command downloads the compiled Mathlib, the second builds the library, and the third
prints, with `#print axioms`, the axioms of the main declarations. The toolchain is fixed in
`lean-toolchain` (Lean `v4.34.0-rc2`) and the version of Mathlib in `lake-manifest.json`
(commit `082e2d37`, 4 September 2026). The library contains no `sorry`, no added axiom and no
`native_decide`, and its main declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`.

## Rebuilding the PDFs

Every PDF is included. The structured proofs (`blueprint/blueprint.tex` and the files
`*-lamport.tex` in `cgss/proofs/`) use Leslie Lamport's package for structured proofs, which we do
not redistribute: to rebuild them, download
[`pf2.sty`](https://lamport.azurewebsites.net/latex/pf2.sty) into the directory of the document
first. The note needs the package `fullpage`, which is in every standard TeX distribution.

## The database

The files are in `exceptional/database/`: `minus2/` holds the exceptional graphs with least
eigenvalue −2 (54,732,046 of them, on 7 to 36 vertices), `above-minus2/` those with least
eigenvalue greater than −2 (573, on 6, 7 and 8 vertices), and `maximal/` the 473 maximal
exceptional graphs, one file for each number of vertices (two for 19, 20 and 21 vertices in
`minus2/`), with one canonical graph6 string per line. The files take about 770 MB; check them with `sha256sum -c SHA256SUMS` in that directory.
The [README](exceptional/database/README.md) there, and Appendix C of the note, say how to read
the files, how to regenerate them, and how to verify them.

## Citing

Please cite the note, K. Guo, *A database of exceptional graphs with least eigenvalue ≥ −2*
(in [`exceptional/note/`](exceptional/note)), and this repository,
https://github.com/kguo-sagecode/least-eig-minus-2.

## Licences

Copyright © 2026 Krystal Guo, University of Amsterdam.

The Lean files, the Lake configuration and the programs and scripts (`.lean`, `.py`, `.sage`,
`.sh`) are under the Apache License 2.0, the licence of Mathlib ([`LICENSE`](LICENSE)). The note,
the blueprint, the other write-ups and documentation (`.tex`, `.pdf`, `.md`) and the database
(the graph lists, `counts.json`, `SHA256SUMS` and the certificates, `.json`) are under the Creative Commons Attribution 4.0
International licence ([`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0)). The scan of [CGSS] and its transcriptions are not
included; we cite [CGSS] by its DOI.

## Author

This formalization and the database are by Krystal Guo, Korteweg-de Vries Institute for
Mathematics, University of Amsterdam, k.guo@uva.nl.

## Models used

We produced the formalization and the code with language-model agents. Orchestration was done by
Claude Opus 5.5 in Claude Code. GPT-6 Astra, in Codex, wrote and reviewed most of the Lean. Claude
Opus 5.5 agents wrote the structured proofs and the rest of the Lean, reviewed the drafts without
editing them, and audited the Lean statements against [CGSS] and the note, statement by
statement, recording every difference and its reason; Claude also helped draft the text of the
note. The agents wrote the proofs; Lean checks them.

## Acknowledgements

We thank SURF ([www.surf.nl](https://www.surf.nl)) for the support in using the National
Supercomputer Snellius. Anthropic supported this work through access to Claude under the Claude
Team for Scientists program.
