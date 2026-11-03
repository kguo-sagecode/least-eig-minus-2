# Blueprint

Structured proofs, in the style of Lamport's *How to write a proof* (1995), for every numbered
result of [CGSS] and for the results from other sources that the formalization needs. The format
and its rules are in `conventions.tex`, which is Section 1 of the blueprint. Lemma 2.8 in
`sec2-lines.tex` is written out in full as the model for the rest.

Compile with

```bash
pdflatex blueprint.tex && pdflatex blueprint.tex
```

## Files

- `blueprint.tex`: the main file; one file per section of the paper (`sec2-lines.tex` to
  `sec6-hadamard.tex`) and `conventions.tex`.
- `macros.tex`: the blueprint's macros. `\lean{...}`, `\uses{...}` and `\leanok` are the macros
  of leanblueprint, as no-ops; the environment `cgss` gives a result the paper's own number;
  `\asm{k}` and `\asm[i]{k}` cite the assumptions $\langle k\rangle$ and $\langle k\rangle{:}i$;
  `\new` and `\repair` are the tags of a step that departs from the paper and of a step that
  fills a gap.
- `pf2.sty` (not included): Lamport's package for structured proofs, version of 27 September
  2011; download it from <https://lamport.azurewebsites.net/latex/pf2.sty> into this directory
  before building (it is not on CTAN or in the system TeX).
  The comments at the top of `pf2.sty` document every command. Since `amsart` loads `amsthm`,
  `blueprint.tex` undefines `amsthm`'s `proof` environment and `\qed` before loading `pf2`.
- `checks/`: exact sanity checks, in Python, of the finite data of some sections:
  `sec2/check_sec2.py`, `sec3/check_sec3.py` and `sec6/check_sec6.py` for Sections 2, 3 and 6,
  and `hallconnor/` and `thm312/` for the Hall–Connor theorem and Theorem 3.12, each with a
  README. They are not proofs, and the Lean proofs do not use them.
