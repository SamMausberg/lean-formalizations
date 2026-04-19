# Erdős Problem E885 — Formal Findings Writeup

## File

- **`erdos885_findings_writeup.tex`** — Self-contained LaTeX source.

## Compilation

```bash
pdflatex erdos885_findings_writeup.tex
```

No BibTeX pass is needed (references use `thebibliography`). The document
requires only standard packages: `amsmath`, `amssymb`, `amsthm`, `hyperref`,
`enumitem`, `geometry`, `mathtools`.

## Structure

| Section | Content |
|---------|---------|
| 1 | Introduction and problem status |
| 2 | Formal problem statement and notation |
| 3 | Verified witnesses for k=2, k=3, and the 3×4 configuration |
| 4 | Square-discriminant reformulation |
| 5 | Pair-fiber finiteness and parametrization |
| 6 | Anchored packets, column/cocycle/transfer laws |
| 7 | B-set and spectrum viewpoint |
| 8 | Row-complex and terminal-spectrum |
| 9 | Square-translate geometry and genus computations |
| 10 | Shift-transpose |
| 11 | Divisor templates and projective obstructions |
| 12 | Obstruction descent |
| 13 | Guidepost rigidity |
| 14 | Lift-surface computations |
| 15 | Addendum computations and counterexamples |
| 16 | Summary: exact / partial / open |

## Relationship to Lean files

The writeup is based on the Lean files under
`FormalConjectures/Problems/Erdos/E885/Findings/` and `Main.lean`.
File-level attribution (e.g. "formalized in `SquareDiscriminant.lean`")
appears throughout the document.
