# erdos885_forum_note.tex

A self-contained LaTeX forum-note reporting **only** the fully formalized
findings from the Erdős Problem E885 Lean project.

## Scope

The note covers exactly two partial results, each backed by machine-checked Lean 4
proofs:

1. **Anchored 3-shift cap counterexample** — the explicit packet behind
   `|Y(a,b,c)| \ge 5`, using `new_3row_5col_packet` in
   `AddendumComputations.lean`).

2. **Guidepost rigidity** — a finite-sieve proof that the seed triple
   (79200, 227205, 1258560) has exactly four positive common secants
   {36, 468, 692, 1028} (`GuidepostRigidity.lean`).

The current note intentionally omits the earlier divisor-template / explicit
4-point section so the forum-facing writeup stays focused on the strongest
standalone statements already supported by Lean.

## Building

```bash
pdflatex erdos885_forum_note.tex
```

No bibliography is needed.
