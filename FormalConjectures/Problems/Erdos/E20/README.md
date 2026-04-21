This directory contains the organized Lean development for Erdős problem `E20`.

## Layout

- `Foundations/`
  Core decomposition, seed-profile, correlation, branching, cover criteria,
  obstruction, example, and gap-analysis modules.
- `Families/`
  Explicit counterexample and extremal family constructions.
- `Kernels/`
  Leaf-stripping, kernel bounds, and terminal-kernel reductions.
- `Recurrences/`
  Projection transfer, tuple-state branching, profitable-drop recurrences, and
  automaton-style counting arguments.
- `Tensors/`
  Explicit local tensor and diagonal support arguments.
- `Compendium/`
  Additional Aristotle-imported sunflower-compendium modules, split into
  `Core/`, `Recurrences/`, and `Models/`.
- `SORRY_INVENTORY.md`
  Current list of compendium declarations that still use `sorry`.

## Entry points

- `Main.lean` imports the organized `E20` development.
- `InformalMap.lean` restates the main pasted informal claims against the
  current formal library.
- `Compendium.lean` imports the organized Aristotle compendium subtree.

## Verification status

`lake build FormalConjectures.Problems.Erdos.E20.Main` succeeds. The E20 Lean
sources are currently `sorry`-free; see `SORRY_INVENTORY.md`.

## Attribution

Parts of this directory were imported from archived Aristotle runs.
To cite Aristotle:

- Tag `@Aristotle-Harmonic` on GitHub PRs/issues.
- Add as co-author to commits:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
