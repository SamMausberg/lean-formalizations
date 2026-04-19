# FormalConjectures

Lean 4 + mathlib workspace for formalizing research problems, currently organized around Erdős
problems `E119` and `E885`.

## Prerequisites

Install the Lean toolchain manager once:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
```

Then load the shell environment and fetch cached mathlib artifacts:

```bash
source "$HOME/.elan/env"
lake exe cache get
lake build
```

## Layout

- `FormalConjectures/Util/ProblemImports.lean`: shared imports and theorem statement helpers
- `FormalConjectures/Util/Attributes.lean`: lightweight metadata attributes used in problem files
- `FormalConjectures/Problems/Erdos/E119/`: working files for Erdős Problem 119
- `FormalConjectures/Problems/Erdos/E885/`: working files for Erdős Problem 885

## Common commands

```bash
source "$HOME/.elan/env"
lake build
lake env lean FormalConjectures/Problems/Erdos/E119/Main.lean
```

## Aristotle CLI

The repo includes a pinned Aristotle wrapper for the E885 writeup flow:

```bash
export ARISTOTLE_API_KEY=...
./scripts/run_aristotle_e885_writeup.sh
```

This uses `uvx --from aristotlelib@1.0.1 aristotle ...`, stages a small E885-focused
project bundle under `artifacts/`, and downloads the result there.

## Notes

- `lean-toolchain` is pinned to mathlib's current toolchain so dependency resolution stays aligned
  with upstream.
- The current `E119` file is intentionally scaffolded with `sorry`, which lets the project build
  while you work theorem-by-theorem.
