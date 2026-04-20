This directory contains additional Aristotle-imported Lean material from
`748b98b9-e194-4a3f-bf40-3fd2b1873860-aristotle.tar.gz`, reorganized under
`FormalConjectures/Problems/Erdos/E20/Compendium`.

## Layout

- `Core/`
  The compendium-specific definition layer.
- `Recurrences/`
  Trace recursion, heavy-set, LP cover, and recursive-closure modules.
- `Models/`
  Block-product, finite-state, and fixed-alphabet code-model modules.

I imported the archive modules that were not already present in the main `E20`
tree as direct file-level counterparts:

- `Recurrences/TraceRecursion.lean`
- `Recurrences/HeavySet.lean`
- `Recurrences/LPCovers.lean`
- `Models/BlockProducts.lean`
- `Models/FiniteState.lean`
- `Models/CodeModels.lean`
- `Recurrences/RecursiveClosure.lean`

The archive uses a distinct core definition layer, so that support file lives here
as `Compendium/Core/Defs.lean` rather than being merged into the existing
`E20/Foundations/Defs.lean`.

I did not duplicate the archive's top-level `Main.lean`, `LeafStripping.lean`, or
`Correlation.lean` into this subtree because `E20` already has corresponding files
covering those names/themes. The imported compendium files are namespaced under
`FormalConjectures.Problems.Erdos.E20.Compendium` to avoid collisions with the main
`E20` development.

Attribution for the source archive: Aristotle, <https://aristotle.harmonic.fun>,
GitHub `@Aristotle-Harmonic`.
