# E20 Sorry Inventory

Last checked: 2026-04-21.

The E20 target builds, but the following compendium declarations still use
`sorry`. They are intentionally left visible rather than replaced by fake proofs.

- `Compendium/Models/CodeModels.lean:52`
- `Compendium/Models/CodeModels.lean:63`
- `Compendium/Models/CodeModels.lean:78`

The previously open `RecursiveClosure.lean` placeholder from the archive has
been replaced by a checked proof of `recursive_closure_bound`.
The previously open Proposition 4.3 placeholder in `TraceRecursion.lean` has
been replaced by a checked proof of `support_piece_universality`.
The recurrence placeholders in `TraceRecursion.lean`, `HeavySet.lean`, and
`LPCovers.lean` have been replaced by checked proofs.  The two uses of
`sunflowerNumber` as an actual extremal maximum now make the required boundedness
of the defining supremum explicit, and the LP cover recurrence now includes the
needed hypothesis that the selected heavy block has size at most the ambient
uniformity.
