import FormalConjectures.Problems.Erdos.E61.PathProfiles
import FormalConjectures.Problems.Erdos.E61.Substitution

/-!
# Safe singleton profiles

This file connects the checked one-vertex path-profile classification with the
checked substitution theorem.  It proves the singleton safe-profile direction
under the explicit local hypothesis that the forbidden path is prime.
-/

namespace Erdos61

open Finset

/--
Singleton safe profile closure under substitution, assuming path primeness.

If the one-vertex profile `S` is not one of the two endpoint singletons, then
`oneVertexExtension S` is `P_{n+2}`-free.  If `P_{n+2}` is prime, substituting
any other `P_{n+2}`-free graph for the added vertex preserves freeness.
-/
theorem singleton_safe_profile_substitution
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (n + 1)))
    (hS : S ≠ ({0} : Finset (Fin (n + 1))) ∧
      S ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))))
    {VB : Type*} (B : SimpleGraph VB)
    (hprime : PrimeGraph (SimpleGraph.pathGraph (n + 2)))
    (hB : InducedFree (SimpleGraph.pathGraph (n + 2)) B) :
    InducedFree (SimpleGraph.pathGraph (n + 2))
      (substituteVertex (oneVertexExtension S) B (none : Option (Fin (n + 1)))) := by
  have hbase : InducedFree (SimpleGraph.pathGraph (n + 2)) (oneVertexExtension S) := by
    exact (oneVertexExtension_pathFree_iff_not_endpoint_singleton n hn S).mpr hS
  exact substituteVertex_inducedFree_of_prime hprime hbase hB

end Erdos61
