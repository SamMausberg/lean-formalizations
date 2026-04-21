import Mathlib

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Separator-Compatible Lifting

This file isolates the local hypotheses from the pasted separator note.

We do not prove the separator bridge unconditionally.  Instead, we name the missing hypotheses
explicitly and record the formal implication that a stronger visible-split forcing assumption
immediately yields the weaker separator-compatible lifting statement.
-/

variable {Kernel : Type*}

/-- Visible split forcing is stronger than separator-compatible lifting. -/
theorem visibleSplitForcing_implies_separatorCompatibleLifting
    {IsLarge IsCompatible HasProfitablePrefixBlock : Kernel → Prop}
    (hVS : ∀ K, IsLarge K → HasProfitablePrefixBlock K) :
    ∀ K, IsLarge K → IsCompatible K ∨ HasProfitablePrefixBlock K := by
  intro K hK
  exact Or.inr (hVS K hK)

end FormalConjectures.Problems.Erdos.E20
