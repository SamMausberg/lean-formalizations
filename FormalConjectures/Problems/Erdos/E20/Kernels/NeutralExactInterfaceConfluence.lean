import FormalConjectures.Problems.Erdos.E20.Kernels.SeparatorLifting
import FormalConjectures.Problems.Erdos.E20.Kernels.UniversalRouting

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Neutral Exact-Interface Confluence

This file records the abstract interface layer suggested by the pasted neutral
exact-interface note.

We do not model the transport groupoid itself here.  Instead, we package the
only logical consequence used downstream: a neutral interface dichotomy that
returns either compatibility or a profitable prefix block already gives the
same solved-or-profitable conclusion as the routing reduction.
-/

variable {Kernel : Type*}

/-- The neutral exact-interface confluence interface: every large kernel is
either compatible or already carries a profitable prefix block. -/
def NeutralExactInterfaceConfluence
    {IsLarge IsCompatible HasProfitablePrefixBlock : Kernel → Prop} : Prop :=
  ∀ K, IsLarge K → IsCompatible K ∨ HasProfitablePrefixBlock K

/-- Visible split forcing gives the neutral exact-interface confluence interface. -/
theorem visibleSplitForcing_implies_neutralExactInterfaceConfluence
    {IsLarge IsCompatible HasProfitablePrefixBlock : Kernel → Prop}
    (hVS : ∀ K, IsLarge K → HasProfitablePrefixBlock K) :
    NeutralExactInterfaceConfluence (Kernel := Kernel)
      (IsLarge := IsLarge) (IsCompatible := IsCompatible)
      (HasProfitablePrefixBlock := HasProfitablePrefixBlock) := by
  intro K hK
  exact Or.inr (hVS K hK)

/-- The neutral exact-interface interface feeds directly into universal routing. -/
theorem universalRouting_of_neutralExactInterfaceConfluence
    {IsLarge IsCompatible IsSolved HasProfitablePrefixBlock : Kernel → Prop}
    (hCR : ∀ K, IsCompatible K → IsSolved K)
    (hNE : NeutralExactInterfaceConfluence (Kernel := Kernel)
      (IsLarge := IsLarge) (IsCompatible := IsCompatible)
      (HasProfitablePrefixBlock := HasProfitablePrefixBlock)) :
    ∀ K, IsLarge K → IsSolved K ∨ HasProfitablePrefixBlock K := by
  exact universalRouting_of_compatibilityToRigidity_and_separatorCompatibleLifting
    (Kernel := Kernel) (IsLarge := IsLarge) (IsCompatible := IsCompatible)
    (IsSolved := IsSolved) (HasProfitablePrefixBlock := HasProfitablePrefixBlock)
    hCR hNE

end FormalConjectures.Problems.Erdos.E20
