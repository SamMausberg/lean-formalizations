import FormalConjectures.Problems.Erdos.E20.Kernels.SeparatorLifting
import FormalConjectures.Problems.Erdos.E20.Recurrences.RecurrenceReduction

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Universal Routing Reduction

This file formalizes the conditional reduction skeleton from the pasted universal-routing notes.

The key point is that we only record the logical dependencies:

* universal routing is a solved-or-profitable dichotomy;
* compatibility-to-rigidity is a separate missing hypothesis;
* visible split forcing is a stronger local assumption implying separator-compatible lifting;
* the downstream numerical bounds come from the existing terminal-kernel and profitable-drop
  lemmas once the relevant hypotheses are supplied.

No claim is made here that the open sunflower conjecture holds unconditionally.
-/

/-- A visible-split theorem together with rigidity collapses the routing field to the universal
solved-or-profitable dichotomy. -/
theorem universalRouting_of_compatibilityToRigidity_and_separatorCompatibleLifting
    {Kernel : Type*}
    {IsLarge IsCompatible IsSolved HasProfitablePrefixBlock : Kernel → Prop}
    (hCR : ∀ K, IsCompatible K → IsSolved K)
    (hSep : ∀ K, IsLarge K → IsCompatible K ∨ HasProfitablePrefixBlock K) :
    ∀ K, IsLarge K → IsSolved K ∨ HasProfitablePrefixBlock K := by
  intro K hK
  rcases hSep K hK with hcomp | hprof
  · exact Or.inl (hCR K hcomp)
  · exact Or.inr hprof

/-- The stronger visible-split forcing assumption implies universal routing after the
separator-compatible lifting bridge. -/
theorem universalRouting_of_compatibilityToRigidity_and_visibleSplitForcing
    {Kernel : Type*}
    {IsLarge IsCompatible IsSolved HasProfitablePrefixBlock : Kernel → Prop}
    (hCR : ∀ K, IsCompatible K → IsSolved K)
    (hVS : ∀ K, IsLarge K → HasProfitablePrefixBlock K) :
    ∀ K, IsLarge K → IsSolved K ∨ HasProfitablePrefixBlock K := by
  exact universalRouting_of_compatibilityToRigidity_and_separatorCompatibleLifting
    (Kernel := Kernel) (IsLarge := IsLarge) (IsCompatible := IsCompatible)
    (IsSolved := IsSolved) (HasProfitablePrefixBlock := HasProfitablePrefixBlock)
    hCR (visibleSplitForcing_implies_separatorCompatibleLifting (Kernel := Kernel) hVS)

/-- The profitable-prefix framework gives the usual exponential bound once the recurrence and
initial segment bounds are supplied. -/
theorem profitablePrefixFramework_implies_exponentialBound
    (M : ℕ → ℝ) (A Λ C : ℝ) (T : ℕ)
    (hA : 1 ≤ A) (hΛ : 1 ≤ Λ) (hC : A * Λ < C)
    (hnonneg : ∀ r, 0 ≤ M r)
    (hbase : ∀ r, r ≤ T → M r ≤ C ^ r)
    (hprof : HasProfitableDropRecurrence M A Λ T) :
    ∀ r, M r ≤ C ^ r := by
  simpa using
    (exponential_bound_of_hasProfitableDropRecurrence M A Λ C T hA hΛ hC hnonneg hbase hprof)

end FormalConjectures.Problems.Erdos.E20
