import FormalConjectures.Problems.Erdos.E20.Kernels.SeparatorLifting
import FormalConjectures.Problems.Erdos.E20.Recurrences.RecurrenceReduction

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

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

section CompatibilityToRigidity

variable {State ι Choice : Type*}
  [DecidableEq ι] [Fintype ι] [Fintype State] [Fintype Choice]

/-- A finite distinguisher skeleton.

The `ι`-indexed local choice data separates all distinct states.  In the intended application,
`ι` is the quasi-laminar family of minimal distinguishers. -/
structure DistinguisherSkeleton where
  localChoice : ι → State → Choice
  separates : ∀ {x y : State}, x ≠ y → ∃ i : ι, localChoice i x ≠ localChoice i y

namespace DistinguisherSkeleton

variable (S : DistinguisherSkeleton (State := State) (ι := ι) (Choice := Choice))

/-- The local choice code is injective. -/
theorem code_injective :
    Function.Injective (fun x : State => fun i : ι => S.localChoice i x) := by
  cases S with
  | mk localChoice separates =>
      intro x y hxy
      by_contra hne
      rcases separates hne with ⟨i, hi⟩
      exact hi (congrArg (fun f : ι → Choice => f i) hxy)

/-- A finite distinguisher skeleton codes the state space into a finite product of local choice
sets. -/
theorem card_state_le_code_space :
    (S : DistinguisherSkeleton (State := State) (ι := ι) (Choice := Choice)) →
      Fintype.card State ≤ Fintype.card Choice ^ Fintype.card ι := by
  intro S
  classical
  cases S with
  | mk localChoice separates =>
      have hcard := Fintype.card_le_of_injective
        (fun x : State => fun i : ι => localChoice i x)
        (by
          intro x y hxy
          by_contra hne
          rcases separates hne with ⟨i, hi⟩
          exact hi (congrArg (fun f : ι → Choice => f i) hxy))
      have hfun : Fintype.card (ι → Choice) = Fintype.card Choice ^ Fintype.card ι := by
        exact (Fintype.card_fun (α := ι) (β := Choice))
      simpa [hfun] using hcard

/-- Compatibility-to-rigidity via a linear-size distinguisher skeleton.

This is the abstract Myhill--Nerode counting step from the pasted compatibility note: once the
minimal distinguishers form a finite skeleton of linear size, the state space is at most
exponential in that linear bound. -/
theorem card_state_le_pow_of_linear_skeleton
    (S : DistinguisherSkeleton (State := State) (ι := ι) (Choice := Choice))
    {B C m : ℕ}
    (hChoice : Fintype.card Choice ≤ B) (hSkeleton : Fintype.card ι ≤ C * m)
    (hB : 1 ≤ B) :
    Fintype.card State ≤ B ^ (C * m) := by
  calc
    Fintype.card State ≤ Fintype.card Choice ^ Fintype.card ι :=
      card_state_le_code_space S
    _ ≤ B ^ Fintype.card ι := by
      exact Nat.pow_le_pow_left hChoice _
    _ ≤ B ^ (C * m) := by
      exact Nat.pow_le_pow_right hB hSkeleton

end DistinguisherSkeleton

end CompatibilityToRigidity

end FormalConjectures.Problems.Erdos.E20
