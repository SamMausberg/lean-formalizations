import FormalConjectures.Problems.Erdos.E119.Findings.Defs

/-!
# Erdős 119 Findings: Fixed-Center Coherence

This file formalizes the additive recursion and weighted defect identity from the repaired
fixed-center theorem in the user-supplied source note.
-/

open scoped BigOperators

namespace Erdos119
namespace Findings

/--
Formalizes the observation from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7 ("Fixed-center coherence"), that the shell increment measured from the inner edge to
itself is exactly zero.
-/
theorem shellIncrement_at_innerEdge {α R : Type*} [Ring R] (f : α → R) (x : α) :
    f x - f x = 0 := by
  exact sub_self (f x)

/--
Formalizes the obstruction from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7: no shell condition of the form `increment ≤ -δ` can hold at the inner edge when
`δ > 0`, because the increment there is exactly zero.
-/
theorem noPositiveMarginAtInnerEdge {α : Type*} (f : α → ℝ) (x : α)
    {δ : ℝ} (hδ : 0 < δ) : ¬ (f x - f x ≤ -δ) := by
  have hnot : ¬ (0 : ℝ) ≤ -δ := by
    linarith
  simpa [shellIncrement_at_innerEdge] using hnot

/--
Formalizes the additive recursion underlying the repaired trimmed fixed-center theorem in
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7: a base inequality `B m ≤ 0` together with one-step decrements
`B j ≤ B (j + 1) - δ j` forces the cumulative bound
`B j ≤ -∑_{k=j}^{m-1} δ_k`.
-/
theorem additiveNegativeBudget {m : ℕ}
    {B δ : ℕ → ℝ} (hbase : B m ≤ 0) (hstep : ∀ j < m, B j ≤ B (j + 1) - δ j) :
    ∀ j ≤ m, B j ≤ -tailSum m δ j := by
  intro j hj
  refine Nat.decreasingInduction' (P := fun k => B k ≤ -tailSum m δ k)
    (fun k hk _ ih => ?_) hj ?_
  · calc
      B k ≤ B (k + 1) - δ k := hstep k hk
      _ ≤ -tailSum m δ (k + 1) - δ k := by gcongr
      _ = -tailSum m δ k := by
            rw [tailSum_step δ hk]
            ring
  · simpa [tailSum_top] using hbase

/--
Formalizes the weighted identity
`∑_{j=1}^m Δ_j = ∑_{k=1}^m k δ_k`
from `FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7, in zero-based indexing over a semiring.
-/
theorem sum_tailSum_eq_weighted_sum (δ : ℕ → ℝ) (m : ℕ) :
    Finset.sum (Finset.range m) (fun j => tailSum m δ j) =
      Finset.sum (Finset.range m) (fun k => ((k + 1 : ℕ) : ℝ) * δ k) := by
  simpa [nsmul_eq_mul] using (sum_tailSum_eq_sum_nsmul δ m)

end Findings
end Erdos119
