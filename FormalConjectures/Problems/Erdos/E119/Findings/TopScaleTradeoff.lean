import Mathlib

/-!
# Erdős 119 Findings: Top-Scale Tradeoff Algebra

This file records the exact algebraic identities that drive the top-scale tradeoff discussion
from the user-supplied source note.
-/

namespace Erdos119
namespace Findings

/--
Formalizes the exact swap identity from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9 ("`W` versus parity recursion"), subsection "Local swap identity":
`T_xy - T_yx = (1 - 1 / d) (A_x - A_y)`.
-/
theorem localSwapDifference (Aₓ Aᵧ d : ℝ) :
    (Aₓ + Aᵧ / d) - (Aᵧ + Aₓ / d) = (1 - 1 / d) * (Aₓ - Aᵧ) := by
  by_cases hd : d = 0
  · simp [hd]
  · field_simp [hd]
    ring

/--
Formalizes the exact regular-example simplification from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 6 ("Top-scale tradeoff theorem"), subsection "Exact sharp example at `ε = 0`":
once `N_{q-(t-1)} = 2q / t` is known, the corresponding defect is `1 - 2 / t`.
-/
theorem exactRegularExample_mainTerm {q t : ℝ}
    (hq : q ≠ 0) (ht : t ≠ 0) :
    ((t - 1) / q) * (2 * q / t) - 1 = 1 - 2 / t := by
  field_simp [hq, ht]
  ring

end Findings
end Erdos119
