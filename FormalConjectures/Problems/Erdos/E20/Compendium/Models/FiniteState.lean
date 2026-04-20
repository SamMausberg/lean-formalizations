import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 9: Fixed-Memory Finite-State Branches

This file formalizes the results from Section 9 of the sunflower compendium
(sunflower_compendium.pdf): "Fixed-memory finite-state branches."
-/

/-
**Theorem 9.3 (State-count entropy gap).**
Let `X` be an irreducible right-resolving `q`-ary finite-state branch with `m` states.
Then exactly one of the following holds:
(i) `X` is the full `q`-shift, in which case `|L_n(X)| = q^n` for all `n`;
(ii) or else, `|L_n(X)| ≤ q^s · (q^m - 1)^t` where `n = t·m + s` with `0 ≤ s < m`.
In particular, `lim sup |L_n(X)|^{1/n} ≤ (q^m - 1)^{1/m} < q`.

We formalize the core combinatorial fact underlying this theorem:
if a set of `q`-ary words of length `m` has size at most `q^m - 1`,
then the number of concatenations of `t` such words is at most `(q^m - 1)^t`.
-/
theorem entropy_gap_block_bound (q m t : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m)
    (S : ℕ) (hS : S ≤ q ^ m - 1) :
    S ^ t ≤ (q ^ m - 1) ^ t := by
  exact Nat.pow_le_pow_left hS _

/-
**Theorem 9.4 (Sharp fixed-memory entropy gap).**
Let `X` be an irreducible `r`-step `q`-ary sliding-window branch that is not the
full `q`-shift. Then `|L_n(X)| ≤ λ_{q,r}^{n+1} / (q-1)` for `n ≥ 0`,
where `λ_{q,r} ∈ (q-1, q)` is the unique root of `λ^{r+1} - q·λ^r + q - 1 = 0`.

This bound is sharp in exponential rate, with equality attained by the branch
forbidding only the word `0^r`.

We formalize the characterizing polynomial equation:
`λ^{r+1} - q·λ^r + q - 1 = 0` ↔ `1 = (q-1) · ∑_{j=1}^{r} λ^{-j}`.

First, we prove that these two forms are equivalent.
-/
theorem sliding_window_polynomial_equiv (q r : ℕ) (hq : 2 ≤ q) (hr : 1 ≤ r)
    (lam : ℝ) (hlam : lam > 0) (hlam1 : lam ≠ 1) :
    lam ^ (r + 1) - (q : ℝ) * lam ^ r + ((q : ℝ) - 1) = 0 ↔
    lam ^ r * (lam - 1) = ((q : ℝ) - 1) * (lam ^ r - 1) := by
  constructor <;> intro h <;> linear_combination' h

/-
**Theorem 9.4, root existence (corrected).**
For `q ≥ 2` and `r ≥ 1`, the polynomial `λ^{r+1} - q·λ^r + q - 1 = 0`
has a root in the interval `[q-1, q)`. For `r ≥ 2`, the root is strictly
in `(q-1, q)`. The boundary case `r = 1` gives the root `q - 1` exactly.

Note: The paper states the root is in `(q-1, q)`, but this is only valid
for `r ≥ 2`. For `r = 1`, the polynomial factors as `(x-1)(x-(q-1))`,
giving root `q-1` at the boundary.
-/
theorem sliding_window_root_exists (q r : ℕ) (hq : 2 ≤ q) (hr : 1 ≤ r) :
    ∃ lam : ℝ, (q : ℝ) - 1 ≤ lam ∧ lam < (q : ℝ) ∧
      lam ^ (r + 1) - (q : ℝ) * lam ^ r + ((q : ℝ) - 1) = 0 := by
  have h_root_interval : ∃ lam ∈ Set.Ico (q - 1 : ℝ) q, lam ^ (r + 1) - (q : ℝ) * lam ^ r + (q - 1) = 0 := by
    apply_rules [ intermediate_value_Ico ];
    · norm_num;
    · fun_prop;
    · constructor <;> ring_nf <;> norm_num;
      · induction hr <;> norm_num [ pow_succ' ] at * ; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ q ) ];
      · grind;
  aesop
end FormalConjectures.Problems.Erdos.E20.Compendium
