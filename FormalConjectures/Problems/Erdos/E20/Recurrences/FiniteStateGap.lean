import FormalConjectures.Problems.Erdos.E20.Recurrences.FiniteStatePrefixes
import FormalConjectures.Problems.Erdos.E20.Recurrences.AutomatonBranches
import FormalConjectures.Problems.Erdos.E20.Recurrences.FixedMemoryBound
import FormalConjectures.Problems.Erdos.E20.Compendium.Models.FiniteState

namespace FormalConjectures.Problems.Erdos.E20

open scoped BigOperators

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Finite-State Gap Statements

This file packages the finite-state content from the pasted note in a form that matches the
current Lean development.

What is proved here is exactly what the surrounding recurrence files already support:

* the finite-state profitable-prefix chain and its ratio form;
* the automaton recurrence `h_A(m,k) ≤ N_*(t) * h_A(m - t,k)`;
* the block-count core of the fixed-state entropy-gap theorem;
* the exact forbidden-block recursion and sharp closed-form bound for fixed-order branches;
* the sliding-window polynomial/root statements needed to phrase the sharp fixed-order story.
-/

/-- The fixed-state block bound used as the combinatorial core of the explicit gap. -/
theorem pasted_finite_state_gap_block_bound
    (q m t : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m)
    (S : ℕ) (hS : S ≤ q ^ m - 1) :
    S ^ t ≤ (q ^ m - 1) ^ t := by
  exact Compendium.entropy_gap_block_bound q m t hq hm S hS

/-- The finite-state profitable-prefix chain from the automaton transfer recursion. -/
theorem pasted_finite_state_gap_profitable_chain
    {Q E : Type*} [Fintype Q] [DecidableEq Q] [Fintype E] [DecidableEq E]
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hsuper : A.IsSuperharmonic h Λ) (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q)
    {n : ℕ} {s : Q} (hcount : 0 < A.continuationCount n s) :
    ∃ q : EdgeShift.StateChain Q n, ∃ e : EdgeShift.EdgeChain E n,
      q 0 = s ∧
      (∀ i : Fin n, e i ∈ A.outEdges (q i.castSucc) ∧ A.dst (e i) = q i.succ) ∧
      ∀ t : Fin (n + 1), A.phi h Λ (n - t) (q t) ≥ A.phi h Λ n s := by
  exact A.exists_phi_chain hsuper hΛ hh hcount

/-- The automaton recurrence packaged in the `HasProfitableDropRecurrence` style. -/
theorem pasted_finite_state_gap_automaton_recurrence
    {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]
    (A : PartialDFA Q σ) {m t k : ℕ} (ht : t ≤ m) :
    A.hA m k ≤ A.NStar t * A.hA (m - t) k := by
  exact A.hA_recurrence ht

/-- The ratio form of the profitable-prefix theorem. -/
theorem pasted_finite_state_gap_automaton_ratio
    {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]
    (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    ∃ u ∈ A.admissibleWords q t,
      (1 : ℚ) / (A.NStar t : ℚ) ≤
        ((A.prefixFiber q t s u).card : ℚ) / (A.continuationCount (t + s) q : ℚ) := by
  exact A.exists_heavy_prefix_ratio hcount

/-- The exact `r`-step recursion for a fixed forbidden block. -/
theorem pasted_finite_state_gap_fixed_order_add_le
    (q r : ℕ) (X : FixedMemoryBranch q r) (n : ℕ) :
    (X.language (n + r)).card ≤ (q ^ r - 1) * (X.language n).card := by
  exact X.card_language_add_le n

/-- The sharp closed form for a fixed forbidden block. -/
theorem pasted_finite_state_gap_fixed_order_bound
    (q r : ℕ) (X : FixedMemoryBranch q r) (n : ℕ) :
    (X.language n).card ≤ q ^ (n % r) * (q ^ r - 1) ^ (n / r) := by
  exact X.card_language_bound n

/-- The polynomial identity used to rewrite the fixed-order root equation. -/
theorem pasted_finite_state_gap_polynomial_equiv
    (q r : ℕ) (hq : 2 ≤ q) (hr : 1 ≤ r)
    (lam : ℝ) (hlam : lam > 0) (hlam1 : lam ≠ 1) :
    lam ^ (r + 1) - (q : ℝ) * lam ^ r + ((q : ℝ) - 1) = 0 ↔
      lam ^ r * (lam - 1) = ((q : ℝ) - 1) * (lam ^ r - 1) := by
  exact Compendium.sliding_window_polynomial_equiv q r hq hr lam hlam hlam1

/-- The corrected root-existence statement for the fixed-order polynomial. -/
theorem pasted_finite_state_gap_root_exists (q r : ℕ) (hq : 2 ≤ q) (hr : 1 ≤ r) :
    ∃ lam : ℝ, (q : ℝ) - 1 ≤ lam ∧ lam < (q : ℝ) ∧
      lam ^ (r + 1) - (q : ℝ) * lam ^ r + ((q : ℝ) - 1) = 0 := by
  exact Compendium.sliding_window_root_exists q r hq hr

end FormalConjectures.Problems.Erdos.E20
