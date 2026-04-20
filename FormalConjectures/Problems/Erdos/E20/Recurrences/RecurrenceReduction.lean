import Mathlib

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Profitable-Drop Recurrence Reductions

This file packages the exact induction step used repeatedly in the user's E20 notes:

if a maximal size function `M(r)` admits a recursive drop

`M(r) ≤ A * Λ^b * M(r - T - b)` with some `b ≥ 1`,

then any constant `C` with `A * Λ < C` already yields an exponential bound `M(r) ≤ C^r`.

The extra shift `T` only helps, so the proof is a clean strong induction.
-/

open scoped BigOperators

/-- Abstract profitable-drop recurrence. -/
def HasProfitableDropRecurrence (M : ℕ → ℝ) (A Λ : ℝ) (T : ℕ) : Prop :=
  ∀ r, T < r → ∃ b : ℕ, 1 ≤ b ∧ b ≤ r - T ∧ M r ≤ A * Λ ^ b * M (r - T - b)

/-- If a nonnegative sequence satisfies a profitable-drop recurrence and is bounded on the initial
segment `r ≤ T`, then any `C` with `A * Λ < C` dominates the whole sequence exponentially.

This is the exact arithmetic backbone behind the user's "`(⋆_k)` implies `f(n,k) ≤ c_k^n`"
reduction. -/
theorem exponential_bound_of_profitableDrop
    (M : ℕ → ℝ) (A Λ C : ℝ) (T : ℕ)
    (hA : 1 ≤ A) (hΛ : 1 ≤ Λ) (hC : A * Λ < C)
    (hnonneg : ∀ r, 0 ≤ M r)
    (hbase : ∀ r, r ≤ T → M r ≤ C ^ r)
    (hrec : HasProfitableDropRecurrence M A Λ T) :
    ∀ r, M r ≤ C ^ r := by
  have hC_one : 1 < C := by
    have hAΛ : 1 ≤ A * Λ := by nlinarith
    linarith
  have hC_pos : 0 < C := by linarith
  have hΛ_lt_C : Λ < C := by
    have hΛ_le_AΛ : Λ ≤ A * Λ := by
      nlinarith
    linarith
  have hΛ_le_C : Λ ≤ C := le_of_lt hΛ_lt_C
  intro r
  induction' r using Nat.strong_induction_on with r ih
  by_cases hr : r ≤ T
  · exact hbase r hr
  · have hTr : T < r := lt_of_not_ge hr
    rcases hrec r hTr with ⟨b, hb, hb_le, hstep⟩
    have hsub_lt : r - T - b < r := by
      omega
    have hIH := ih (r - T - b) hsub_lt
    have hb' : ∃ d : ℕ, b = d + 1 := by
      exact ⟨b - 1, by omega⟩
    rcases hb' with ⟨d, rfl⟩
    calc
      M r ≤ A * Λ ^ (d + 1) * M (r - T - (d + 1)) := hstep
      _ ≤ A * Λ ^ (d + 1) * C ^ (r - T - (d + 1)) := by
        gcongr
      _ = (A * Λ) * Λ ^ d * C ^ (r - T - (d + 1)) := by
        rw [pow_succ]
        ring
      _ ≤ C * Λ ^ d * C ^ (r - T - (d + 1)) := by
        gcongr
      _ ≤ C * C ^ d * C ^ (r - T - (d + 1)) := by
        have hΛ_nonneg : 0 ≤ Λ := by linarith
        have _hpowΛC : Λ ^ d ≤ C ^ d :=
          pow_le_pow_left₀ hΛ_nonneg hΛ_le_C d
        gcongr
      _ = C ^ (d + 1) * C ^ (r - T - (d + 1)) := by
        rw [pow_succ]
        ring
      _ = C ^ ((d + 1) + (r - T - (d + 1))) := by
        rw [← pow_add]
      _ = C ^ (r - T) := by
        congr
        omega
      _ ≤ C ^ r := by
        exact pow_le_pow_right₀ hC_one.le (by omega)

/-- A packaged corollary: once one has a profitable-drop recurrence and any exponential control on
the bounded initial segment, the whole sequence is exponentially bounded. -/
theorem exponential_bound_of_hasProfitableDropRecurrence
    (M : ℕ → ℝ) (A Λ C : ℝ) (T : ℕ)
    (hA : 1 ≤ A) (hΛ : 1 ≤ Λ) (hC : A * Λ < C)
    (hnonneg : ∀ r, 0 ≤ M r)
    (hbase : ∀ r, r ≤ T → M r ≤ C ^ r)
    (hrec : HasProfitableDropRecurrence M A Λ T) :
    ∀ r, M r ≤ C ^ r :=
  exponential_bound_of_profitableDrop M A Λ C T hA hΛ hC hnonneg hbase hrec

end FormalConjectures.Problems.Erdos.E20
