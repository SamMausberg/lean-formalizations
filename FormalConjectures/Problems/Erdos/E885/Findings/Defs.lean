import Mathlib

/-!
# Erdős Problem #885 — Core Definitions

This file formalizes the core definitions from `erdos885_notes.tex`, Section 1
("Problem statement and basic notation") and Section 6.1 ("The exact recursion").
-/

open Finset

/-- **Definition 1.1** (erdos885_notes.tex, §1).
For a positive integer `n`, its *factor-difference set* is
  `D(n) := { |a - b| : n = a * b, a, b ∈ ℤ_{>0} }`.
We formalize this as the set of positive integers `d` such that there exist
positive integers `a, b` with `a * b = n` and `b - a = d` (taking `a ≤ b` WLOG). -/
def factorDiffSet (n : ℕ) : Set ℕ :=
  {d : ℕ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a * b = n ∧ (b - a = d ∨ a - b = d)}

/-- **Fiber set** (erdos885_notes.tex, §1).
`F(S) := { n ≥ 1 : S ⊆ D(n) }`. The set of positive integers whose
factor-difference set contains every element of `S`. -/
def fiberSet (S : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ S ⊆ factorDiffSet n}

/-- **Sigma set** (erdos885_notes.tex, §1).
`Σ(T) := { n ≥ 1 : T ⊆ D(n) }`. Identical to `fiberSet` but used with a
different notational convention in the notes. -/
abbrev sigmaSet (T : Set ℕ) : Set ℕ := fiberSet T

/-- Decidable membership test for `factorDiffSet` restricted to finite domains.
`d ∈ D(n)` iff there exist `a, b > 0` with `a * b = n` and `|a - b| = d`. -/
def memFactorDiffSet (d n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a * b = n ∧ (b - a = d ∨ a - b = d)
