import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Verified Small Examples and Supporting Computations

This file formalizes the verified computations from Section 3 of
`erdos885_notes.tex`. These declarations mainly record explicit
factor-difference memberships and arithmetic checks used in the examples.
-/

/-! ## Helper: decidable factor-difference membership -/

/-- A decidable version of `d ∈ D(n)`: checks whether there exist `a` with
`1 ≤ a`, `a ∣ n`, and `n / a - a = d` or `a - n / a = d`. -/
def inFactorDiffSet (d n : ℕ) : Bool :=
  ((Finset.range n).filter fun a =>
    let a' := a + 1
    a' ∣ n ∧ (n / a' - a' = d ∨ a' - n / a' = d)).card > 0

/-
Correctness of the decidable factor-difference test.
-/
set_option maxHeartbeats 4000000 in
-- The backward direction case-splits on explicit factor witnesses from the finite search encoding.
set_option linter.flexible false in
theorem inFactorDiffSet_iff_mem {d n : ℕ} (hn : 0 < n) :
    inFactorDiffSet d n = true ↔ d ∈ factorDiffSet n := by
  unfold inFactorDiffSet factorDiffSet
  constructor <;> intro h
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by simpa using h)
    refine ⟨a + 1, n / (a + 1), Nat.succ_pos _, ?_, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hn (by aesop)) (Nat.succ_pos _)
    · exact Nat.mul_div_cancel' (by aesop)
    · exact by aesop
  · simp +zetaDelta at *
    obtain ⟨a, ha, b, hb, rfl, h | h⟩ := h
    · refine ⟨a - 1, ?_⟩
      rcases a with _ | _ | a <;> simp_all +decide
      nlinarith
    · refine ⟨b - 1, ?_⟩
      rcases b with _ | _ | b <;> simp_all +decide
      nlinarith

/-! ## Computation 3.1: The first nontrivial pair -/

/-
**Computation 3.1** (erdos885_notes.tex, §3, "the first nontrivial pair").
`1 ∈ D(12)`: since `12 = 3 × 4`, the difference `4 - 3 = 1`.
-/
theorem one_mem_factorDiffSet_12 : 1 ∈ factorDiffSet 12 := by
  use 3, 4
  norm_num

/-
**Computation 3.1** (continued). `11 ∈ D(12)`: since `12 = 1 × 12`,
the difference `12 - 1 = 11`.
-/
theorem eleven_mem_factorDiffSet_12 : 11 ∈ factorDiffSet 12 := by
  use 1, 12
  norm_num

/-
**Computation 3.1** (continued). `1 ∈ D(42)`: since `42 = 6 × 7`,
the difference `7 - 6 = 1`.
-/
theorem one_mem_factorDiffSet_42 : 1 ∈ factorDiffSet 42 := by
  use 6, 7
  norm_num

/-
**Computation 3.1** (continued). `11 ∈ D(42)`: since `42 = 3 × 14`,
the difference `14 - 3 = 11`.
-/
theorem eleven_mem_factorDiffSet_42 : 11 ∈ factorDiffSet 42 := by
  use 3, 14
  norm_num

/-
**Computation 3.1** (continued). `1 ∈ D(210)`: since `210 = 14 × 15`,
the difference `15 - 14 = 1`.
-/
theorem one_mem_factorDiffSet_210 : 1 ∈ factorDiffSet 210 := by
  use 14, 15
  norm_num

/-
**Computation 3.1** (continued). `11 ∈ D(210)`: since `210 = 10 × 21`,
the difference `21 - 10 = 11`.
-/
theorem eleven_mem_factorDiffSet_210 : 11 ∈ factorDiffSet 210 := by
  use 10, 21
  norm_num

/-- **Computation 3.1** (erdos885_notes.tex, §3). The factorization
`11² - 1² = 120` is verified. -/
theorem pair_fiber_delta : 11 ^ 2 - 1 ^ 2 = 120 := by norm_num

/-! ## Computation 3.2: The first nontrivial triple -/

/-
**Computation 3.2** (erdos885_notes.tex, §3, "the first nontrivial triple").
`6 ∈ D(112)`: since `112 = 8 × 14`, the difference `14 - 8 = 6`.
-/
theorem six_mem_factorDiffSet_112 : 6 ∈ factorDiffSet 112 := by
  use 8, 14
  norm_num

/-
**Computation 3.2** (continued). `54 ∈ D(112)`: since `112 = 2 × 56`,
the difference `56 - 2 = 54`.
-/
theorem fiftyfour_mem_factorDiffSet_112 : 54 ∈ factorDiffSet 112 := by
  use 2, 56
  norm_num

/-
**Computation 3.2** (continued). `111 ∈ D(112)`: since `112 = 1 × 112`,
the difference `112 - 1 = 111`.
-/
theorem oneonone_mem_factorDiffSet_112 : 111 ∈ factorDiffSet 112 := by
  use 1, 112
  norm_num

/-
**Computation 3.2** (continued). `6 ∈ D(952)`: since `952 = 28 × 34`,
the difference `34 - 28 = 6`.
-/
theorem six_mem_factorDiffSet_952 : 6 ∈ factorDiffSet 952 := by
  use 28, 34
  norm_num

/-
**Computation 3.2** (continued). `54 ∈ D(952)`: since `952 = 14 × 68`,
the difference `68 - 14 = 54`.
-/
theorem fiftyfour_mem_factorDiffSet_952 : 54 ∈ factorDiffSet 952 := by
  use 14, 68
  norm_num

/-
**Computation 3.2** (continued). `111 ∈ D(952)`: since `952 = 8 × 119`,
the difference `119 - 8 = 111`.
-/
theorem oneonone_mem_factorDiffSet_952 : 111 ∈ factorDiffSet 952 := by
  use 8, 119
  norm_num

/-
**Computation 3.2** (continued). `6 ∈ D(3240)`: since `3240 = 54 × 60`,
the difference `60 - 54 = 6`.
-/
theorem six_mem_factorDiffSet_3240 : 6 ∈ factorDiffSet 3240 := by
  use 54, 60
  norm_num

/-
**Computation 3.2** (continued). `54 ∈ D(3240)`: since `3240 = 36 × 90`,
the difference `90 - 36 = 54`.
-/
theorem fiftyfour_mem_factorDiffSet_3240 : 54 ∈ factorDiffSet 3240 := by
  use 36, 90
  norm_num

/-
**Computation 3.2** (continued). `111 ∈ D(3240)`: since `3240 = 24 × 135`,
the difference `135 - 24 = 111`.
-/
theorem oneonone_mem_factorDiffSet_3240 : 111 ∈ factorDiffSet 3240 := by
  use 24, 135
  norm_num

/-! ## Computation 3.3: A non-endpoint triple -/

/-
**Computation 3.3** (erdos885_notes.tex, §3, "a non-endpoint triple").
`2 ∈ D(120)`: since `120 = 10 × 12`, the difference `12 - 10 = 2`.
-/
theorem two_mem_factorDiffSet_120 : 2 ∈ factorDiffSet 120 := by
  use 10, 12
  norm_num

/-
**Computation 3.3** (continued). `37 ∈ D(120)`: since `120 = 3 × 40`,
the difference `40 - 3 = 37`.
-/
theorem thirtyseven_mem_factorDiffSet_120 : 37 ∈ factorDiffSet 120 := by
  use 3, 40
  norm_num

/-
**Computation 3.3** (continued). `58 ∈ D(120)`: since `120 = 2 × 60`,
the difference `60 - 2 = 58`.
-/
theorem fiftyeight_mem_factorDiffSet_120 : 58 ∈ factorDiffSet 120 := by
  use 2, 60
  norm_num

/-
**Computation 3.3** (continued). `2 ∈ D(528)`: since `528 = 22 × 24`,
the difference `24 - 22 = 2`.
-/
theorem two_mem_factorDiffSet_528 : 2 ∈ factorDiffSet 528 := by
  use 22, 24
  norm_num

/-
**Computation 3.3** (continued). `37 ∈ D(528)`: since `528 = 11 × 48`,
the difference `48 - 11 = 37`.
-/
theorem thirtyseven_mem_factorDiffSet_528 : 37 ∈ factorDiffSet 528 := by
  use 11, 48
  norm_num

/-
**Computation 3.3** (continued). `58 ∈ D(528)`: since `528 = 8 × 66`,
the difference `66 - 8 = 58`.
-/
theorem fiftyeight_mem_factorDiffSet_528 : 58 ∈ factorDiffSet 528 := by
  use 8, 66
  norm_num

/-
**Computation 3.3** (continued). `2 ∈ D(4488)`: since `4488 = 66 × 68`,
the difference `68 - 66 = 2`.
-/
theorem two_mem_factorDiffSet_4488 : 2 ∈ factorDiffSet 4488 := by
  use 66, 68
  norm_num

/-
**Computation 3.3** (continued). `37 ∈ D(4488)`: since `4488 = 51 × 88`,
the difference `88 - 51 = 37`.
-/
theorem thirtyseven_mem_factorDiffSet_4488 : 37 ∈ factorDiffSet 4488 := by
  use 51, 88
  norm_num

/-
**Computation 3.3** (continued). `58 ∈ D(4488)`: since `4488 = 44 × 102`,
the difference `102 - 44 = 58`.
-/
theorem fiftyeight_mem_factorDiffSet_4488 : 58 ∈ factorDiffSet 4488 := by
  use 44, 102
  norm_num

/-! ## Computation 3.5: A 3×4 configuration -/

/-
**Computation 3.5** (erdos885_notes.tex, §3, "a 3×4 configuration").
The four-element common-difference set for the triple `(13608, 29848, 65968)`.
-/
theorem eighteen_mem_factorDiffSet_13608 : 18 ∈ factorDiffSet 13608 := by
  use 108, 126
  norm_num

theorem eighteen_mem_factorDiffSet_29848 : 18 ∈ factorDiffSet 29848 := by
  use 164, 182
  norm_num

theorem eighteen_mem_factorDiffSet_65968 : 18 ∈ factorDiffSet 65968 := by
  use 248, 266
  norm_num

theorem twoeightytwo_mem_factorDiffSet_13608 : 282 ∈ factorDiffSet 13608 := by
  use 42, 324
  norm_num

theorem twoeightytwo_mem_factorDiffSet_29848 : 282 ∈ factorDiffSet 29848 := by
  use 82, 364
  norm_num

theorem twoeightytwo_mem_factorDiffSet_65968 : 282 ∈ factorDiffSet 65968 := by
  use 152, 434
  norm_num

theorem foursevenseven_mem_factorDiffSet_13608 : 477 ∈ factorDiffSet 13608 := by
  use 27, 504
  norm_num

theorem foursevenseven_mem_factorDiffSet_29848 : 477 ∈ factorDiffSet 29848 := by
  use 56, 533
  norm_num

theorem foursevenseven_mem_factorDiffSet_65968 : 477 ∈ factorDiffSet 65968 := by
  use 112, 589
  norm_num

theorem oneonetwotwo_mem_factorDiffSet_13608 : 1122 ∈ factorDiffSet 13608 := by
  use 12, 1134
  norm_num

theorem oneonetwotwo_mem_factorDiffSet_29848 : 1122 ∈ factorDiffSet 29848 := by
  use 26, 1148
  norm_num

theorem oneonetwotwo_mem_factorDiffSet_65968 : 1122 ∈ factorDiffSet 65968 := by
  use 56, 1178
  norm_num
