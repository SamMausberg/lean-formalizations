import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Canonical Divisor-Seed Dynamics and Row Complexes

This file records selected arithmetic identities and example-chain checks from
Section 6 of `erdos885_notes.tex`. It does not formalize the full
`H(T)` / `S(T)` recursion, the exact sum-difference duality, or the complete
row-complex bijection from the notes.
-/

set_option maxHeartbeats 800000

/-! ## Verified chain computations for Examples 6.3–6.6 -/

/-- **Example 6.3** (erdos885_notes.tex, §6.2, "the pair {1,11}").
Verifies the explicit factorizations used in the notes to show that `12`
supports differences `1` and `11`. -/
theorem chain_pair_1_11_H : 3 * 4 = 12 ∧ (4 : ℕ) - 3 = 1 ∧ (12 : ℕ) - 1 = 11 := by
  omega

/-- **Example 6.3** (continued). Verifies the arithmetic producing the next
displayed pair `(7, 13)` in the notes. -/
theorem chain_pair_1_11_S : 2 * 3 + 1 = 7 ∧ 2 * 1 + 11 = 13 := by omega

/-- **Example 6.3** (continued). Verifies explicit supporting factorizations
for the pair `(7, 13)` at `30`. -/
theorem chain_pair_7_13_H :
    3 * 10 = 30 ∧ (10 : ℕ) - 3 = 7 ∧ 2 * 15 = 30 ∧ (15 : ℕ) - 2 = 13 := by omega

/-- **Example 6.3** (continued). Verifies the arithmetic producing the next
displayed pair `(13, 17)`. -/
theorem chain_pair_7_13_S : 2 * 3 + 7 = 13 ∧ 2 * 2 + 13 = 17 := by omega

/-- **Example 6.3** (continued). Verifies explicit supporting factorizations
for the pair `(13, 17)` at `168`. -/
theorem chain_pair_13_17_H :
    8 * 21 = 168 ∧ (21 : ℕ) - 8 = 13 ∧ 7 * 24 = 168 ∧ (24 : ℕ) - 7 = 17 := by omega

/-- **Example 6.3** (continued). Verifies the cumulative sums appearing in the
displayed chain for `{1, 11}`. -/
theorem chain_pair_1_11_sigma :
    12 + 30 = 42 ∧ 12 + 30 + 168 = 210 := by omega

/-- **Example 6.4** (erdos885_notes.tex, §6.2, "the triple {6,54,111}").
Verifies the explicit supporting factorizations for `(6, 54, 111)` at `112`. -/
theorem chain_triple_6_54_111_H :
    8 * 14 = 112 ∧ (14 : ℕ) - 8 = 6 ∧
    2 * 56 = 112 ∧ (56 : ℕ) - 2 = 54 ∧
    1 * 112 = 112 ∧ (112 : ℕ) - 1 = 111 := by omega

/-- **Example 6.4** (continued). Verifies the cumulative sums appearing in the
displayed chain for `(6, 54, 111)`. -/
theorem chain_triple_sigma :
    112 + 840 = 952 ∧ 112 + 840 + 2288 = 3240 := by omega

/-- **Example 6.5** (erdos885_notes.tex, §6.2, "the triple {2,37,58}").
Verifies the explicit supporting factorizations for `(2, 37, 58)` at `120`. -/
theorem chain_triple_2_37_58_H :
    10 * 12 = 120 ∧ (12 : ℕ) - 10 = 2 ∧
    3 * 40 = 120 ∧ (40 : ℕ) - 3 = 37 ∧
    2 * 60 = 120 ∧ (60 : ℕ) - 2 = 58 := by omega

/-- **Example 6.5** (continued). Verifies the cumulative sums appearing in the
displayed chain for `(2, 37, 58)`. -/
theorem chain_triple_2_37_58_sigma :
    120 + 408 = 528 ∧ 120 + 408 + 3960 = 4488 := by omega

/-- **Example 6.6** (erdos885_notes.tex, §6.2, "the four-difference packet").
Verifies the displayed square-difference equalities for the first row of the
four-difference packet. -/
theorem chain_quad_H :
    (234 : ℕ) ^ 2 = 18 ^ 2 + 4 * 13608 ∧
    (366 : ℕ) ^ 2 = 282 ^ 2 + 4 * 13608 ∧
    (531 : ℕ) ^ 2 = 477 ^ 2 + 4 * 13608 ∧
    (1146 : ℕ) ^ 2 = 1122 ^ 2 + 4 * 13608 := by
  constructor <;> [norm_num; constructor <;> [norm_num; constructor <;> norm_num]]

/-- **Example 6.6** (continued). Verifies the cumulative sums appearing in the
displayed packet chain. -/
theorem chain_quad_sigma :
    13608 + 16240 = 29848 ∧ 13608 + 16240 + 36120 = 65968 := by omega

/-! ## Theorem 6.8: Row-complex theorem (key identity) -/

/-- Algebraic identity appearing inside the row-complex theorem:
if `rⱼ² - dⱼ² = 4N` for two columns, then the corresponding row differences
preserve `d₂² - d₁²`. -/
theorem row_complex_identity {d₁ d₂ r₁ r₂ N : ℤ}
    (h1 : r₁ ^ 2 - d₁ ^ 2 = 4 * N)
    (h2 : r₂ ^ 2 - d₂ ^ 2 = 4 * N) :
    r₂ ^ 2 - r₁ ^ 2 = d₂ ^ 2 - d₁ ^ 2 := by
  linarith

/-! ## Proposition 6.9: Stitched factor-pair description -/

/-- **Proposition 6.9** (erdos885_notes.tex, §6.3, "stitched factor-pair description
of a row"). For adjacent columns, `gᵢ * hᵢ = Δᵢ` where `gᵢ = rᵢ₊₁ - rᵢ` and
`hᵢ = rᵢ₊₁ + rᵢ`. This is the identity `(a + b)(a - b) = a² - b²`. -/
theorem stitched_factor_pair {r_i r_next : ℤ} :
    (r_next - r_i) * (r_next + r_i) = r_next ^ 2 - r_i ^ 2 := by ring

/-! ## Theorem 6.10: Terminal stitch criterion -/

/-- Algebraic identity used in the terminal stitch criterion:
if `u * v = Λ` and `v - u = s`, then `s² + 4Λ = (u + v)²`. -/
theorem terminal_stitch_identity {u v s Λ : ℤ}
    (huv : u * v = Λ) (hdiff : v - u = s) :
    s ^ 2 + 4 * Λ = (u + v) ^ 2 := by
  subst hdiff; nlinarith [sq_nonneg (v - u), sq_nonneg (v + u)]

/-! ## Proposition 6.7: Pair-gap contraction -/

/-- Basic identity used in the pair-gap discussion: if `d = H / u - u` and
`m = H / u + u`, then `m = d + 2u`. -/
theorem pair_gap_identity {H u : ℤ} :
    H / u + u = (H / u - u) + 2 * u := by ring
