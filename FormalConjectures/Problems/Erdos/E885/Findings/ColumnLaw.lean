import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Anchored Packets, Divisor Grids, and Column Laws

This file captures selected exact algebraic identities and packet checks from
Section 4 of `erdos885_notes.tex`, especially the anchored-packet identity,
column law, cocycle law, cross-ratio numerics for the displayed packet, the
3-row transfer identity, and explicit width-4 packet verifications.
-/

set_option maxHeartbeats 800000

/-! ## Proposition 4.1: Anchored packet formulation -/

/-
**Proposition 4.1** (erdos885_notes.tex, §4.1, "anchored packet formulation").
A finite set `T = {d₁, …, dᵣ}` has `m` positive common supports `N₁, …, Nₘ`
iff there exist positive integers `x₁, …, xₘ` such that for every `i = 2, …, r`
and every `t = 1, …, m`, `xₜ² + cᵢ` is a square, where `cᵢ = dᵢ² - d₁²`.

We formalize the key algebraic identity: `c = r * (2 * x + r)` iff
`(x + r)² = x² + c`.
-/
theorem anchored_packet_identity (x r c : ℕ) :
    c = r * (2 * x + r) ↔ (x + r) * (x + r) = x * x + c := by
  grind

/-! ## Theorem 4.2: Column law -/

/-
**Theorem 4.2** (erdos885_notes.tex, §4.2, "column law").
For a fixed column `t`, if `cᵢ = rᵢ(2x + rᵢ)` and `cⱼ = rⱼ(2x + rⱼ)`,
then `cⱼ * rᵢ - cᵢ * rⱼ = rᵢ * rⱼ * (rⱼ - rᵢ)`.

This is the exact cubic column law.
-/
theorem column_law {x : ℤ} {ri rj ci cj : ℤ}
    (hi : ci = ri * (2 * x + ri))
    (hj : cj = rj * (2 * x + rj)) :
    cj * ri - ci * rj = ri * rj * (rj - ri) := by
  grind

/-
**Theorem 4.2** (continued, "cocycle form").
For three rows `i < j < k` with `δᵢⱼ = yⱼ - yᵢ`, `Δᵢⱼ = cⱼ - cᵢ`,
the exact cocycle law is `Δⱼₖ * δᵢⱼ - Δᵢⱼ * δⱼₖ = δᵢⱼ * δⱼₖ * δᵢₖ`.
-/
theorem cocycle_law {x : ℤ} {ri rj rk ci cj ck : ℤ}
    (hi : ci = ri * (2 * x + ri))
    (hj : cj = rj * (2 * x + rj))
    (hk : ck = rk * (2 * x + rk))
    (hrij : ri < rj) (hrjk : rj < rk) :
    let δij := rj - ri
    let δjk := rk - rj
    let δik := rk - ri
    let Δij := cj - ci
    let Δjk := ck - cj
    Δjk * δij - Δij * δjk = δij * δjk * δik := by
  grind

/-! ## Theorem 4.5: Cross-ratio test -/

/-- **Theorem 4.5** (erdos885_notes.tex, §4.3, "cross-ratio test on completed packets").
The cross-ratios of the three rows of the 3×4 packet are distinct. This is
verified by direct computation. The cross-ratio `CR(a,b,c,d) = (a-c)(b-d)/((a-d)(b-c))`. -/
theorem crossRatio_row1 :
    (264 - 100) * (132 - 72) = 9840 ∧
    (264 - 72) * (132 - 100) = 6144 := by
  constructor <;> norm_num

theorem crossRatio_row2 :
    (459 - 243) * (297 - 187) = 23760 ∧
    (459 - 187) * (297 - 243) = 14688 := by
  constructor <;> norm_num

theorem crossRatio_row3 :
    (1104 - 828) * (912 - 720) = 52992 ∧
    (1104 - 720) * (912 - 828) = 32256 := by
  constructor <;> norm_num

/-- **Theorem 4.5** (continued). The cross-ratios `9840/6144`, `23760/14688`,
`52992/32256` are pairwise distinct, hence the packet is not of Möbius type. -/
theorem crossRatios_distinct :
    (9840 : ℚ) / 6144 ≠ 23760 / 14688 ∧
    (9840 : ℚ) / 6144 ≠ 52992 / 32256 ∧
    (23760 : ℚ) / 14688 ≠ 52992 / 32256 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-! ## Theorem 4.8: Exact 3-row transfer law (elliptic curve) -/

/-
**Theorem 4.8** (erdos885_notes.tex, §4.4, "exact 3-row transfer law").
The adjacent law `A * u - B * v = u * v * (u + v)` holds for column differences
`u = r₃ - r₂`, `v = r₄ - r₃`, where `B = c₃ - c₂`, `A = c₄ - c₃`.

We verify the algebraic identity underlying the transfer:
if `c₂ = r₂(2x + r₂)`, `c₃ = r₃(2x + r₃)`, `c₄ = r₄(2x + r₄)`,
and `u = r₃ - r₂`, `v = r₄ - r₃`, `B = c₃ - c₂`, `A = c₄ - c₃`,
then `A * u - B * v = u * v * (u + v)`.
-/
theorem three_row_transfer_law {x : ℤ} {r2 r3 r4 c2 c3 c4 : ℤ}
    (h2 : c2 = r2 * (2 * x + r2))
    (h3 : c3 = r3 * (2 * x + r3))
    (h4 : c4 = r4 * (2 * x + r4)) :
    let u := r3 - r2
    let v := r4 - r3
    let B := c3 - c2
    let A := c4 - c3
    A * u - B * v = u * v * (u + v) := by
  grind +revert

/-! ## Verified packet computations -/

/-- **Computation 4.4** (erdos885_notes.tex, §4.3, "completed width-4 packets").
Verification of the 3×4 packet: `c₂ = 79200`, and `r₂,₁ = 264`, `x₁ = 18`.
Check: `79200 = 264 * (2 * 18 + 264) = 264 * 300`. -/
theorem packet_3x4_check_c2_col1 : (79200 : ℤ) = 264 * (2 * 18 + 264) := by norm_num

theorem packet_3x4_check_c2_col2 : (79200 : ℤ) = 132 * (2 * 234 + 132) := by norm_num

theorem packet_3x4_check_c2_col3 : (79200 : ℤ) = 100 * (2 * 346 + 100) := by norm_num

theorem packet_3x4_check_c2_col4 : (79200 : ℤ) = 72 * (2 * 514 + 72) := by norm_num

theorem packet_3x4_check_c3_col1 : (227205 : ℤ) = 459 * (2 * 18 + 459) := by norm_num

theorem packet_3x4_check_c3_col2 : (227205 : ℤ) = 297 * (2 * 234 + 297) := by norm_num

theorem packet_3x4_check_c3_col3 : (227205 : ℤ) = 243 * (2 * 346 + 243) := by norm_num

theorem packet_3x4_check_c3_col4 : (227205 : ℤ) = 187 * (2 * 514 + 187) := by norm_num

theorem packet_3x4_check_c4_col1 : (1258560 : ℤ) = 1104 * (2 * 18 + 1104) := by norm_num

theorem packet_3x4_check_c4_col2 : (1258560 : ℤ) = 912 * (2 * 234 + 912) := by norm_num

theorem packet_3x4_check_c4_col3 : (1258560 : ℤ) = 828 * (2 * 346 + 828) := by norm_num

theorem packet_3x4_check_c4_col4 : (1258560 : ℤ) = 720 * (2 * 514 + 720) := by norm_num
