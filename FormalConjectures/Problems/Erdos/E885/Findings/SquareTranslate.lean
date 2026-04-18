import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Square-Translate Geometry and Genus Computations

This file records selected algebraic maps, genus formulas, and explicit seed
computations from Sections 7 and 8 of `erdos885_notes.tex`. It does not
formalize the full algebraic-geometry statements from those sections.
-/

set_option maxHeartbeats 800000

/-! ## Proposition 7.1: Pairwise factorization formula -/

/-- **Proposition 7.1** (erdos885_notes.tex, §7, "pairwise factorization formula").
For `dⱼ = H/uⱼ - uⱼ`, we have `dᵢ² - dⱼ² = (uⱼ² - uᵢ²)(cᵢⱼ² - 1)`,
where `cᵢⱼ = H / (uᵢ * uⱼ)`.

The basic identity: `(H/u - u)² = H²/u² - 2H + u²`. -/
theorem pairwise_factorization_sq (H u : ℤ) :
    (H / u - u) ^ 2 = (H / u) ^ 2 - 2 * (H / u) * u + u ^ 2 := by ring

/-- **Proposition 7.1** (continued). The difference of squares identity:
`(H/uᵢ - uᵢ)² - (H/uⱼ - uⱼ)² = (H/uᵢ + H/uⱼ)(H/uᵢ - H/uⱼ) - 2H(1/uᵢ - 1/uⱼ) ...`
We verify the factored form over ℚ. -/
theorem pairwise_diff_sq (H ui uj : ℚ) (hui : ui ≠ 0) (huj : uj ≠ 0) :
    (H / ui - ui) ^ 2 - (H / uj - uj) ^ 2 =
    (uj ^ 2 - ui ^ 2) * (H ^ 2 / (ui ^ 2 * uj ^ 2) - 1) := by
  field_simp
  ring

/-! ## Proposition 7.4: Normalized square-translate equivalence -/

/- **Proposition 7.4** (erdos885_notes.tex, §7.1, "normalized square-translate
equivalence"). The original k×k problem is equivalent to finding shifts
`e₁ = 0, e₂, …, eₖ` and squares `u₀², u₁², …, uₖ²` such that every
`uⱼ² + eᵢ` is a square.

We state the key reformulation: `d ∈ D(N)` iff `d² + 4N` is a perfect square,
which means the problem becomes: find `eᵢ` and `uⱼ` such that `uⱼ² + eᵢ` is
a square for all `i, j`. This is already covered by Proposition 1.2.

Here we verify the specific normalizations from Example 7.8. -/

/-- **Example 7.8** (erdos885_notes.tex, §7.3, "normalized seeds").
`(112, 952, 3240)` with `{6, 54, 111}` becomes `e = {0, 2880, 12285}`,
`u = {6, 22, 62, 114}`. Verification: `6² + 0 = 36 = 6²` (trivial),
`6² + 2880 = 2916 = 54²`, `6² + 12285 = 12321 = 111²`. -/
theorem normalized_seed_triple :
    6 ^ 2 + 2880 = 54 ^ 2 ∧
    6 ^ 2 + 12285 = 111 ^ 2 ∧
    22 ^ 2 + 2880 = 58 ^ 2 ∧
    22 ^ 2 + 12285 = 113 ^ 2 ∧
    62 ^ 2 + 2880 = 82 ^ 2 ∧
    62 ^ 2 + 12285 = 127 ^ 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Example 7.8** (continued). `(13608, 29848, 65968)` with `{18, 282, 477, 1122}`
becomes `e = {0, 79200, 227205, 1258560}`, `u = {18, 234, 346, 514}`. -/
theorem normalized_seed_quad_e :
    282 ^ 2 - 18 ^ 2 = 79200 * 1 ∧
    477 ^ 2 - 18 ^ 2 = 227205 * 1 ∧
    1122 ^ 2 - 18 ^ 2 = 1258560 * 1 := by
  constructor <;> [norm_num; constructor <;> norm_num]

/-! ## Theorem 7.5: The 3-shift curve is elliptic -/

/-
**Theorem 7.5** (erdos885_notes.tex, §7.2, "the 3-shift curve is elliptic").
Fix shifts `(0, p, q)`. The common-square curve `u² + p = v²`, `u² + q = w²`
is genus 1. The Weierstrass model is `E_{p,q}: Y² = X(X + 4p)(X + 4q)`.

We verify the birational map: if `X = 4(u+v)(u+w)` and `Y = 8(u+v)(u+w)(v+w)`,
then `Y² = X(X + 4p)(X + 4q)` when `v² = u² + p` and `w² = u² + q`.
-/
theorem three_shift_weierstrass (u v w p q : ℤ)
    (hv : v ^ 2 = u ^ 2 + p) (hw : w ^ 2 = u ^ 2 + q) :
    let X := 4 * (u + v) * (u + w)
    let Y := 8 * (u + v) * (u + w) * (v + w)
    Y ^ 2 = X * (X + 4 * p) * (X + 4 * q) := by
  grind +ring

/-
**Theorem 7.5** (continued). The inverse map:
`u = (16pq - X²) / (4Y)`. We verify that `16pq - X² = -4Y·u` when
`X = 4(u+v)(u+w)` and `Y = 8(u+v)(u+w)(v+w)`.
-/
theorem three_shift_inverse_u (u v w p q : ℤ)
    (hv : v ^ 2 = u ^ 2 + p) (hw : w ^ 2 = u ^ 2 + q)
    (hvw_ne : (u + v) * (u + w) * (v + w) ≠ 0) :
    let X := 4 * (u + v) * (u + w)
    let Y := 8 * (u + v) * (u + w) * (v + w)
    16 * p * q - X ^ 2 = -(4 * Y * u) := by
  grind +ring

/-! ## Proposition 7.6: A moving elliptic family -/

/-- **Proposition 7.6** (erdos885_notes.tex, §7.2, "a moving elliptic family").
At `t = 3`, the specialization `E₃: Y² = X(X + 4900)(X + 100)` has the point
`P₃ = (4900, 490000)`. Verification. -/
theorem moving_family_t3 :
    (490000 : ℤ) ^ 2 = 4900 * (4900 + 4900) * (4900 + 100) := by norm_num

/-! ## Theorem 7.7: The 4-shift curve is genus 5 -/

/-- Numerical genus formula used in the notes for the four-shift curve. -/
theorem genus_four_shift : 1 + (3 - 2) * 2 ^ 2 = (5 : ℤ) := by norm_num

/-- Riemann--Hurwitz arithmetic appearing in the genus-5 discussion. -/
theorem genus_four_shift_RH : 4 * (-2 : ℤ) + 16 = 8 := by norm_num

/-! ## Proposition 7.2: Static support curve genus formula -/

/-- Evaluates the static-support genus formula at `r = 2, 3, 4`. -/
theorem static_support_genus_2 : 1 + 2 ^ (2 - 2) * ((2 : ℤ) - 3) = 0 := by norm_num
theorem static_support_genus_3 : 1 + 2 ^ (3 - 2) * ((3 : ℤ) - 3) = 1 := by norm_num
theorem static_support_genus_4 : 1 + 2 ^ (4 - 2) * ((4 : ℤ) - 3) = 5 := by norm_num

/-! ## Section 8: Non-split seed computations -/

/-- **Proposition 8.1** (erdos885_notes.tex, §8.1, "the non-split seed").
`(r - p)(r - q) = 1179360 × 1031355` for `(p,q,r) = (79200, 227205, 1258560)`. -/
theorem nonsplit_seed_factorization :
    (1258560 - 79200) * (1258560 - 227205) = 1179360 * 1031355 := by norm_num

/-- **Proposition 8.1** (continued). The rational points on the seed curve:
`z = 2 * sqrt(u² + r)` for `u ∈ {18, 234, 346, 514}`. -/
theorem nonsplit_seed_points :
    4 * (18 ^ 2 + 1258560) = 2244 ^ 2 ∧
    4 * (234 ^ 2 + 1258560) = 2292 ^ 2 ∧
    4 * (346 ^ 2 + 1258560) = 2348 ^ 2 ∧
    4 * (514 ^ 2 + 1258560) = 2468 ^ 2 := by
  constructor <;> [norm_num; constructor <;> [norm_num; constructor <;> norm_num]]

/-- **Proposition 8.2** (erdos885_notes.tex, §8.1, "the quotient elliptic curve").
The three points `P₁₈, P₂₃₄, P₅₁₄` are collinear on `Y = 1582X + 17319744`.
Verification: each point satisfies the line equation. -/
theorem collinear_points :
    1582 * 1296 + 17319744 = (19370016 : ℤ) ∧
    1582 * 219024 + 17319744 = (363815712 : ℤ) ∧
    1582 * 1056784 + 17319744 = (1689152032 : ℤ) := by
  constructor <;> [norm_num; constructor <;> norm_num]

/-
**Proposition 8.2** (continued). The points lie on the elliptic curve
`Y² = X(X + 316800)(X + 908820)`.
-/
theorem points_on_elliptic_curve :
    (19370016 : ℤ) ^ 2 = 1296 * (1296 + 316800) * (1296 + 908820) ∧
    (363815712 : ℤ) ^ 2 = 219024 * (219024 + 316800) * (219024 + 908820) ∧
    (727136992 : ℤ) ^ 2 = 478864 * (478864 + 316800) * (478864 + 908820) ∧
    (1689152032 : ℤ) ^ 2 = 1056784 * (1056784 + 316800) * (1056784 + 908820) := by
  grind

/-- **Proposition 8.3** (erdos885_notes.tex, §8.1, "cross-ratio obstruction").
The normalized cross-ratio `λ = 227205 / 79200 = 459 / 160`. -/
theorem crossRatio_seed : (227205 : ℚ) / 79200 = 459 / 160 := by norm_num

/-
**Proposition 8.3** (continued). `459/160` is not a perfect square in ℚ.
Neither `459` nor `160` is a perfect square in ℤ.
-/
theorem crossRatio_not_square :
    ¬ ∃ (a b : ℤ), 0 < b ∧ (a : ℚ) ^ 2 / (b : ℚ) ^ 2 = 459 / 160 := by
  push_neg;
  intro a b hb;
  -- Suppose for contradiction that $459/160$ is a perfect square.
  by_contra h
  obtain ⟨k, hk⟩ : ∃ k : ℚ, k^2 = 459 / 160 := by
    exact ⟨ a / b, by simpa [ div_pow ] using h ⟩;
  exact absurd hk ( by apply_fun ( fun x => x.num ) at hk; norm_num [ sq, Rat.mul_self_num ] at hk; nlinarith [ show k.num ≤ 21 by nlinarith, show k.num ≥ -21 by nlinarith ] )

/-! ## Proposition 8.4: 3-point deformation base -/

/-- **Proposition 8.4** (erdos885_notes.tex, §8.2, "the 3-point deformation base").
The seed point `(m, Δ) = (1582, 592020)` recovers `(p, q) = (79200, 227205)`.
Verification of the coefficient relations. -/
theorem deformation_base_seed :
    1582 ^ 2 - 1277104 = 4 * (79200 + 227205) ∧
    (233114505984 : ℤ) + 34639488 * 1582 = 16 * 79200 * 227205 := by
  constructor <;> norm_num

/-- **Proposition 8.4** (continued). The base curve factors:
`Δ² = (m - 1532)(m - 524)(m + 596)(m + 1460)` at `m = 1582`. -/
theorem deformation_base_check :
    (1582 - 1532) * (1582 - 524) * (1582 + 596) * (1582 + 1460) =
    (592020 : ℤ) ^ 2 := by norm_num
