import Mathlib

/-!
# Divisor-Template Identities

This file collects the addendum algebraic identities around divisor templates
and the projective-rank-2 obstruction that were not already present in the
existing `E885` findings.
-/

namespace Erdos885

/--
If `a = r(r + n)`, `b = s(s + n)`, `c = t(t + n)`, and `M = 2s + n`, then the
adjacent row gaps factor exactly through `M`, and `M² - 4b = n²`.
-/
theorem factor_pair_encoding_identity (r s t n : ℤ) :
    let a := r * (r + n)
    let b := s * (s + n)
    let c := t * (t + n)
    let x := s - r
    let y := t - s
    let M := 2 * s + n
    b - a = x * (M - x) ∧
    c - b = y * (M + y) ∧
    M ^ 2 - 4 * b = n ^ 2 := by
  constructor
  · ring
  constructor
  · ring
  · ring

/--
Writing `y² = b + u²`, the addendum divisor-template equalities are the exact
rewrites `y² - (b - a) = a + u²` and `y² + (c - b) = c + u²`.
-/
theorem divisor_template_identity (u a b c : ℤ) :
    let A := b - a
    let B := c - b
    let y_sq := b + u ^ 2
    y_sq - A = a + u ^ 2 ∧
    y_sq + B = c + u ^ 2 := by
  constructor <;> ring

/--
Diagonal projective-rank-2 obstruction: the functional identity coming from
`ψ(z) = λ z` forces the two `κ` parameters to agree.
-/
theorem mobius_obstruction_diagonal (kappa kappa' lambda : ℤ)
    (hlam : lambda ≠ 0)
    (h : ∀ z : ℤ, z ≠ 0 →
      kappa * z - lambda ^ 2 * z ^ 3 = kappa' * lambda * z - lambda * z ^ 3) :
    kappa = kappa' := by
  by_contra hneq
  have hlambda_sq : lambda ^ 2 = lambda := by
    cases lt_or_gt_of_ne hneq <;> nlinarith [h 1 one_ne_zero, h 2 two_ne_zero]
  simp_all +decide [sq]

/--
Antidiagonal projective-rank-2 obstruction: the corresponding identity coming
from `ψ(z) = λ / z` again forces the two `κ` parameters to agree.
-/
theorem mobius_obstruction_antidiagonal (kappa kappa' lambda : ℤ)
    (hlam : lambda ≠ 0)
    (h : ∀ z : ℤ, z ≠ 0 →
      kappa * z ^ 2 - lambda ^ 2 = kappa' * lambda - z ^ 2 * lambda) :
    kappa = kappa' := by
  cases lt_or_gt_of_ne hlam <;> nlinarith [h 1 one_ne_zero, h 2 two_ne_zero]

end Erdos885
