import Mathlib

/-!
# Four-Row Transfer Laws

The existing `ColumnLaw.lean` file already records the exact `3`-row transfer
law. This file adds the genuinely new `4`-row transfer identities and the
quartic discriminant formulas from the addendum batch.
-/

namespace Erdos885

/--
For a `4`-row anchored packet, the adjacent cubic transfer law holds on both
consecutive triples of rows.
-/
theorem four_row_transfer_law
    (x r2 r3 r4 r5 c2 c3 c4 c5 : ℤ)
    (h2 : c2 = r2 * (2 * x + r2))
    (h3 : c3 = r3 * (2 * x + r3))
    (h4 : c4 = r4 * (2 * x + r4))
    (h5 : c5 = r5 * (2 * x + r5)) :
    (c4 - c3) * (r3 - r2) - (c3 - c2) * (r4 - r3) =
      (r3 - r2) * (r4 - r3) * ((r3 - r2) + (r4 - r3)) ∧
    (c5 - c4) * (r4 - r3) - (c4 - c3) * (r5 - r4) =
      (r4 - r3) * (r5 - r4) * ((r4 - r3) + (r5 - r4)) := by
  subst h2
  subst h3
  subst h4
  subst h5
  constructor <;> ring

/--
Solving the `4`-row transfer system for the outer step sizes yields the two
quartic discriminant identities from the addendum.
-/
theorem four_row_discriminant_formulas
    (u v w A B C : ℤ)
    (h1 : A * u - B * v = u * v * (u + v))
    (h2 : C * v - A * w = v * w * (v + w)) :
    (2 * u * v + v ^ 2 - A) ^ 2 = v ^ 4 - 2 * (A + 2 * B) * v ^ 2 + A ^ 2 ∧
    (2 * w * v + v ^ 2 + A) ^ 2 = v ^ 4 + 2 * (A + 2 * C) * v ^ 2 + A ^ 2 := by
  constructor <;> cases le_or_gt 0 v <;> nlinarith

/--
The Riemann-Hurwitz arithmetic in the addendum genus computation.
-/
theorem genus_5_arithmetic : 2 * 5 - 2 = 4 * (-2 : ℤ) + 16 := by
  norm_num

end Erdos885
