import Mathlib

/-!
# Addendum Computations

This file collects the genuinely new explicit packets and counterexamples from
the Aristotle batch. It intentionally omits computations already formalized in
the existing `Computations`, `GuidepostRigidity`, `RowComplex`, and `Spectrum`
files.
-/

set_option linter.style.nativeDecide false

namespace Erdos885

/--
An explicit `3`-row / `5`-column packet from the addendum, giving a counterexample
to the universal `|Y(a, b, c)| ≤ 4` claim.
-/
theorem new_3row_5col_packet :
    330 ^ 2 + 756000 = 930 ^ 2 ∧
    330 ^ 2 + 15971200 = 4010 ^ 2 ∧
    330 ^ 2 + 45130176 = 6726 ^ 2 ∧
    870 ^ 2 + 756000 = 1230 ^ 2 ∧
    870 ^ 2 + 15971200 = 4090 ^ 2 ∧
    870 ^ 2 + 45130176 = 6774 ^ 2 ∧
    2445 ^ 2 + 756000 = 2595 ^ 2 ∧
    2445 ^ 2 + 15971200 = 4685 ^ 2 ∧
    2445 ^ 2 + 45130176 = 7149 ^ 2 ∧
    4155 ^ 2 + 756000 = 4245 ^ 2 ∧
    4155 ^ 2 + 15971200 = 5765 ^ 2 ∧
    4155 ^ 2 + 45130176 = 7899 ^ 2 ∧
    10482 ^ 2 + 756000 = 10518 ^ 2 ∧
    10482 ^ 2 + 15971200 = 11218 ^ 2 ∧
    10482 ^ 2 + 45130176 = 12450 ^ 2 := by
  native_decide

/--
The addendum also exhibits a two-shift counterexample with six solutions.
-/
theorem two_shift_cap_false :
    150 ^ 2 - 22176 = 18 ^ 2 ∧ 150 ^ 2 + 78624 = 318 ^ 2 ∧
    174 ^ 2 - 22176 = 90 ^ 2 ∧ 174 ^ 2 + 78624 = 330 ^ 2 ∧
    201 ^ 2 - 22176 = 135 ^ 2 ∧ 201 ^ 2 + 78624 = 345 ^ 2 ∧
    326 ^ 2 - 22176 = 290 ^ 2 ∧ 326 ^ 2 + 78624 = 430 ^ 2 ∧
    701 ^ 2 - 22176 = 685 ^ 2 ∧ 701 ^ 2 + 78624 = 755 ^ 2 ∧
    1390 ^ 2 - 22176 = 1382 ^ 2 ∧ 1390 ^ 2 + 78624 = 1418 ^ 2 := by
  native_decide

/--
The `3`-point obstruction route is false: the set `{18, 66, 186}` has at least
four positive shifts.
-/
theorem three_point_obstruction_false :
    18 ^ 2 + 1885 = 47 ^ 2 ∧ 66 ^ 2 + 1885 = 79 ^ 2 ∧ 186 ^ 2 + 1885 = 191 ^ 2 ∧
    18 ^ 2 + 3040 = 58 ^ 2 ∧ 66 ^ 2 + 3040 = 86 ^ 2 ∧ 186 ^ 2 + 3040 = 194 ^ 2 ∧
    18 ^ 2 + 25920 = 162 ^ 2 ∧ 66 ^ 2 + 25920 = 174 ^ 2 ∧ 186 ^ 2 + 25920 = 246 ^ 2 ∧
    18 ^ 2 + 110565 = 333 ^ 2 ∧ 66 ^ 2 + 110565 = 339 ^ 2 ∧
    186 ^ 2 + 110565 = 381 ^ 2 := by
  native_decide

/--
First primitive maximal `4`-secant triple from the addendum.
-/
theorem primitive_4secant_triple_1 :
    16 ^ 2 + 4 * 46592 = 432 ^ 2 ∧
    16 ^ 2 + 4 * 363545 = 1206 ^ 2 ∧
    16 ^ 2 + 4 * 1498112 = 2448 ^ 2 ∧
    344 ^ 2 + 4 * 46592 = 552 ^ 2 ∧
    344 ^ 2 + 4 * 363545 = 1254 ^ 2 ∧
    344 ^ 2 + 4 * 1498112 = 2472 ^ 2 ∧
    776 ^ 2 + 4 * 46592 = 888 ^ 2 ∧
    776 ^ 2 + 4 * 363545 = 1434 ^ 2 ∧
    776 ^ 2 + 4 * 1498112 = 2568 ^ 2 ∧
    1424 ^ 2 + 4 * 46592 = 1488 ^ 2 ∧
    1424 ^ 2 + 4 * 363545 = 1866 ^ 2 ∧
    1424 ^ 2 + 4 * 1498112 = 2832 ^ 2 := by
  native_decide

/--
Second primitive maximal `4`-secant triple from the addendum.
-/
theorem primitive_4secant_triple_2 :
    108 ^ 2 + 4 * 24640 = 332 ^ 2 ∧
    108 ^ 2 + 4 * 405405 = 1278 ^ 2 ∧
    108 ^ 2 + 4 * 1723680 = 2628 ^ 2 ∧
    516 ^ 2 + 4 * 24640 = 604 ^ 2 ∧
    516 ^ 2 + 4 * 405405 = 1374 ^ 2 ∧
    516 ^ 2 + 4 * 1723680 = 2676 ^ 2 ∧
    1212 ^ 2 + 4 * 24640 = 1252 ^ 2 ∧
    1212 ^ 2 + 4 * 405405 = 1758 ^ 2 ∧
    1212 ^ 2 + 4 * 1723680 = 2892 ^ 2 ∧
    1524 ^ 2 + 4 * 24640 = 1556 ^ 2 ∧
    1524 ^ 2 + 4 * 405405 = 1986 ^ 2 ∧
    1524 ^ 2 + 4 * 1723680 = 3036 ^ 2 := by
  native_decide

end Erdos885
