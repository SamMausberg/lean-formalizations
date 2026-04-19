import Mathlib

/-!
# Shift Transpose

This file records the non-duplicate transpose formalization from the addendum:
the passage from a `5`-point / `3`-shift witness to a `4`-point / `4`-shift
configuration.
-/

namespace Erdos885

/--
For a finite set `Y`, `shiftSet Y` is the set of positive shifts turning every
`y² + a` into a square.
-/
def shiftSet (Y : Finset ℕ) : Set ℕ :=
  {a : ℕ | 0 < a ∧ ∀ y ∈ Y, ∃ z : ℕ, z ^ 2 = y ^ 2 + a}

/--
Core algebraic identity behind the transpose from a `5`-point / `3`-shift
configuration to a `4`-point / `4`-shift configuration.
-/
theorem transpose_identity (y0 y a x0 z : ℤ)
    (hx0 : x0 ^ 2 = y0 ^ 2 + a)
    (hz : z ^ 2 = y ^ 2 + a) :
    x0 ^ 2 + (y ^ 2 - y0 ^ 2) = z ^ 2 := by
  linarith

/--
The transpose identity immediately yields a square witness for the translated
shift.
-/
theorem transpose_forward (y0 yi a x0 zi : ℤ)
    (hx0 : x0 ^ 2 = y0 ^ 2 + a)
    (hzi : zi ^ 2 = yi ^ 2 + a) :
    ∃ w : ℤ, w ^ 2 = x0 ^ 2 + (yi ^ 2 - y0 ^ 2) := by
  exact ⟨zi, by linarith⟩

end Erdos885
