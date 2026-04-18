import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Square-Discriminant Reformulation

This file formalizes Proposition 1.2 of `erdos885_notes.tex`:
the square-discriminant characterization of membership in the factor-difference set.
-/

set_option maxHeartbeats 800000

/-
**Proposition 1.2** (erdos885_notes.tex, §1, "square-discriminant reformulation").
For positive integers `d` and `n`, `d ∈ D(n)` if and only if there exists a
positive integer `m` such that `m² - d² = 4n`. Equivalently, `d² + 4n` is a
perfect square.
-/
theorem square_discriminant_iff {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    d ∈ factorDiffSet n ↔ ∃ m : ℕ, d < m ∧ m * m = d * d + 4 * n := by
  constructor;
  · rintro ⟨ a, b, ha, hb, hab, h | h ⟩ <;> refine' ⟨ _, _, _ ⟩;
    exacts [ 2 * a + d, by omega, by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : b - a ≠ 0 ) ) ), h, hab ], 2 * b + d, by omega, by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : a - b ≠ 0 ) ) ), h, hab ] ];
  · rintro ⟨ m, hm₁, hm₂ ⟩;
    -- From the equation $m^2 = d^2 + 4n$, we can derive that $n = \frac{m^2 - d^2}{4}$.
    obtain ⟨a, ha⟩ : ∃ a : ℕ, n = a * (a + d) := by
      exact ⟨ ( m - d ) / 2, by nlinarith only [ Nat.div_mul_cancel ( show 2 ∣ m - d from even_iff_two_dvd.mp ( by rw [ Nat.even_sub hm₁.le ] ; replace hm₂ := congr_arg Even hm₂ ; simp_all +decide [ parity_simps ] ) ), hm₂, Nat.sub_add_cancel hm₁.le ] ⟩;
    exact ⟨ a, a + d, Nat.pos_of_ne_zero ( by aesop_cat ), Nat.pos_of_ne_zero ( by aesop_cat ), by linarith, by omega ⟩

/-
Forward direction of Proposition 1.2: if `n = a * (a + d)` for some `a > 0`,
then `(2a+d)² - d² = 4n`.
-/
theorem factorDiff_implies_square {d n a : ℕ} (ha : 0 < a)
    (heq : a * (a + d) = n) :
    (2 * a + d) * (2 * a + d) = d * d + 4 * n := by
  linarith

/-
Backward direction of Proposition 1.2: if `m² - d² = 4n` with `m > d` and
same parity, then `n = a * (a + d)` where `a = (m - d) / 2`.
-/
theorem square_implies_factorDiff {d n m : ℕ} (hmd : d < m)
    (hsq : m * m = d * d + 4 * n) :
    ∃ a : ℕ, 0 < a ∧ a * (a + d) = n := by
  have h_even : Even (m - d) := by
    apply_fun Even at hsq; simp_all +decide [ hmd.le, parity_simps ] ;
  exact ⟨ ( m - d ) / 2, Nat.div_pos ( Nat.le_of_dvd ( Nat.sub_pos_of_lt hmd ) ( even_iff_two_dvd.mp h_even ) ) two_pos, by nlinarith only [ Nat.div_mul_cancel ( even_iff_two_dvd.mp h_even ), Nat.sub_add_cancel hmd.le, hsq ] ⟩