import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.SquareDiscriminant

/-!
# Pair-Fiber Parametrization

This file adds the exact square-discriminant parametrization and a simple
uniform bound for pair-fibers. These are stronger than the existing finiteness
results in `PairFiber.lean` and do not duplicate the weaker finiteness
statements already recorded there.
-/

namespace Erdos885

/--
If `d < e` are both factor differences of `n`, then the square-discriminant
witnesses for `d` and `e` satisfy the exact factorization
`(y - x) * (y + x) = e² - d²`.
-/
theorem pairFiber_parametrization {d e n : ℕ} (hd : 0 < d) (hde : d < e)
    (hdn : d ∈ factorDiffSet n) (hen : e ∈ factorDiffSet n) :
    ∃ x y : ℕ,
      x * x = d * d + 4 * n ∧
      y * y = e * e + 4 * n ∧
      d < x ∧
      e < y ∧
      (y - x) * (y + x) = e ^ 2 - d ^ 2 := by
  have he : 0 < e := lt_trans hd hde
  have hn : 0 < n := by
    rcases hdn with ⟨a, b, ha, hb, hab, _⟩
    simpa [hab] using Nat.mul_pos ha hb
  rcases (square_discriminant_iff hd hn).mp hdn with ⟨x, hdx, hx⟩
  rcases (square_discriminant_iff he hn).mp hen with ⟨y, hey, hy⟩
  have hxy : x < y := by
    nlinarith [hx, hy, hde]
  refine ⟨x, y, hx, hy, hdx, hey, ?_⟩
  have hcast :
      (((y - x) * (y + x) : ℕ) : ℤ) = ((e ^ 2 - d ^ 2 : ℕ) : ℤ) := by
    have hxz : (x : ℤ) * x = d * d + 4 * n := by exact_mod_cast hx
    have hyz : (y : ℤ) * y = e * e + 4 * n := by exact_mod_cast hy
    have hsq : (y : ℤ) * y - x * x = e * e - d * d := by
      nlinarith
    calc
      (((y - x) * (y + x) : ℕ) : ℤ) = ((y : ℤ) - x) * ((y : ℤ) + x) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hxy)]
      _ = (y : ℤ) * y - x * x := by ring
      _ = e * e - d * d := hsq
      _ = ((e ^ 2 - d ^ 2 : ℕ) : ℤ) := by
        rw [Int.ofNat_sub (by nlinarith [hde] : d ^ 2 ≤ e ^ 2)]
        norm_num [pow_two]
  exact Int.ofNat.inj hcast

/--
The exact parametrization gives a crude but uniform upper bound for every
element of the pair-fiber `F({d, e})`.
-/
theorem pairFiber_bounded {d e : ℕ} (hd : 0 < d) (hde : d < e) :
    ∀ n : ℕ, d ∈ factorDiffSet n → e ∈ factorDiffSet n → n ≤ (e ^ 2 - d ^ 2) ^ 2 := by
  intro n hdn hen
  obtain ⟨x, y, hx, _, _, _, hfactor⟩ := pairFiber_parametrization hd hde hdn hen
  have hed_pos : 0 < e ^ 2 - d ^ 2 := by
    apply Nat.sub_pos_of_lt
    nlinarith [hde, hd]
  have hsum_le : y + x ≤ e ^ 2 - d ^ 2 := by
    exact Nat.le_of_dvd hed_pos ⟨y - x, by simpa [Nat.mul_comm] using hfactor.symm⟩
  have hx_le_sum : x ≤ y + x := by
    exact Nat.le_add_left _ _
  have hx_le : x ≤ e ^ 2 - d ^ 2 := hx_le_sum.trans hsum_le
  have hxx_le : x * x ≤ (e ^ 2 - d ^ 2) * (e ^ 2 - d ^ 2) :=
    Nat.mul_le_mul hx_le hx_le
  nlinarith [hx, hxx_le]

end Erdos885
