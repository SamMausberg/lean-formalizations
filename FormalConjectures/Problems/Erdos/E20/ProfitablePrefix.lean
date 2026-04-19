import FormalConjectures.Problems.Erdos.E20.TransversalCounterexample

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Profitable Prefix Obstructions

This file records the exact negative statement behind the parity-slice obstruction:
if the alphabet size is strictly larger than a target base `Λ`, then every positive-length prefix
fiber of the parity slice has probability strictly smaller than `Λ^{-s}`.
-/

/-- In the parity slice, every positive prefix of length `s` has probability strictly smaller than
`Λ^{-s}` whenever `Λ < |G|`.  This is the exact finite form of the user's "no profitable proper
prefix below the alphabet threshold" statement. -/
theorem paritySlice_prefix_probability_lt_inversePow_of_nat_lt_card
    {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]
    {s n Λ : ℕ} (hs : 0 < s) (hΛpos : 0 < Λ) (hΛ : Λ < Fintype.card G) (a : Fin s → G) :
    ((prefixFiber (G := G) s n 0 a).card : ℚ) /
        (paritySlice (G := G) (r := s + (n + 1))).card <
      1 / (Λ : ℚ) ^ s := by
  rw [paritySlice_prefix_uniform]
  have hΛq : (Λ : ℚ) < (Fintype.card G : ℚ) := by
    exact_mod_cast hΛ
  have hΛ_nonneg : 0 ≤ (Λ : ℚ) := by
    positivity
  have hs_ne : s ≠ 0 := Nat.ne_of_gt hs
  have hpow : (Λ : ℚ) ^ s < (Fintype.card G : ℚ) ^ s :=
    pow_lt_pow_left₀ hΛq hΛ_nonneg hs_ne
  have hΛpow_pos : 0 < (Λ : ℚ) ^ s := by
    positivity
  have hqpow_pos : 0 < (Fintype.card G : ℚ) ^ s := by
    positivity
  rw [one_div, one_div]
  exact (inv_lt_inv₀ hqpow_pos hΛpow_pos).2 hpow

/-- Reformulation of the parity-slice obstruction in the "not profitable" direction. -/
theorem paritySlice_prefix_not_profitable_of_nat_lt_card
    {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]
    {s n Λ : ℕ} (hs : 0 < s) (hΛpos : 0 < Λ) (hΛ : Λ < Fintype.card G) (a : Fin s → G) :
    ¬ 1 / (Λ : ℚ) ^ s ≤
        ((prefixFiber (G := G) s n 0 a).card : ℚ) /
          (paritySlice (G := G) (r := s + (n + 1))).card := by
  exact not_le_of_gt <|
    paritySlice_prefix_probability_lt_inversePow_of_nat_lt_card
      (G := G) hs hΛpos hΛ a

end FormalConjectures.Problems.Erdos.E20
