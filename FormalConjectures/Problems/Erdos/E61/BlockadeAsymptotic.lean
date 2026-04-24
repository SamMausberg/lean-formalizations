import FormalConjectures.Problems.Erdos.E61.Blockade

/-!
# Power-threshold blockade wrappers

The paper states `lem:failed-coordinate` and `prop:coordinate-synchronizes` in
asymptotic exponent language.  `Blockade.lean` contains the finite counting
cores.  This file packages those cores in the natural power-threshold form used
by the proofs.
-/

namespace Erdos61

open Finset

variable {α β ι : Type*}

/--
If `θ + λ < β`, then the room inequality used by the failed-coordinate cleaning
lemma follows from the explicit large-width condition
`2 ≤ m^(β-(θ+λ))`.
-/
theorem power_room_of_exponent_gap {m β θ lam : ℕ}
    (hgap : θ + lam < β) (hlarge : 2 ≤ m ^ (β - (θ + lam))) :
    m ^ θ * m ^ lam + m ^ θ ≤ m ^ β := by
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hdiff : 0 < β - (θ + lam) := Nat.sub_pos_of_lt hgap
    simp [hm0, hdiff] at hlarge
  have hθ_le : m ^ θ ≤ m ^ (θ + lam) := by
    exact Nat.pow_le_pow_right hmpos (Nat.le_add_right θ lam)
  have hpowθlam : m ^ θ * m ^ lam = m ^ (θ + lam) := by
    rw [Nat.pow_add]
  have hmain :
      m ^ θ * m ^ lam + m ^ θ ≤ 2 * m ^ (θ + lam) := by
    calc
      m ^ θ * m ^ lam + m ^ θ = m ^ (θ + lam) + m ^ θ := by rw [hpowθlam]
      _ ≤ m ^ (θ + lam) + m ^ (θ + lam) :=
        Nat.add_le_add_left hθ_le _
      _ = 2 * m ^ (θ + lam) := by omega
  have hsplit : β = θ + lam + (β - (θ + lam)) := by omega
  have hpowβ : m ^ β = m ^ (θ + lam) * m ^ (β - (θ + lam)) := by
    calc
      m ^ β = m ^ (θ + lam + (β - (θ + lam))) :=
        congrArg (fun n => m ^ n) hsplit
      _ = m ^ (θ + lam) * m ^ (β - (θ + lam)) := by rw [Nat.pow_add]
  have hlarge_mul : 2 * m ^ (θ + lam) ≤ m ^ β := by
    calc
      2 * m ^ (θ + lam) = m ^ (θ + lam) * 2 := by rw [Nat.mul_comm]
      _ ≤ m ^ (θ + lam) * m ^ (β - (θ + lam)) :=
        Nat.mul_le_mul_left _ hlarge
      _ = m ^ β := hpowβ.symm
  exact le_trans hmain hlarge_mul

/--
Power-threshold form of `lem:failed-coordinate`.

Here `R` is the correct-coordinate relation.  If every `x ∈ X` has fewer than
`m^λ` correct neighbors in `Y`, and both sides have enough room at exponent
`β`, then there are `m^θ` vertices on each side with no correct relation.
-/
theorem failed_coordinate_cleans_power
    (R : α → β → Prop) [DecidableRel R]
    (X : Finset α) (Y : Finset β) {m βexp θ lam : ℕ}
    (hgap : θ + lam < βexp)
    (hlarge : 2 ≤ m ^ (βexp - (θ + lam)))
    (hX : m ^ θ ≤ X.card)
    (hY : m ^ βexp ≤ Y.card)
    (hsmall : ∀ x ∈ X, (Y.filter fun y => R x y).card < m ^ lam) :
    ∃ X' : Finset α, X' ⊆ X ∧ X'.card = m ^ θ ∧
      ∃ Y' : Finset β, Y' ⊆ Y ∧ Y'.card = m ^ θ ∧ Anticomplete R X' Y' := by
  exact failed_coordinate_cleans_finite R X Y hX hsmall
    (le_trans (power_room_of_exponent_gap hgap hlarge) hY)

/--
Power-threshold form of the finite synchronization lemma used in
`prop:coordinate-synchronizes`.
-/
theorem coordinatewise_synchronizes_power
    (J : Finset ι) (X : Finset α) (Good : ι → α → Prop)
    [∀ j, DecidablePred (Good j)] {m γ : ℕ}
    (hbad : ∀ j ∈ J, (X.filter fun x => ¬ Good j x).card < m ^ γ)
    (hroom : J.card * m ^ γ < X.card) :
    ∃ x ∈ X, ∀ j ∈ J, Good j x :=
  coordinatewise_synchronizes_finite J X Good hbad hroom

end Erdos61
