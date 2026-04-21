import Mathlib

open scoped BigOperators
open Finset

set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-!
# Uniform Solved-Class Capture and Pressure Bounds

This file isolates the part of the user's proposed pressure argument that is already
formally sound at the current level of abstraction.

The key input is a **uniform solved-class capture hypothesis**:
every probability measure on a finite trace set `T` gives at least `δ` mass to some
subfamily belonging to the chosen solved class.

From that hypothesis one gets the desired dual/packing bound immediately:
every feasible packing has total mass at most `δ⁻¹`.

What this file deliberately does **not** attempt to formalize is the local mechanism
that would produce the capture hypothesis from residual continuation-cone data.
That part depends on additional semantics that are not yet present in the current
`E20` library.
-/

variable {α : Type*} [DecidableEq α]

/-- A finitely supported probability distribution on the trace set `T`. -/
def IsProbabilityOn (T : Finset α) (μ : α → ℝ) : Prop :=
  (∀ a ∈ T, 0 ≤ μ a) ∧ Finset.sum T μ = 1

/-- Feasible dual packing for a solved-class LP on `T`: nonnegative weights on `T`
whose total weight on every solved subtrace is at most `1`. -/
def FeasibleSolvedPacking (T : Finset α) (Solved : Finset α → Prop) (x : α → ℝ) : Prop :=
  (∀ a ∈ T, 0 ≤ x a) ∧
    ∀ U, U ⊆ T → Solved U → Finset.sum U x ≤ 1

/-- Uniform solved-class capture: every probability measure on `T` gives at least `δ`
mass to some solved subtrace. -/
def UniformSolvedCapture (T : Finset α) (Solved : Finset α → Prop) (δ : ℝ) : Prop :=
  ∀ μ, IsProbabilityOn T μ →
    ∃ U, U ⊆ T ∧ Solved U ∧ δ ≤ Finset.sum U μ

/-- "Solved-trace pressure at most `M`" stated directly as a bound on every feasible packing. -/
def HasSolvedTracePressureBound
    (T : Finset α) (Solved : Finset α → Prop) (M : ℝ) : Prop :=
  ∀ x, FeasibleSolvedPacking T Solved x → Finset.sum T x ≤ M

/-- The dual argument from the user's note:
uniform solved-class capture with parameter `δ > 0` forces every feasible packing to have
total mass at most `δ⁻¹`. -/
theorem uniformSolvedCapture_gives_pressureBound
    {T : Finset α} {Solved : Finset α → Prop} {δ : ℝ}
    (hδ : 0 < δ)
    (hCapture : UniformSolvedCapture T Solved δ) :
    HasSolvedTracePressureBound T Solved (1 / δ) := by
  intro x hx
  let m : ℝ := Finset.sum T x
  have hm_nonneg : 0 ≤ m := by
    exact Finset.sum_nonneg fun a ha => hx.1 a ha
  by_cases hm : m = 0
  · rw [show Finset.sum T x = m by rfl, hm]
    positivity
  · have hm_ne : m ≠ 0 := hm
    have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hm_ne)
    let μ : α → ℝ := fun a => x a / m
    have hμ : IsProbabilityOn T μ := by
      constructor
      · intro a ha
        exact div_nonneg (hx.1 a ha) hm_nonneg
      · have hsum :
          Finset.sum T μ = (Finset.sum T x) / m := by
            simp [μ, Finset.sum_div]
        calc
          Finset.sum T μ = m / m := by simpa [m] using hsum
          _ = 1 := by field_simp [hm]
    obtain ⟨U, hUT, hSolved, hUcapt⟩ := hCapture μ hμ
    have hUle : Finset.sum U x ≤ 1 := hx.2 U hUT hSolved
    have hscale :
        Finset.sum U x = m * Finset.sum U μ := by
      calc
        Finset.sum U x = Finset.sum U (fun a => m * μ a) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          dsimp [μ]
          field_simp [hm_ne]
        _ = m * Finset.sum U μ := by
          symm
          simpa using (Finset.mul_sum U μ m)
    have hmdelta : m * δ ≤ 1 := by
      have hmul : m * δ ≤ m * Finset.sum U μ :=
        mul_le_mul_of_nonneg_left hUcapt hm_nonneg
      calc
        m * δ ≤ m * Finset.sum U μ := hmul
        _ = Finset.sum U x := by symm; exact hscale
        _ ≤ 1 := hUle
    have hm_bound : m ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]
      simpa [mul_comm] using hmdelta
    simpa [m] using hm_bound

end FormalConjectures.Problems.Erdos.E20.Compendium
