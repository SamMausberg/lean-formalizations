import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Anchored Spectra and Spectral-Cap Obstructions

This file records selected identities and explicit calculations from Section 5
of `erdos885_notes.tex`. It does not formalize the full anchored spectrum
theorem, boundary embedding criterion, or spectral-cap obstruction.
-/

set_option maxHeartbeats 800000

/-! ## Theorem 5.5: Column-spectrum theorem (key algebraic identity) -/

/-- Basic factorization identity used in the anchored spectrum discussion:
`r^2 - d^2 = (r - d)(r + d)` and the factor difference is `2d`. -/
theorem column_spectrum_key {r d : ℤ} :
    ∃ (g h_val : ℤ), g * h_val = r ^ 2 - d ^ 2 ∧ h_val - g = 2 * d := by
  exact ⟨r - d, r + d, by ring, by ring⟩

/-! ## Computation 5.9: Spectral cap verification -/

/-- Computes the three `δ_t` values used in the spectral-cap example from the
notes. -/
theorem spectral_cap_deltas :
    (468 ^ 2 - 36 ^ 2 : ℤ) / 4 = 54432 ∧
    (692 ^ 2 - 36 ^ 2 : ℤ) / 4 = 119392 ∧
    (1028 ^ 2 - 36 ^ 2 : ℤ) / 4 = 263872 := by
  constructor <;> [norm_num; constructor <;> norm_num]

/-- Verifies the first displayed element of the sample `B(54432)` spectrum. -/
theorem spectral_cap_element_1 : 18 ^ 2 + 54432 = (234 : ℤ) ^ 2 := by norm_num

/-- Verifies the second displayed element of the sample `B(54432)` spectrum. -/
theorem spectral_cap_element_2 : 282 ^ 2 + 54432 = (366 : ℤ) ^ 2 := by norm_num

/-- Verifies the third displayed element of the sample `B(54432)` spectrum. -/
theorem spectral_cap_element_3 : 477 ^ 2 + 54432 = (531 : ℤ) ^ 2 := by norm_num

/-- Verifies the fourth displayed element of the sample `B(54432)` spectrum. -/
theorem spectral_cap_element_4 : 1122 ^ 2 + 54432 = (1146 : ℤ) ^ 2 := by norm_num

/-! ## Computation 5.10: 7-interface near-miss -/

/-- **Computation 5.10** (erdos885_notes.tex, §5.5, "the 7-interface near-miss").
For `(Δ₂, Δ₃) = (48960, 196560)`, verification of `458 ∈ M(Δ₂, Δ₃)`:
`458² - 4 × 48960 = 209764 - 195840 = 13924` and `118² = 13924`.
`458² + 4 × 196560 = 209764 + 786240 = 996004` and `998² = 996004`. -/
theorem interface_458 :
    458 ^ 2 - 4 * 48960 = (118 : ℤ) ^ 2 ∧
    458 ^ 2 + 4 * 196560 = (998 : ℤ) ^ 2 := by
  constructor <;> norm_num

/-- **Computation 5.10** (continued). `496 ∈ M(Δ₂, Δ₃)`:
`496² - 4 × 48960 = 246016 - 195840 = 50176 = 224²`.
`496² + 4 × 196560 = 246016 + 786240 = 1032256 = 1016²`. -/
theorem interface_496 :
    496 ^ 2 - 4 * 48960 = (224 : ℤ) ^ 2 ∧
    496 ^ 2 + 4 * 196560 = (1016 : ℤ) ^ 2 := by
  constructor <;> norm_num

/-- **Computation 5.10** (continued). `528 ∈ M(Δ₂, Δ₃)`. -/
theorem interface_528 :
    528 ^ 2 - 4 * 48960 = (288 : ℤ) ^ 2 ∧
    528 ^ 2 + 4 * 196560 = (1032 : ℤ) ^ 2 := by
  constructor <;> norm_num

/-! ## Proposition 5.11: Quartic / hyperelliptic reformulation -/

/-- Numerical genus formula used for the quartic curve in the notes. -/
theorem quartic_genus_1 : (4 : ℤ) / 2 - 1 = 1 := by norm_num

/-- Numerical genus formula used for the degree-8 hyperelliptic curve in the
notes. -/
theorem hyperelliptic_genus_3 : ((8 : ℤ) - 2) / 2 = 3 := by norm_num
