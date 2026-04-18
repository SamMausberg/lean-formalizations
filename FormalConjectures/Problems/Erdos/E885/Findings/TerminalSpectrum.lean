import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.RowComplex

/-!
# Two-Sided Terminal Spectra and Backward Rigidity

This file formalizes the exact two-sided square-translate sieve attached to a
candidate terminal column and the resulting rigidity for backward
reconstruction.

The main point is simple: once a terminal column `C` is fixed, every coherent
earlier column is already determined by a constant square shift
`u_t^2 = c_t^2 - 4Δ`, so backward reconstruction only translates the same
terminal spectrum. No new stitch values are created.
-/

set_option maxHeartbeats 4000000

namespace Erdos885
namespace TerminalSpectrum

/-- The two-sided terminal spectrum of a column `C`. -/
def terminalSpectrum {α : Sort*} (C : α → ℤ) : Set ℤ :=
  {Λ : ℤ | ∀ a, IsSquare (C a ^ 2 + 4 * Λ)}

/-- The canonical backward reconstruction attached to a negative spectral value
`-Δ ∈ terminalSpectrum C`. -/
def backwardColumn {α : Sort*} (C : α → ℤ) (Δ : ℤ) : α → ℤ :=
  fun a => Int.sqrt (C a ^ 2 - 4 * Δ)

/-- Two columns have the same square-step profile if all adjacent square
differences agree. -/
def sameSquareSteps {m : ℕ} (U C : Fin (m + 1) → ℤ) : Prop :=
  ∀ t : Fin m, U t.succ ^ 2 - U t.castSucc ^ 2 = C t.succ ^ 2 - C t.castSucc ^ 2

/-- Minimal exact-recursion interface: every adjacent row step is a common square
translate across all columns. -/
def exactRowComplex {m k : ℕ} (R : Fin (m + 1) → Fin (k + 1) → ℤ) : Prop :=
  ∀ t : Fin m, ∃ H : ℤ, ∀ j : Fin (k + 1), R t.succ j ^ 2 - R t.castSucc j ^ 2 = 4 * H

/-- The `j`-th column of a row complex. -/
def columnAt {m k : ℕ} (R : Fin (m + 1) → Fin (k + 1) → ℤ) (j : Fin (k + 1)) :
    Fin (m + 1) → ℤ :=
  fun t => R t j

/-- The rightmost column of a row complex. -/
def terminalColumn {m k : ℕ} (R : Fin (m + 1) → Fin (k + 1) → ℤ) : Fin (m + 1) → ℤ :=
  columnAt R (Fin.last k)

/-- Restricting to fewer row constraints can only enlarge the terminal
spectrum. -/
theorem terminalSpectrum_comp_subset {α β : Sort*} (C : β → ℤ) (f : α → β) :
    terminalSpectrum C ⊆ terminalSpectrum (fun a => C (f a)) := by
  intro Λ hΛ a
  exact hΛ (f a)

/-- Prefix monotonicity for finite columns: deleting the last row can only
enlarge the terminal spectrum. -/
theorem terminalSpectrum_castSucc_subset {m : ℕ} (C : Fin (m + 1) → ℤ) :
    terminalSpectrum C ⊆ terminalSpectrum (fun a : Fin m => C a.castSucc) :=
  terminalSpectrum_comp_subset C Fin.castSucc

/-- Single-row positive part of the spectrum: for a positive terminal entry `c`,
positive spectral values are exactly the values `x (x + c)` with `x > 0`. -/
theorem isSquare_add_four_mul_iff {c Λ : ℤ} (hc : 0 < c) (hΛ : 0 < Λ) :
    IsSquare (c ^ 2 + 4 * Λ) ↔ ∃ x : ℤ, 0 < x ∧ Λ = x * (x + c) := by
  constructor
  · intro hs
    let r := Int.sqrt (c ^ 2 + 4 * Λ)
    have hr_sq : r * r = c ^ 2 + 4 * Λ := by
      dsimp [r]
      exact (Int.exists_mul_self (c ^ 2 + 4 * Λ)).mp <| by
        rcases hs with ⟨n, hn⟩
        exact ⟨n, hn.symm⟩
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact Int.sqrt_nonneg _
    have hgt : c < r := by
      nlinarith [hr_sq, hc, hΛ]
    have hEven : Even (r - c) := by
      have h4 : Even (4 : ℤ) := by norm_num
      apply_fun Even at hr_sq
      simp [h4, parity_simps] at hr_sq
      simpa [parity_simps] using hr_sq
    refine ⟨(r - c) / 2, ?_, ?_⟩
    · have hdiv : (r - c) / 2 * 2 = r - c := Int.ediv_mul_cancel hEven.two_dvd
      nlinarith [hgt, hdiv]
    · have hdiv : (r - c) / 2 * 2 = r - c := Int.ediv_mul_cancel hEven.two_dvd
      nlinarith [hr_sq, hdiv]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨2 * x + c, ?_⟩
    ring

/-- Positive part of the terminal spectrum for a positive column. -/
theorem mem_terminalSpectrum_pos_iff {α : Sort*} {C : α → ℤ}
    (hC : ∀ a, 0 < C a) {Λ : ℤ} (hΛ : 0 < Λ) :
    Λ ∈ terminalSpectrum C ↔ ∀ a, ∃ x : ℤ, 0 < x ∧ Λ = x * (x + C a) := by
  constructor
  · intro hΛspec a
    exact (isSquare_add_four_mul_iff (hC a) hΛ).mp (hΛspec a)
  · intro h a
    exact (isSquare_add_four_mul_iff (hC a) hΛ).mpr (h a)

/-- Rewriting a negative spectral value as a downward square shift. -/
theorem neg_mem_terminalSpectrum_iff {α : Sort*} {C : α → ℤ} {Δ : ℤ} :
    -Δ ∈ terminalSpectrum C ↔ ∀ a, IsSquare (C a ^ 2 - 4 * Δ) := by
  constructor
  · intro h a
    have ha := h a
    have hEq : C a ^ 2 + 4 * (-Δ) = C a ^ 2 - 4 * Δ := by ring
    simpa [hEq] using ha
  · intro h a
    have ha := h a
    have hEq : C a ^ 2 - 4 * Δ = C a ^ 2 + 4 * (-Δ) := by ring
    simpa [hEq] using ha

/-- If a column is obtained by a constant downward square shift from `C`, then
the corresponding negative level lies in the terminal spectrum of `C`. -/
theorem neg_mem_terminalSpectrum_of_shift {α : Sort*} {U C : α → ℤ} {Δ : ℤ}
    (hshift : ∀ a, U a ^ 2 = C a ^ 2 - 4 * Δ) :
    -Δ ∈ terminalSpectrum C := by
  rw [neg_mem_terminalSpectrum_iff]
  intro a
  exact ⟨U a, by simpa [sq] using (hshift a).symm⟩

/-- Canonical square-root form of a negative spectral point. -/
theorem backwardColumn_sq {α : Sort*} {C : α → ℤ} {Δ : ℤ}
    (hΔ : -Δ ∈ terminalSpectrum C) (a : α) :
    backwardColumn C Δ a ^ 2 = C a ^ 2 - 4 * Δ := by
  dsimp [backwardColumn]
  have hs : IsSquare (C a ^ 2 - 4 * Δ) := (neg_mem_terminalSpectrum_iff.mp hΔ) a
  rcases hs with ⟨n, hn⟩
  have hsqrt : Int.sqrt (C a ^ 2 - 4 * Δ) * Int.sqrt (C a ^ 2 - 4 * Δ) = C a ^ 2 - 4 * Δ := by
    exact (Int.exists_mul_self (C a ^ 2 - 4 * Δ)).mp ⟨n, by simpa [sq] using hn.symm⟩
  simpa [sq] using hsqrt

/-- The reconstructed column is automatically nonnegative. -/
theorem backwardColumn_nonneg {α : Sort*} {C : α → ℤ} {Δ : ℤ} (a : α) :
    0 ≤ backwardColumn C Δ a := by
  dsimp [backwardColumn]
  exact Int.sqrt_nonneg _

/-- The reconstructed column is uniquely determined among nonnegative coherent
solutions. -/
theorem eq_backwardColumn_of_nonneg_sq {α : Sort*} {C : α → ℤ} {U : α → ℤ} {Δ : ℤ}
    (hU_nonneg : ∀ a, 0 ≤ U a) (hU_sq : ∀ a, U a ^ 2 = C a ^ 2 - 4 * Δ) :
    U = backwardColumn C Δ := by
  funext a
  calc
    U a = Int.sqrt (U a ^ 2) := by
      symm
      simpa [sq, Int.natAbs_of_nonneg (hU_nonneg a)] using Int.sqrt_eq (U a)
    _ = backwardColumn C Δ a := by
      rw [hU_sq a, backwardColumn]

/-- Backward reconstruction preserves all adjacent square differences. -/
theorem backwardColumn_sameSquareSteps {m : ℕ} {C : Fin (m + 1) → ℤ} {Δ : ℤ}
    (hΔ : -Δ ∈ terminalSpectrum C) :
    sameSquareSteps (backwardColumn C Δ) C := by
  intro t
  rw [backwardColumn_sq hΔ, backwardColumn_sq hΔ]
  ring

/-- Backward reconstruction translates the entire terminal spectrum. -/
theorem mem_terminalSpectrum_backwardColumn_iff {α : Sort*} {C : α → ℤ} {Δ Λ : ℤ}
    (hΔ : -Δ ∈ terminalSpectrum C) :
    Λ ∈ terminalSpectrum (backwardColumn C Δ) ↔ Λ - Δ ∈ terminalSpectrum C := by
  constructor
  · intro h a
    have ha : IsSquare (backwardColumn C Δ a ^ 2 + 4 * Λ) := h a
    have hEq : backwardColumn C Δ a ^ 2 + 4 * Λ = C a ^ 2 + 4 * (Λ - Δ) := by
      rw [backwardColumn_sq hΔ]
      ring
    simpa [hEq] using ha
  · intro h a
    have ha : IsSquare (C a ^ 2 + 4 * (Λ - Δ)) := h a
    have hEq : C a ^ 2 + 4 * (Λ - Δ) = backwardColumn C Δ a ^ 2 + 4 * Λ := by
      rw [backwardColumn_sq hΔ]
      ring
    simpa [hEq] using ha

/-- If two columns share all adjacent square differences, then a single base-row
shift forces the same shift on every row. -/
theorem sameSquareSteps_constant_shift {m : ℕ} {U C : Fin (m + 1) → ℤ} {Δ : ℤ}
    (hsteps : sameSquareSteps U C)
    (h0 : U 0 ^ 2 = C 0 ^ 2 - 4 * Δ) :
    ∀ t : Fin (m + 1), U t ^ 2 = C t ^ 2 - 4 * Δ := by
  have haux : ∀ i (hi : i < m + 1), U ⟨i, hi⟩ ^ 2 = C ⟨i, hi⟩ ^ 2 - 4 * Δ := by
    intro i
    induction i with
    | zero =>
        intro hi
        simpa using h0
    | succ i ih =>
        intro hi
        have hprev : U ⟨i, Nat.lt_of_succ_lt hi⟩ ^ 2 = C ⟨i, Nat.lt_of_succ_lt hi⟩ ^ 2 - 4 * Δ := by
          exact ih (Nat.lt_of_succ_lt hi)
        have hstep := hsteps ⟨i, Nat.lt_of_succ_lt_succ hi⟩
        have hstep' :
            U ⟨i + 1, hi⟩ ^ 2 - U ⟨i, Nat.lt_of_succ_lt hi⟩ ^ 2 =
              C ⟨i + 1, hi⟩ ^ 2 - C ⟨i, Nat.lt_of_succ_lt hi⟩ ^ 2 := by
          simpa using hstep
        nlinarith
  intro t
  simpa using haux t.1 t.2

/-- Any two columns of an exact row complex have the same square-step profile. -/
theorem sameSquareSteps_of_exactRowComplex {m k : ℕ}
    {R : Fin (m + 1) → Fin (k + 1) → ℤ} (hR : exactRowComplex R) (i j : Fin (k + 1)) :
    sameSquareSteps (columnAt R i) (columnAt R j) := by
  intro t
  rcases hR t with ⟨H, hH⟩
  have hi : columnAt R i t.succ ^ 2 - columnAt R i t.castSucc ^ 2 = 4 * H := by
    simpa [columnAt] using hH i
  have hj : columnAt R j t.succ ^ 2 - columnAt R j t.castSucc ^ 2 = 4 * H := by
    simpa [columnAt] using hH j
  nlinarith

/-- Backward reconstruction inside an exact row complex is forced by a single
base-row shift. -/
theorem exactRowComplex_constant_shift_to_terminal {m k : ℕ}
    {R : Fin (m + 1) → Fin (k + 1) → ℤ} (hR : exactRowComplex R) (j : Fin k) {Δ : ℤ}
    (h0 : R 0 j.castSucc ^ 2 = R 0 (Fin.last k) ^ 2 - 4 * Δ) :
    ∀ t : Fin (m + 1), R t j.castSucc ^ 2 = R t (Fin.last k) ^ 2 - 4 * Δ := by
  apply sameSquareSteps_constant_shift
  · exact sameSquareSteps_of_exactRowComplex hR j.castSucc (Fin.last k)
  · simpa [columnAt, terminalColumn] using h0

/-- Hence every such earlier column contributes a negative spectral value of the
terminal column. -/
theorem exactRowComplex_terminal_negative_level {m k : ℕ}
    {R : Fin (m + 1) → Fin (k + 1) → ℤ} (hR : exactRowComplex R) (j : Fin k) {Δ : ℤ}
    (h0 : R 0 j.castSucc ^ 2 = R 0 (Fin.last k) ^ 2 - 4 * Δ) :
    -Δ ∈ terminalSpectrum (terminalColumn R) := by
  apply neg_mem_terminalSpectrum_of_shift
  exact exactRowComplex_constant_shift_to_terminal hR j h0

/-! ## Long `3`-column chain example -/

/-- First column in the length-`8` chain from the notes. -/
def longChainC₁ : Fin 8 → ℤ :=
  ![126, 236, 448, 576, 828, 2368, 5404, 16308]

/-- Second column in the length-`8` chain from the notes. -/
def longChainC₂ : Fin 8 → ℤ :=
  ![894, 916, 992, 1056, 1212, 2528, 5476, 16332]

/-- Third column in the length-`8` chain from the notes. -/
def longChainC₃ : Fin 8 → ℤ :=
  ![1986, 1996, 2032, 2064, 2148, 3088, 5756, 16428]

/-- The second column is obtained from the third by the constant shift
`Δ = 786240`. -/
theorem longChainC₂_sq_eq_longChainC₃_sq_sub :
    ∀ t : Fin 8, longChainC₂ t ^ 2 = longChainC₃ t ^ 2 - 4 * 786240 := by
  intro t
  fin_cases t <;> norm_num [longChainC₂, longChainC₃]

/-- The first column is obtained from the third by the constant shift
`Δ = 982080`. -/
theorem longChainC₁_sq_eq_longChainC₃_sq_sub :
    ∀ t : Fin 8, longChainC₁ t ^ 2 = longChainC₃ t ^ 2 - 4 * 982080 := by
  intro t
  fin_cases t <;> norm_num [longChainC₁, longChainC₃]

/-- Accordingly, the rightmost column carries the negative spectral level
`-786240`. -/
theorem neg_786240_mem_longChainC₃_terminalSpectrum :
    (-786240 : ℤ) ∈ terminalSpectrum longChainC₃ := by
  apply neg_mem_terminalSpectrum_of_shift
  exact longChainC₂_sq_eq_longChainC₃_sq_sub

/-- And it also carries the negative spectral level `-982080`. -/
theorem neg_982080_mem_longChainC₃_terminalSpectrum :
    (-982080 : ℤ) ∈ terminalSpectrum longChainC₃ := by
  apply neg_mem_terminalSpectrum_of_shift
  exact longChainC₁_sq_eq_longChainC₃_sq_sub

end TerminalSpectrum
end Erdos885
