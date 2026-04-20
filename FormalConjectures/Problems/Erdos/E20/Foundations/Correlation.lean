/-
# Correlation-Concentration Lemmas

This file formalizes the **correlation-concentration lemmas** from §2 Section 3
of the informal document.

## Informal references

### §2 Section 3: Correlation-concentration lemmas

"The cleanest one is:
  Σ_x d(x)² = Σ_{A,B ∈ H} |A ∩ B| ≥ m² / (k-1)."

### §2 Section 3: Structural version at every level

"For a set B, write d(B) = |{H ∈ H : B ⊆ H}|, and define
Γ_t = Σ_{|B|=t} d(B)².
Then for every 1 ≤ t < r, Γ_t ≤ (k-1)(t+1)(r-t) · Γ_{t+1}."

## Main results

- `degree_sum_eq_card_sum` : Σ_x d(x) = Σ_{e∈H} |e|
- `degree_sq_sum_eq_intersection_sum'` : Σ_x d(x)² = Σ_{A,B} |A∩B|
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Defs
import FormalConjectures.Problems.Erdos.E20.Foundations.SeedProfile

open Finset BigOperators

set_option maxHeartbeats 800000

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Degree definitions -/

/-- **Vertex degree** d(x) = |{e ∈ H : x ∈ e}| (§2 Section 3). -/
def vertexDegree' (H : Finset (Finset α)) (x : α) : ℕ :=
  (H.filter (fun e => x ∈ e)).card

/-- **Set degree** d(B) = |{e ∈ H : B ⊆ e}| (§2 Section 3). -/
def setDegree (H : Finset (Finset α)) (B : Finset α) : ℕ :=
  (H.filter (fun e => B ⊆ e)).card

/-! ## Degree sum identity -/

/-- **Degree sum identity** (§2 Section 3, standard double counting).
"Σ_x d(x) = Σ_{e ∈ H} |e|" — each vertex-edge incidence is counted once on each side. -/
theorem degree_sum_eq_card_sum (H : Finset (Finset α)) :
    ∑ x : α, (H.filter (fun e => x ∈ e)).card =
    ∑ e ∈ H, e.card := by
  simp only [card_filter]
  rw [Finset.sum_comm]
  congr 1; ext e
  simp [Finset.sum_boole, Finset.filter_mem_eq_inter]

/-! ## Sum of squared degrees equals total intersection -/

/-- **Intersection sum equals sum of squared degrees** (§2 Section 3).
"Σ_x d(x)² = Σ_{A,B ∈ H} |A ∩ B|" — the sum of squared degrees equals
the total pairwise intersection size. -/
theorem degree_sq_sum_eq_intersection_sum' (H : Finset (Finset α)) :
    ∑ x : α, (H.filter (fun e => x ∈ e)).card ^ 2 =
    ∑ A ∈ H, ∑ B ∈ H, (A ∩ B).card :=
  degree_sq_sum_eq_intersection_sum H

/-! ## Γ function definition -/

/-- **Γ function** Γ_t = Σ_{|B|=t} d(B)² (§2 Section 3, structural version).
The sum of squared set-degrees at level t. This is the key quantity in the
chain inequality Γ_t ≤ (k-1)(t+1)(r-t) · Γ_{t+1}. -/
noncomputable def gammaLevel (H : Finset (Finset α)) (t : ℕ) : ℕ :=
  ∑ B ∈ (Finset.univ : Finset α).powerset.filter (fun B => B.card = t),
    setDegree H B ^ 2
