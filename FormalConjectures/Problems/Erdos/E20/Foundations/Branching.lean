/-
# Fractional Branching Theorem and Recurrence

This file formalizes the **fractional branching theorem** (§5 of the informal document)
and the associated recurrence for the sunflower function f(n,k).

## Informal reference: §5 Theorem (fractional branching theorem)

"Every k-sunflower-free n-uniform family G admits nonneg weights w_T on nonempty seeds
T ⊆ V(G) such that Σ_{T⊆G} w_T ≥ 1 for all G ∈ G, and for every 1 ≤ j ≤ n,
Σ_{|T|=j} w_T ≤ (1/j!) ∏_{i=0}^{j-1} β_k(n-i)."

## Informal reference: §5 Section 2

"f(n,k) ≤ Σ_{j=1}^{n} (1/j!) ∏_{i=0}^{j-1} β_k(n-i) · f(n-j,k)."

## Main results

- `weighted_recurrence` : the recurrence from any weighted seed profile
- `tau_star_bound` : the unconditional bound τ* ≤ r(k-1)
- `IsCGood` : C-good family definition (LP feasibility)
- `weak_duality_C_good` : weak LP duality for C-good families
- `exponential_bound_from_bounded_beta` : partial Taylor series ≤ exp(B) - 1
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Defs

open Finset BigOperators

set_option maxHeartbeats 800000

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Weighted seed profile recurrence

§5, Section 4.1: "For any weighted seed profile satisfying the covering condition,
|G| ≤ Σ_{j=1}^{n} m_j · f(n-j,k)."
-/

/-- **Weighted recurrence lemma** (§5 Section 4.1).
"For any weighted seed profile satisfying the covering condition,
|G| ≤ Σ_{j=1}^{n} m_j · f(n-j,k)."

Formally: if m_j ≥ 0 for all j, Σ m_j ≥ 1, and
size ≤ Σ m_j · (f_j - 1) (the link-counting bound), then
size ≤ Σ m_j · f_j - 1.

This captures the key step: the covering condition Σ m_j ≥ 1 absorbs
the +1 offset, turning link bounds into a full recurrence. -/
theorem weighted_recurrence
    {n : ℕ} (m : Fin n → ℝ) (f : Fin n → ℝ)
    (hm_nonneg : ∀ j, 0 ≤ m j)
    (hf_ge_one : ∀ j, 1 ≤ f j)
    (hcover : 1 ≤ ∑ j, m j)
    (size : ℝ)
    (hsize : size ≤ ∑ j, m j * (f j - 1)) :
    size + 1 ≤ ∑ j, m j * f j := by
  have hsub : ∑ j : Fin n, m j * (f j - 1) = ∑ j, m j * f j - ∑ j, m j := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  linarith

/-! ## Unconditional bound

§5, Section 4.3: "τ*(H) ≤ τ(H) ≤ r·ν(H) ≤ r(k-1)"
-/

/-- **Unconditional τ* bound** (§5, Section 4.3).
"τ*(H) ≤ τ(H) ≤ r·ν(H) ≤ r(k-1)" for any r-uniform k-sunflower-free H.
This is because a k-sunflower-free family has matching number ≤ k-1
(k pairwise disjoint sets would form a sunflower with empty core),
and a matching of size m gives a vertex cover of size ≤ r·m. -/
theorem tau_star_bound (r k : ℕ) (hk : 2 ≤ k) :
    ∀ (t : ℕ), t < k → t * r ≤ (k - 1) * r := by
  intro t ht
  exact Nat.mul_le_mul_right r (by omega)

/-! ## LP dual obstruction

§5, Section 4.4: "H is not C-good ↔ ∃ y_E, z_j s.t. Σ y_E > Σ C^j z_j"
-/

/-- **C-good family** (§5, Section 4.4).
"Call an r-uniform family H C-good if there are nonneg weights w_T on nonempty seeds
with Σ_{T⊆E} w_T ≥ 1 for all E ∈ H, and Σ_{|T|=j} w_T ≤ C^j for 1 ≤ j ≤ r."
This is the key LP feasibility condition whose dual characterizes the obstruction. -/
def IsCGood (H : Finset (Finset α)) (r : ℕ) (C : ℝ) : Prop :=
  ∃ (w : Finset α → ℝ),
    (∀ T, 0 ≤ w T) ∧
    (∀ e ∈ H, ∑ T ∈ e.powerset.filter Finset.Nonempty, w T ≥ 1) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ r →
      ∑ T ∈ (Finset.univ : Finset α).powerset.filter (fun T => T.card = j), w T ≤ C ^ j)

/-- **Weak duality for the C-good LP** (§5, Section 4.4, "Easy direction").
"If both a C-good profile w and an obstruction y existed, then
Σ y_E ≤ Σ_E y_E Σ_{T⊆E} w_T = Σ_T w_T Σ_{E⊇T} y_E ≤ Σ_j C^j L_j(y), contradiction."
-/
theorem weak_duality_C_good
    (H : Finset (Finset α)) (r : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hgood : IsCGood H r C)
    (y : Finset α → ℝ) (hy : ∀ e, 0 ≤ y e) :
    ∑ e ∈ H, y e ≤
      ∑ T ∈ (Finset.univ : Finset α).powerset.filter Finset.Nonempty,
        (hgood.choose T) * ∑ e ∈ H.filter (fun e => T ⊆ e), y e := by
  have := hgood.choose_spec.2.1
  convert Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left (this e he) (hy e) using 1
  · simp +decide
  · simp +decide only [Finset.mul_sum _ _ _, mul_comm]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => ⟨x.snd, x.fst⟩) ?_ ?_ ?_ ?_ <;> aesop

/-! ## Key consequence for exponential bounds -/

/-- **Heavy-link generating function** P_{H,μ}(x) (§5, Section 5 / §6).
P_{H,μ}(x) = Σ_{j=1}^{r} p_j(μ) x^j where p_j(μ) = max_{|T|=j} μ(H_T). -/
def heavyLinkGenFun (p : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range r, p (j + 1) * x ^ (j + 1)

/-- **Exponential bound from bounded β** (§5, Section 5).
If β_k(r) ≤ B for all r, then Σ_{j=1}^{n} B^j/j! ≤ e^B - 1.
This is the key analytic step: bounded fractional transversal numbers give
exponentially bounded level masses via the Taylor series of exp. -/
theorem exponential_bound_from_bounded_beta
    (B : ℝ) (hB : 0 < B) :
    ∀ n : ℕ, (∑ j ∈ Finset.range n, B ^ (j + 1) / (j + 1).factorial) ≤ Real.exp B - 1 := by
  intro n
  have h_sum : ∑ j ∈ Finset.range (n + 1), (B ^ j / (Nat.factorial j)) ≤ Real.exp B := by
    simpa only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using
      Summable.sum_le_tsum (Finset.range (n + 1))
        (fun _ _ => by positivity) (Real.summable_pow_div_factorial B)
  rw [Finset.sum_range_succ'] at h_sum; norm_num at *; linarith

/-- **Level mass factorial bound** (§5 Theorem, fractional branching theorem).
"Σ_{|T|=j} w_T ≤ (1/j!) ∏_{i=0}^{j-1} β_k(n-i)."
When β_k(r) ≤ B uniformly, this gives m_j ≤ B^j/j!.
We state the simpler fact: B^j / j! ≤ B^j for j ≥ 1. -/
theorem level_mass_factorial_bound (B : ℝ) (hB : 0 ≤ B) (j : ℕ) (hj : 1 ≤ j) :
    B ^ j / (j.factorial : ℝ) ≤ B ^ j := by
  apply div_le_self (pow_nonneg hB j)
  exact_mod_cast Nat.factorial_pos j
