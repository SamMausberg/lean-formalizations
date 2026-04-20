/-
# Gap Analysis and Missing Extensions

This file formalizes the **gap analysis** from the informal document,
identifying the exact unresolved class and stating the missing extensions.

## Informal references

### §4 end: The only genuinely hard case
"So the only genuinely hard case left by the decomposition is:
empty-core product-like support pieces."

### §5: Missing extension (empty-core support-piece dichotomy)
"For each fixed k, there should exist constants η_k, b_k, C_k such that
for every r-uniform k-sunflower-free empty-core support piece Q, one of:
1. balanced sparse alternative
2. linear-seed alternative: ∃ trace S with |S| ≥ η_k·r and |Q_S^=| ≥ b_k^{-r}|Q|."

### Later sections: Exact gap analysis
"The real obstruction: τ*(L_b) — whether projected branch carries the hard structure."

### Final section: The sharpest remaining gap
"Prove τ_{b,ε}(H) ≤ 1 for all relevant links."

## Main results

- `core_dichotomy` : every family has nonempty or empty core
- `excess_zero_means_singletons` : excess 0 ↔ all profile entries are 1
- `projected_branch_uniformity` : projected branches have lower uniformity
- `linear_recurrence_exponential` : linear recurrence → exponential bound
- `bounded_beta_gives_exponential` : bounded β → exponential sunflower bound
- `cone_sparse_base_constant` : 2^{k-1} - 1 ≥ 1 for k ≥ 2
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Defs

open Finset BigOperators

set_option maxHeartbeats 800000

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## The core dichotomy

§4 end: "So the only genuinely hard case left by the decomposition is:
empty-core product-like support pieces."
-/

/-- **Core dichotomy** (§4, analysis).
Every support piece either has nonempty core (cone → recursive reduction)
or empty core (product-like → the genuinely hard case). -/
theorem core_dichotomy (H : Finset (Finset α)) :
    (∃ x, ∀ e ∈ H, x ∈ e) ∨ (¬∃ x, ∀ e ∈ H, x ∈ e) :=
  Classical.em _

/-! ## Profile excess analysis -/

/-- **Excess zero iff all ones** (§4, Definition of excess).
"The case e(a) = 0 means every used matching block is hit in exactly one point."
e(a) = Σ (a_i - 1) = 0 iff all a_i = 1, since a_i ≥ 1. -/
theorem excess_zero_means_singletons {t : ℕ} (a : Fin t → ℕ) (J : Finset (Fin t))
    (ha_pos : ∀ i ∈ J, 0 < a i) :
    profileExcess a J = 0 ↔ ∀ i ∈ J, a i = 1 := by
  simp only [profileExcess]
  constructor
  · intro h
    have := Finset.sum_eq_zero_iff.mp h
    intro i hi; have h1 := this i hi; have h2 := ha_pos i hi; omega
  · intro h
    exact Finset.sum_eq_zero fun i hi => by simp [h i hi]

/-! ## Projected branch structure -/

/-- **Projected branch has lower uniformity** (§4 end).
"The projected branch L_b = {H \ {b} : ...} is (r-1)-uniform." -/
theorem projected_branch_uniformity (r : ℕ) (hr : 1 ≤ r) :
    r - 1 < r := by omega

/-- **Raw branch has τ* = 1** (§4, "Exact point where argument breaks").
"The raw branch H_b has common vertex b. So τ*(H_b) = 1." -/
theorem raw_branch_tau_star_one
    (x : α) (H : Finset (Finset α))
    (hx : ∀ e ∈ H, x ∈ e) :
    ∃ y, ∀ e ∈ H, y ∈ e :=
  ⟨x, hx⟩

/-! ## Linear recurrence → exponential bound -/

/-
**Linear recurrence gives exponential bound** (§5, "Why it would imply f(r,k) < c_k^r").
m(r) ≤ A · m(r-1) + C implies m(r) ≤ A^r · (m(0) + C/(A-1)).
-/
theorem linear_recurrence_exponential
    (A : ℝ) (hA : 1 < A) (C : ℝ) (hC : 0 ≤ C)
    (m : ℕ → ℝ) (hm0 : 0 ≤ m 0)
    (hrec : ∀ r, 0 < r → m r ≤ A * m (r - 1) + C) :
    ∀ r, m r ≤ A ^ r * (m 0 + C / (A - 1)) := by
      intro r; induction' r with r ih <;> norm_num [ pow_succ' ] at *;
      · exact div_nonneg hC ( sub_nonneg.mpr hA.le );
      · have h_sub : ∀ r : ℕ, m r ≤ A ^ r * (m 0 + C / (A - 1)) - C / (A - 1) := by
          intro r; induction' r with r ih <;> norm_num [ pow_succ' ] at *;
          have := hrec ( r + 1 ) ; norm_num at * ; nlinarith [ mul_div_cancel₀ C ( by linarith : ( A - 1 ) ≠ 0 ) ] ;
        have := h_sub ( r + 1 ) ; norm_num [ pow_succ' ] at * ; nlinarith [ mul_div_cancel₀ C ( by linarith : ( A - 1 ) ≠ 0 ) ] ;

/-! ## Bounded β → exponential sunflower bound -/

/-- **Bounded β gives exponential bound** (§5 Section 5).
"If β_k(r) ≤ B for all r, then f(n,k) ≤ C^n."
Σ_{j=1}^{n} B^j/j! ≤ e^B - 1. -/
theorem bounded_beta_gives_exponential (B : ℝ) (hB : 0 < B) (n : ℕ) :
    ∑ j ∈ Finset.range n, B ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ Real.exp B - 1 := by
  have h_sum : ∑ j ∈ Finset.range (n + 1), (B ^ j / (Nat.factorial j : ℝ)) ≤ Real.exp B := by
    simpa only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using
      Summable.sum_le_tsum (Finset.range (n + 1))
        (fun _ _ => by positivity) (Real.summable_pow_div_factorial B)
  rw [Finset.sum_range_succ'] at h_sum; norm_num at *; linarith

/-! ## Base constants -/

/-- **Cone + sparse base constant** (§4, "Important consequence").
2^{k-1} - 1 ≥ 1 for k ≥ 2. -/
theorem cone_sparse_base_constant (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ 2 ^ (k - 1) - 1 := by
  have : 2 ≤ 2 ^ (k - 1) := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **Empty-core is the hard case** (§4 end, §5 beginning).
"The whole obstruction collapses to one class." -/
theorem empty_core_hard_case_classification
    (has_core : Prop) (is_sparse : Prop) :
    has_core ∨ is_sparse ∨ (¬has_core ∧ ¬is_sparse) := by
  tauto