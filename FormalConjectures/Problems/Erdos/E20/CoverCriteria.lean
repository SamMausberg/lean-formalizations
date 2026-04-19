/-
# Fractional Bounded-Block Cover Criterion

This file formalizes the **fractional bounded-block cover criterion** from §1 of the
final section of the informal document.

## Informal reference: §1 Theorem (fractional bounded-block cover criterion)

"If τ_{b,ε}(H) ≤ 1, then H contains a block S with 1 ≤ |S| ≤ b and q_H(S) ≥ ε^{|S|}."

## Informal reference: §2 Full proof

The proof is by contradiction: average the cover inequality over the branch measure,
swap sums, and use the contradictory assumption q_H(S) < ε^{|S|} to get 1 < 1.

## Main results

- `fractional_cover_criterion` : the main theorem
- `dual_obstruction` : the dual characterization via LP duality
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Defs

open Finset BigOperators

set_option maxHeartbeats 800000

/-! ## Fractional bounded-block cover number

§1, Definition: τ_{b,ε}(H) = inf { Σ w_S · ε^{|S|} : w covers all branches }
-/

/-
**Fractional bounded-block cover criterion** (§1 Theorem).
If there exist nonneg weights w_S on blocks S with 1 ≤ |S| ≤ b such that
(1) Σ_{S⊆A, 1≤|S|≤b} w_S ≥ 1 for every branch A in the support, and
(2) Σ_{1≤|S|≤b} w_S · ε^{|S|} ≤ 1,
then some block S with 1 ≤ |S| ≤ b has q_H(S) ≥ ε^{|S|}.

The proof is by contradiction: assume q_H(S) < ε^{|S|} for all S.
Average the cover inequality (1) over A ~ μ_H:
1 ≤ Σ_S w_S · q_H(S) < Σ_S w_S · ε^{|S|} ≤ 1, contradiction.

Here we state the abstract version: given a probability measure μ on a finite set Ω,
and a function q : Finset Ω → ℝ measuring how much mass lands on each block,
if there is a cheap cover, then some block is heavy.
-/
theorem fractional_cover_criterion
    {Ω : Type*} [DecidableEq Ω] [Fintype Ω]
    (μ : Ω → ℝ) (hμ_nonneg : ∀ a, 0 ≤ μ a) (hμ_prob : ∑ a, μ a = 1)
    (b : ℕ) (ε : ℝ) (hε : 0 < ε)
    (blocks : Finset (Finset Ω))
    (hblocks_size : ∀ S ∈ blocks, 1 ≤ S.card ∧ S.card ≤ b)
    (w : Finset Ω → ℝ) (hw_nonneg : ∀ S, 0 ≤ w S)
    (hcover : ∀ a : Ω, μ a > 0 →
      ∑ S ∈ blocks.filter (fun S => a ∈ S), w S ≥ 1)
    (hcost : ∑ S ∈ blocks, w S * ε ^ S.card ≤ 1) :
    ∃ S ∈ blocks,
      ∑ a ∈ Finset.univ.filter (fun a => a ∈ S), μ a ≥ ε ^ S.card := by
  contrapose! hcost with hcost;
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a, μ a * (∑ S ∈ blocks with a ∈ S, w S) = ∑ S ∈ blocks, w S * ∑ a ∈ S, μ a := by
    simp +decide only [sum_filter, Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; simp +contextual [ mul_comm ];
  -- Applying the hypothesis `hcost` to each term in the sum, we get:
  have h_sum_lt : ∑ S ∈ blocks, w S * (∑ a ∈ S, μ a) < ∑ S ∈ blocks, w S * ε ^ (Finset.card S) := by
    apply Finset.sum_lt_sum;
    · exact fun S hS => mul_le_mul_of_nonneg_left ( by simpa using le_of_lt ( hcost S hS ) ) ( hw_nonneg S );
    · by_cases h_empty : ∀ S ∈ blocks, w S = 0;
      · obtain ⟨a, ha⟩ : ∃ a, μ a > 0 := by
          exact not_forall_not.mp fun h => by rw [ Finset.sum_eq_zero fun a _ => le_antisymm ( le_of_not_gt fun ha => h a ha ) ( hμ_nonneg a ) ] at hμ_prob; norm_num at hμ_prob;
        exact absurd ( hcover a ha ) ( by rw [ Finset.sum_eq_zero fun S hS => h_empty S ( Finset.mem_filter.mp hS |>.1 ) ] ; norm_num );
      · exact by push_neg at h_empty; obtain ⟨ S, hS₁, hS₂ ⟩ := h_empty; exact ⟨ S, hS₁, mul_lt_mul_of_pos_left ( by simpa using hcost S hS₁ ) ( lt_of_le_of_ne ( hw_nonneg S ) ( Ne.symm hS₂ ) ) ⟩ ;
  refine' lt_of_le_of_lt _ h_sum_lt;
  rw [ ← h_fubini, ← hμ_prob ];
  exact Finset.sum_le_sum fun a _ => if ha : μ a = 0 then by simp +decide [ ha ] else by nlinarith only [ hμ_nonneg a, hcover a ( lt_of_le_of_ne ( hμ_nonneg a ) ( Ne.symm ha ) ), ha ] ;

/-
**Weak LP duality for block cover** (§2, dual statement).
"If q_H(S) ≤ ε^{|S|} for all 1 ≤ |S| ≤ b, then the branch distribution μ_H(A)
is feasible for ν_{b,ε} with total mass 1, hence ν_{b,ε}(H) ≥ 1,
and therefore τ_{b,ε}(H) ≥ 1."

Stated abstractly: if no block is heavy, then no cheap cover exists.
-/
theorem dual_obstruction
    {Ω : Type*} [DecidableEq Ω] [Fintype Ω]
    (μ : Ω → ℝ) (hμ_nonneg : ∀ a, 0 ≤ μ a) (hμ_prob : ∑ a, μ a = 1)
    (b : ℕ) (ε : ℝ) (hε : 0 < ε)
    (blocks : Finset (Finset Ω))
    (hblocks_size : ∀ S ∈ blocks, 1 ≤ S.card ∧ S.card ≤ b)
    (hno_heavy : ∀ S ∈ blocks,
      ∑ a ∈ Finset.univ.filter (fun a => a ∈ S), μ a < ε ^ S.card)
    (w : Finset Ω → ℝ) (hw_nonneg : ∀ S, 0 ≤ w S)
    (hcover : ∀ a : Ω, μ a > 0 →
      ∑ S ∈ blocks.filter (fun S => a ∈ S), w S ≥ 1) :
    1 < ∑ S ∈ blocks, w S * ε ^ S.card := by
  -- Apply the fractional cover criterion with the given conditions.
  by_contra h_contra
  have h_cover : ∃ S ∈ blocks, ∑ a ∈ Finset.univ.filter (fun a => a ∈ S), μ a ≥ ε ^ S.card := by
    apply fractional_cover_criterion μ hμ_nonneg hμ_prob b ε hε blocks hblocks_size w hw_nonneg hcover (by
    linarith);
  exact not_lt_of_ge h_cover.choose_spec.2 ( hno_heavy _ h_cover.choose_spec.1 )

/-! ## Weak duality for general LP

§5, Section 4.4: General weak duality for covering LPs.
-/

/-
**General weak LP duality** (§5, Section 4.4, standard).
For any feasible primal solution (λ) to the packing LP and feasible dual solution (w)
to the covering LP, the primal objective ≤ dual objective.
Σ_A λ_A ≤ Σ_A λ_A · Σ_{S⊆A} w_S = Σ_S w_S · Σ_{A⊇S} λ_A ≤ Σ_S w_S · c_S.

This is formalized as: if λ_A and w_S are nonneg,
Σ_{S⊆A} w_S ≥ 1 for all A, and Σ_{A⊇S} λ_A ≤ c_S for all S,
then Σ_A λ_A ≤ Σ_S w_S · c_S.
-/
theorem general_weak_lp_duality
    {Ω S_type : Type*} [Fintype Ω] [Fintype S_type] [DecidableEq Ω] [DecidableEq S_type]
(lam : Ω → ℝ) (w : S_type → ℝ) (c : S_type → ℝ)
    (contains : S_type → Ω → Bool)
    (hlam_nonneg : ∀ a, 0 ≤ lam a)
    (hw_nonneg : ∀ s, 0 ≤ w s)
    (hc_nonneg : ∀ s, 0 ≤ c s)
    (hcover : ∀ a : Ω, ∑ s ∈ Finset.univ.filter (fun s => contains s a), w s ≥ 1)
    (hpacking : ∀ s : S_type, ∑ a ∈ Finset.univ.filter (fun a => contains s a), lam a ≤ c s) :
    ∑ a : Ω, lam a ≤ ∑ s : S_type, w s * c s := by
  have h_dual_obstruction : ∑ a, lam a ≤ ∑ s, w s * ∑ a with contains s a = true, lam a := by
    have h_dual_obstruction : ∑ a, lam a ≤ ∑ a, ∑ s with contains s a = true, w s * lam a := by
      exact Finset.sum_le_sum fun a _ => by simpa only [ ← Finset.sum_mul _ _ _ ] using le_mul_of_one_le_left ( hlam_nonneg a ) ( hcover a ) ;
    convert h_dual_obstruction using 1;
    simp +decide only [sum_filter, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring );
  exact h_dual_obstruction.trans ( Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ( hpacking s ) ( hw_nonneg s ) )