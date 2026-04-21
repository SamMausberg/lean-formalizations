import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 12: Recursive Closure of Solved Trace Classes

This file formalizes the results from Section 12 of the sunflower compendium
(sunflower_compendium.pdf): "Recursive closure of solved trace classes."

**Definition 12.1 (Solved trace class).** A trace class `C` is called solved with
base function `B_C(r, k)` if, whenever `G` is `k`-sunflower-free, `P` is a support
piece of rank `r`, and `Tr_P(G) ∈ C`, one has `|Tr_P(G)| ≤ B_C(r, k)`.
We represent the concept abstractly via bound hypotheses on trace family sizes.
-/

/-
**Theorem 12.2 (Exact one-step recursion over a solved trace class).**
If `G` has residual rank `m` and `P` is a support piece of rank `r` with
`|Tr_P(G)| ≤ B`, and each projected branch has size at most `f(m-r, k) - 1`,
then `|G| ≤ B · f(m-r, k)`.

We formalize this using the trace identity and the individual bounds.
-/
theorem one_step_recursion_over_solved_class
    {α : Type*} [DecidableEq α] [Fintype α]
    (G : Finset (Finset α)) (P : Finset α) (r m k B : ℕ)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r)
    (hfree : SunflowerFree G k)
    (trace_bound : (traceFamily G P).card ≤ B)
    (branch_bound : ∀ τ ∈ traceFamily G P,
      (projectedBranch G P τ).card ≤ sunflowerNumber (m - r) k) :
    G.card ≤ B * sunflowerThreshold (m - r) k := by
  -- By exact_trace_identity (from TraceRecursion.lean): G.card = ∑_{τ ∈ Tr_P(G)} |G_τ|.
  have exact_trace_identity : G.card = ∑ τ ∈ traceFamily G P, (projectedBranch G P τ).card := by
    unfold projectedBranch traceFamily;
    rw [ Finset.card_eq_sum_ones, Finset.sum_image' ];
    intro A hA; rw [ Finset.card_image_of_injOn ] ; aesop;
    intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
    grind;
  exact exact_trace_identity.symm ▸ le_trans ( Finset.sum_le_sum branch_bound ) ( by simp +decide [ sunflowerThreshold, mul_add ] ; nlinarith )

/-
**Theorem 12.2, recursive closure bound.**
If every `n`-uniform `k`-sunflower-free family has size at most `B^n`,
then `M(n,k) ≤ B^n`. This is the formal closure of the recursive argument.
-/
theorem recursive_closure_bound
    (B k : ℕ) (hk : 2 ≤ k)
    (h_base : ∀ (α : Type*) [DecidableEq α] [Fintype α]
      (G : Finset (Finset α)) (m : ℕ),
      IsUniform G m → SunflowerFree G k →
      G.card ≤ B ^ m) :
    ∀ n : ℕ, sunflowerNumber n k ≤ B ^ n := by
  intro n
  unfold sunflowerNumber
  apply csSup_le' _;
  rintro m ⟨ α, _, _, F, hF₁, hF₂, rfl ⟩;
  convert h_base ( ULift α ) ( F.image ( fun s => s.image ULift.up ) ) n _ _;
  · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using Finset.image_injective ( fun x y hxy => by simpa using hxy ) hxy ];
  · intro s hs;
    rw [ Finset.mem_image ] at hs; obtain ⟨ t, ht, rfl ⟩ := hs; rw [ Finset.card_image_of_injective _ ULift.up_injective ] ; exact hF₁ t ht;
  · rintro ⟨ petals, Y, hpetals₁, hpetals₂, hpetals₃ ⟩;
    refine' hF₂ _;
    use fun i => Finset.image ULift.down ( petals i ), Finset.image ULift.down Y;
    simp_all +decide [ Finset.ext_iff, Function.Injective ];
    refine' ⟨ fun i => _, hpetals₂ ⟩;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hpetals₁ i; convert ha₁; ext x; aesop;

end FormalConjectures.Problems.Erdos.E20.Compendium
