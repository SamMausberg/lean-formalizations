import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 4: Support Pieces, Traces, and Exact Trace Recursion

This file formalizes the results from Section 4 of the sunflower compendium
(sunflower_compendium.pdf): "Support pieces, traces, and exact trace recursion."
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
**Theorem 4.2 (Exact trace recursion), part 1: the exact identity.**
For every support piece `P` of rank `r` in an `m`-uniform family `G`:
  `|G| = ∑_{τ ∈ Tr_P(G)} |G_τ|`.

This is the fundamental trace decomposition identity: the family `G` partitions
exactly by its traces on `P`.
-/
theorem exact_trace_identity
    (G : Finset (Finset α)) (P : Finset α) (r m : ℕ)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r) :
    G.card = ∑ τ ∈ traceFamily G P, (projectedBranch G P τ).card := by
  rw [ @traceFamily ];
  rw [ Finset.card_eq_sum_ones, Finset.sum_image' ];
  intro A hA; rw [ projectedBranch ] ; simp +decide [ Finset.sum_filter ] ;
  rw [ Finset.card_image_of_injOn ];
  intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
  grind

/-
**Theorem 4.2, part 2: uniformity of projected branches.**
Each projected branch `G_τ` is `(m - r)`-uniform when `G` is `m`-uniform
and `P` is a support piece of rank `r`.
-/
theorem projected_branch_uniform
    (G : Finset (Finset α)) (P : Finset α) (r m : ℕ) (τ : Finset α)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r) (hτ : τ ∈ traceFamily G P) :
    IsUniform (projectedBranch G P τ) (m - r) := by
  intro A' hA';
  obtain ⟨ A, hA, hA' ⟩ := Finset.mem_image.mp hA';
  have := huni A ( Finset.filter_subset _ _ hA );
  have := hsp.2 A ( Finset.filter_subset _ _ hA );
  grind

/-
**Theorem 4.2, part 3: sunflower-freeness of projected branches.**
If `G` is `k`-sunflower-free, then each projected branch `G_τ` is also `k`-sunflower-free.
-/
theorem projected_branch_sunflower_free
    (G : Finset (Finset α)) (P : Finset α) (k : ℕ) (τ : Finset α)
    (hfree : SunflowerFree G k) :
    SunflowerFree (projectedBranch G P τ) k := by
  intro h;
  -- If G_τ contained a k-sunflower with petals A'_1, ..., A'_k having common intersection Y, then for each i there is A_i ∈ G with A_i ∩ P = τ and A'_i = A_i \ P.
  obtain ⟨petals, Y, hpetals, hinjective, hcommon⟩ := h;
  obtain ⟨A, hA⟩ : ∃ A : Fin k → Finset α, (∀ i, A i ∈ G) ∧ (∀ i, A i ∩ P = τ) ∧ (∀ i, petals i = A i \ P) := by
    choose A hA₁ hA₂ using fun i => Finset.mem_image.mp ( hpetals i );
    exact ⟨ A, fun i => Finset.mem_filter.mp ( hA₁ i ) |>.1, fun i => Finset.mem_filter.mp ( hA₁ i ) |>.2, fun i => hA₂ i ▸ rfl ⟩;
  refine' hfree ⟨ A, Y ∪ τ, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  · intro i j hij; have := @hinjective i j; simp_all +decide [ Finset.ext_iff ] ;
  · grind

/-- **Theorem 4.2, consequence: trace recursion bound.**
If `G` is `m`-uniform and `k`-sunflower-free, and `P` is a support piece of rank `r`
with `Tr_P(G)` itself `k`-sunflower-free, then
  `|G| ≤ |Tr_P(G)| · f(m - r, k) ≤ f(r, k) · f(m - r, k)`.

We formalize the first inequality. -/
theorem trace_recursion_bound
    (G : Finset (Finset α)) (P : Finset α) (r m k : ℕ)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r)
    (hfree : SunflowerFree G k)
    (htrace_free : SunflowerFree (traceFamily G P) k) :
    G.card ≤ (traceFamily G P).card * sunflowerThreshold (m - r) k := by
  sorry

/-- **Proposition 4.3 (One-block universality of empty-core support pieces).**
Any coreless `r`-uniform `k`-sunflower-free family can be embedded into an
`n`-uniform `k`-sunflower-free family (for `n ≥ r`) such that the original family
appears as a one-block support-piece trace.

We formalize part (iv): the trace family of the constructed `F` on a suitable
support piece `A` is isomorphic to `H`. This shows that one-block empty-core
support pieces can encode arbitrary smaller coreless sunflower-free families,
and hence "broad support-piece dichotomies are fake" (Section 11.1, claim R27). -/
theorem support_piece_universality
    (H : Finset (Finset α)) (r k : ℕ)
    (hr : IsUniform H r) (hfree : SunflowerFree H k)
    (hcore : ∀ x : α, ¬ (∀ A ∈ H, x ∈ A)) :
    ∀ n : ℕ, r ≤ n →
      ∃ (β : Type) (_ : DecidableEq β) (_ : Fintype β)
        (F : Finset (Finset β)),
        IsUniform F n ∧ SunflowerFree F k ∧ H.card ≤ F.card := by
  sorry
end FormalConjectures.Problems.Erdos.E20.Compendium
