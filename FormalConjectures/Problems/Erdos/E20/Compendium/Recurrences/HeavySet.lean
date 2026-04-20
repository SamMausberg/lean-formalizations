import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 5: The Exact Γ_t/β_t Formalism and the Kernel-Prefix Criterion

This file formalizes the results from Section 5 of the sunflower compendium
(sunflower_compendium.pdf): "The exact Γ_t/β_t formalism and the kernel-prefix criterion."
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
**Lemma 5.1 (Moment propagation), first identity.**
For an `n`-uniform family `F`, `Λ_t(F) = C(n,t) · |F|`.
This is a direct double-counting identity.
-/
theorem lambda_identity
    (F : Finset (Finset α)) (n t : ℕ) (hn : IsUniform F n) (ht : t ≤ n) :
    lambdaT F t = n.choose t * F.card := by
  -- By double counting: this sum counts pairs (B, A) where B is a t-element subset and A ∈ F with B ⊆ A.
  have h_double_count : (∑ B ∈ (Finset.univ.powersetCard t), (familyDegree F B)) = (∑ A ∈ F, (Finset.powersetCard t A).card) := by
    simp +decide only [familyDegree];
    simp +decide only [card_eq_sum_ones, sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro A hA; rw [ ← Finset.sum_filter ] ; congr; ext; aesop;
  simp_all +decide [ IsUniform ];
  exact h_double_count.trans ( mul_comm _ _ )

/-
**Theorem 5.2 (Exact heavy-set lemma).**
For every `0 ≤ t ≤ n`,
  `M_t(F) := max_{|S|=t} d_F(S) ≥ Γ_t(F) / Λ_t(F)`.

Equivalently, `M_t(F) · Λ_t(F) ≥ Γ_t(F)`, i.e., the maximum t-degree
times the sum of t-degrees is at least the sum of squared t-degrees.
This is the Cauchy–Schwarz / pigeonhole inequality.
-/
theorem heavy_set_lemma
    (F : Finset (Finset α)) (n t : ℕ) (hn : IsUniform F n)
    (hne : F.Nonempty) (ht : t ≤ n) :
    ∃ S ∈ (Finset.univ : Finset α).powersetCard t,
      familyDegree F S * lambdaT F t ≥ gammaT F t := by
  -- By definition of $M_t(F)$, we know that $M_t(F) \geq \frac{\Gamma_t(F)}{\Lambda_t(F)}$.
  have h_Mt : ∃ S ∈ Finset.powersetCard t (Finset.univ : Finset α), ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset α), familyDegree F S ≥ familyDegree F T := by
    apply_rules [ Finset.exists_max_image ];
    simp +decide [ Finset.card_univ, ht ];
    exact le_trans ht ( hn _ hne.choose_spec ▸ Finset.card_le_univ _ );
  obtain ⟨ S, hS₁, hS₂ ⟩ := h_Mt;
  refine' ⟨ S, hS₁, _ ⟩;
  rw [ gammaT, lambdaT ];
  simpa only [ sq, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun T hT => Nat.mul_le_mul_right _ ( hS₂ T hT )

/-
**Corollary 5.4 (Exact recursive upper bound).**
If `F` is `n`-uniform and `k`-sunflower-free, and every `t`-link has size at most
`g(n-t, k) = M(n-t, k)`, then the maximum `t`-degree is at most `M(n-t, k)`.
Combined with the heavy-set lemma, this gives `|F| ≤ g(n-t,k) / B_{n,k}(t)`.
-/
theorem recursive_upper_bound
    (F : Finset (Finset α)) (n k : ℕ) (t : ℕ)
    (hn : IsUniform F n) (hk : 2 ≤ k) (ht : t ≤ n)
    (hfree : SunflowerFree F k) :
    ∀ S ∈ (Finset.univ : Finset α).powersetCard t,
      familyDegree F S ≤ sunflowerNumber (n - t) k := by
  intro S hS
  have h_link : IsUniform (familyLink F S) (n - t) := by
    intro A hA
    obtain ⟨B, hB, h_eq⟩ : ∃ B ∈ F, S ⊆ B ∧ A = B \ S := by
      unfold familyLink at hA; aesop;
    have hB_card : B.card = n := hn B hB
    have hA_card : A.card = n - t := by
      grind
    exact hA_card
  have h_free : SunflowerFree (familyLink F S) k := by
    intro h;
    obtain ⟨petals, Y, hpetals, h_inj, h_inter⟩ := h;
    -- Since petals are in the link, each petals i is of the form A \ S for some A in F with S ⊆ A.
    obtain ⟨A, hA⟩ : ∃ A : Fin k → Finset α, (∀ i, A i ∈ F) ∧ (∀ i, S ⊆ A i) ∧ (∀ i, petals i = A i \ S) := by
      choose A hA using fun i => Finset.mem_image.mp ( hpetals i ) ; use A; aesop;
    refine' hfree ⟨ A, Y ∪ S, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
    · intro i j hij; have := @h_inj i j; simp_all +decide [ Finset.ext_iff ] ;
    · grind
  have h_card : (familyLink F S).card = familyDegree F S := by
    rw [ familyLink, familyDegree, Finset.card_image_of_injOn ];
    intro A hA B hB hAB; simp_all +decide [ Finset.ext_iff ] ;
    grind +ring
  -- The link familyLink F S has card = familyDegree F S,
  -- is (n-t)-uniform and k-sunflower-free.
  -- So familyDegree F S = |familyLink F S| ≤ sunflowerNumber (n-t) k by definition.
  rw [h_card] at *
  sorry

/-
**Theorem 5.6 (Adaptive kernel-prefix criterion).**
This is the central conditional reduction theorem of the paper.
Let `K_k` be a class of reduced kernel links equipped with an essential-rank
function. If there exists `λ_k > 1` such that every nontrivial reduced kernel
link has some prefix block of length `t` with `∏_{i<t} β_i(H) ≥ λ_k^{-t}`,
then `g(n,k) ≤ λ_k^n`.

We state a simplified version: if every n-uniform k-sunflower-free family
has a nonempty ε-heavy block (as in Proposition 7.2), then f(n,k) ≤ ε^{-n}.
This corresponds to the "heavy seeds imply an exponential bound" principle
(Proposition 7.2 from Section 7).
-/
theorem heavy_seeds_imply_exponential_bound
    (k : ℕ) (hk : 2 ≤ k) (C : ℕ)
    (h_heavy : ∀ (β : Type) [DecidableEq β] [Fintype β]
      (F : Finset (Finset β)) (n : ℕ),
      1 ≤ n → IsUniform F n → SunflowerFree F k → F.Nonempty →
      ∃ (S : Finset β), S.Nonempty ∧ S.card ≤ n ∧
        F.card ≤ C ^ S.card * sunflowerNumber (n - S.card) k) :
    ∀ n : ℕ, sunflowerNumber n k ≤ C ^ n := by
  intro n;
  -- By induction on $n$, we can show that $M(n,k) \leq C^n$.
  induction' n using Nat.strong_induction_on with n ih;
  refine' csSup_le' _;
  rintro m ⟨ α, _, _, F, hF₁, hF₂, rfl ⟩;
  by_cases hn : 1 ≤ n;
  · by_cases hF₃ : F.Nonempty;
    · obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := h_heavy α F n hn hF₁ hF₂ hF₃;
      refine le_trans hS₃ ?_;
      exact le_trans ( Nat.mul_le_mul_left _ ( ih _ ( Nat.sub_lt hn ( Finset.card_pos.mpr hS₁ ) ) ) ) ( by rw [ ← pow_add, Nat.add_sub_of_le hS₂ ] );
    · aesop;
  · interval_cases n ; simp_all +decide [ IsUniform ];
    exact Finset.card_le_one.mpr fun x hx y hy => hF₁ x hx ▸ hF₁ y hy ▸ rfl
end FormalConjectures.Problems.Erdos.E20.Compendium
