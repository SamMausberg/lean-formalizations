import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 7: LP Bounded-Block Covers and Projected-Branch Obstructions

This file formalizes the results from Section 7 of the sunflower compendium
(sunflower_compendium.pdf): "LP bounded-block covers and projected-branch obstructions."
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Proposition 7.2 (Heavy seeds imply an exponential bound).**
If there exists `ε_k > 0` such that every nonempty `k`-sunflower-free `n`-uniform
family contains a nonempty `ε_k`-heavy block, then `f(n,k) ≤ ε_k^{-n}`.

We formalize: if `C ≥ 1` is such that for every nonempty `n`-uniform `k`-sunflower-free
family `F` there exists a nonempty set `S` with `|F| ≤ C^{|S|} · M(n - |S|, k)`,
then `M(n, k) ≤ C^n`. -/
theorem heavy_seeds_exponential
    (k : ℕ) (hk : 2 ≤ k)
    (C : ℕ) (hC : 1 ≤ C)
    (h : ∀ (β : Type*) [DecidableEq β] [Fintype β]
      (F : Finset (Finset β)) (n : ℕ),
      1 ≤ n → IsUniform F n → SunflowerFree F k → F.Nonempty →
      ∃ (S : Finset β), S.Nonempty ∧
        F.card ≤ C ^ S.card * sunflowerNumber (n - S.card) k) :
    ∀ n, sunflowerNumber n k ≤ C ^ n := by
  sorry

/-
**Proposition 7.4 (Cheap covers force heavy blocks).**
If `τ_{B,ε}(H) ≤ 1`, then `H` contains some block `T` with `|T| ≤ B`
such that `μ_H(T) ≥ ε^{|T|}`.

We formalize the averaging argument: if a weighted cover of `H` by small blocks
has the property that each edge is covered (sum ≥ 1), then the total weight
`∑_T x(T) · count(T)` is at least `|H|`, where `count(T) = |{E ∈ H : T ⊆ E}|`.
-/
theorem cheap_cover_total_weight
    (H : Finset (Finset α)) (B : ℕ)
    (x : Finset α → ℚ) (hx : ∀ T, 0 ≤ x T)
    (hcov : ∀ E ∈ H, ∑ T ∈ E.powerset.filter (fun T => T.card ≤ B), x T ≥ 1)
    (hH : H.Nonempty) :
    (↑H.card : ℚ) ≤
      ∑ T ∈ (Finset.univ : Finset α).powerset.filter (fun T => T.card ≤ B),
        x T * ↑(H.filter (fun E => T ⊆ E)).card := by
  have h_sum : (∑ E ∈ H, (∑ T ∈ (E.powerset) with T.card ≤ B, x T)) = (∑ T ∈ (Finset.univ.powerset) with T.card ≤ B, x T * ((H.filter (fun E => T ⊆ E)).card : ℚ)) := by
    have h_sum : ∑ E ∈ H, ∑ T ∈ E.powerset.filter (fun T => T.card ≤ B), x T = ∑ T ∈ Finset.univ.powerset.filter (fun T => T.card ≤ B), ∑ E ∈ H, (if T ⊆ E then x T else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +decide [ Finset.sum_ite ];
      intro E hE; rw [ ← Finset.sum_subset ( show Finset.filter ( fun T => T.card ≤ B ) ( Finset.powerset E ) ⊆ Finset.filter ( fun T => T ⊆ E ) ( Finset.filter ( fun T => T.card ≤ B ) Finset.univ ) from fun T hT => by aesop ) ] ; aesop;
    simp_all +decide [ Finset.sum_ite, mul_comm ];
  exact h_sum ▸ mod_cast le_trans ( by simp +decide ) ( Finset.sum_le_sum hcov )
end FormalConjectures.Problems.Erdos.E20.Compendium
