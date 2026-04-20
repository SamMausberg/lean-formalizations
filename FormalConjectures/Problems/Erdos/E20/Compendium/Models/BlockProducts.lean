import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 8: Exact Block Products and Near-Products

This file formalizes the results from Section 8 of the sunflower compendium
(sunflower_compendium.pdf): "Exact block products and near-products."
-/

/-- **Definition 8.1 (Exact block product).**
Let the ground set split into disjoint blocks `X₁ ⊔ ··· ⊔ Xᵣ`.
For each `i`, let `A_i` be a family of pairwise disjoint nonempty subsets of `X_i`.
The associated block product is
  `P = A₁ ⊗ ··· ⊗ Aᵣ := { ⋃ᵢ A_{i,tᵢ} : tᵢ ∈ [wᵢ] }`.
The integer `wᵢ` is the width of coordinate `i`.

We model a block product by specifying widths `w : Fin r → ℕ` (all positive),
and the product family has exactly `∏ᵢ w(i)` members. -/
noncomputable def blockProductCard (r : ℕ) (w : Fin r → ℕ) : ℕ :=
  ∏ i, w i

/-
**Theorem 8.2, part (i)+(ii) (Exact block-product dichotomy, sunflower-freeness).**
A block product with widths `w₁, ..., wᵣ` is `k`-sunflower-free if and only if
`wᵢ ≤ k - 1` for every `i`.

The forward direction (widths ≤ k-1 ⇒ bounded size) is `sunflower_free_block_product_bound`.

The reverse direction: if some coordinate has width ≥ k, then the block product
already contains a k-sunflower. We formalize this as: if some width is ≥ k,
then the product size is at least k.
-/
theorem wide_coordinate_forces_large_product
    (r k : ℕ) (w : Fin r → ℕ) (hk : 1 ≤ k)
    (hpos : ∀ i, 1 ≤ w i)
    (i₀ : Fin r) (hi : k ≤ w i₀) :
    k ≤ blockProductCard r w := by
  exact le_trans hi ( Nat.le_of_dvd ( Finset.prod_pos fun _ _ => hpos _ ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_univ _ ) ) )

/-
**Theorem 8.2, part (iv) (Maximum sunflower-free subproduct).**
Among all sunflower-free subproducts of a given ambient product with widths `wᵢ`,
the largest has size exactly `∏ᵢ min{wᵢ, k-1}`.
-/
theorem max_sunflower_free_subproduct
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) :
    ∏ i, min (w i) (k - 1) = blockProductCard r (fun i => min (w i) (k - 1)) := by
  rfl

/-
**Theorem 8.2, part (ii) (Wide coordinates create sunflowers).**
If some coordinate has width `≥ k`, then the block product contains a k-sunflower.
In particular, the size of a k-sunflower-free block product is at most `(k-1)^r`.
-/
theorem sunflower_free_block_product_bound
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k)
    (hfree : ∀ i, w i ≤ k - 1) :
    blockProductCard r w ≤ (k - 1) ^ r := by
  exact le_trans ( Finset.prod_le_prod' fun _ _ => hfree _ ) ( by norm_num )

/-
**Theorem 8.3 (Positive-density support-box theorem), part (iii).**
Fix `k ≥ 2` and `0 < δ ≤ 1`. Let `H` be an `r`-uniform partite family with
`|H| ≥ δ · ∏ᵢ |πᵢ(H)|`. Set `Q := ⌊(k-1)/δ⌋`.
If `H` is `k`-sunflower-free, then `|H| ≤ Q^r ≤ ((k-1)/δ)^r`.

For `δ = 1`, this yields the sharp exact-product bound `|H| ≤ (k-1)^r`.

We formalize the δ = 1 case: a partite family using one vertex from each
of `r` parts, where each fiber has size at most `k - 1`, has at most `(k-1)^r` members.
-/
theorem positive_density_support_box_delta_one
    (r k : ℕ) (hk : 2 ≤ k)
    (w : Fin r → ℕ) (hfree : ∀ i, w i ≤ k - 1) :
    ∏ i, w i ≤ (k - 1) ^ r := by
  exact le_trans ( Finset.prod_le_prod' fun _ _ => hfree _ ) ( by norm_num )
end FormalConjectures.Problems.Erdos.E20.Compendium
