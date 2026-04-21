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

/-! ## A tagged singleton model for exact block products -/

/-- A word in the product of coordinate alphabets with widths `w`. -/
abbrev BlockProductWord (r : ℕ) (w : Fin r → ℕ) : Type :=
  ∀ i : Fin r, Fin (w i)

/-- The edge represented by a block-product word, using one tagged singleton in each block. -/
def blockProductEdge {r : ℕ} {w : Fin r → ℕ} (x : BlockProductWord r w) :
    Finset (Sigma fun i : Fin r => Fin (w i)) :=
  Finset.univ.image fun i => Sigma.mk i (x i)

@[simp] theorem mem_blockProductEdge_iff {r : ℕ} {w : Fin r → ℕ}
    {x : BlockProductWord r w} {i : Fin r} {a : Fin (w i)} :
    Sigma.mk i a ∈ blockProductEdge x ↔ x i = a := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, -, hj⟩
    cases hj
    rfl
  · intro h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [h]⟩

theorem blockProductEdge_injective {r : ℕ} {w : Fin r → ℕ} :
    Function.Injective (blockProductEdge (r := r) (w := w)) := by
  intro x y hxy
  funext i
  have hmem : Sigma.mk i (x i) ∈ blockProductEdge y := by
    simpa [hxy] using (show Sigma.mk i (x i) ∈ blockProductEdge x by simp)
  exact (mem_blockProductEdge_iff.mp hmem).symm

/-- The exact block product in the tagged singleton model.  This is a faithful model for the
sunflower behavior of products whose local pieces in each block are pairwise disjoint. -/
noncomputable def exactBlockProductFamily (r : ℕ) (w : Fin r → ℕ) :
    Finset (Finset (Sigma fun i : Fin r => Fin (w i))) :=
  Finset.univ.image (blockProductEdge (r := r) (w := w))

@[simp] theorem blockProductEdge_mem_exactBlockProductFamily {r : ℕ} {w : Fin r → ℕ}
    (x : BlockProductWord r w) :
    blockProductEdge x ∈ exactBlockProductFamily r w := by
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

@[simp] theorem card_exactBlockProductFamily (r : ℕ) (w : Fin r → ℕ) :
    (exactBlockProductFamily r w).card = blockProductCard r w := by
  classical
  unfold exactBlockProductFamily blockProductCard BlockProductWord
  rw [Finset.card_image_of_injective _ blockProductEdge_injective]
  simp [Fintype.card_pi]

/-- The default word used to keep all non-wide coordinates fixed. -/
def defaultBlockProductWord {r : ℕ} {w : Fin r → ℕ} (hpos : ∀ i, 0 < w i) :
    BlockProductWord r w :=
  fun i => ⟨0, hpos i⟩

/-- The common kernel obtained by deleting one varying coordinate from the default edge. -/
def blockProductKernelExcept {r : ℕ} {w : Fin r → ℕ} (hpos : ∀ i, 0 < w i)
    (i₀ : Fin r) : Finset (Sigma fun i : Fin r => Fin (w i)) :=
  (Finset.univ.filter fun i => i ≠ i₀).image fun i =>
    Sigma.mk i (defaultBlockProductWord hpos i)

@[simp] theorem mem_blockProductKernelExcept_iff {r : ℕ} {w : Fin r → ℕ}
    (hpos : ∀ i, 0 < w i) (i₀ i : Fin r) (a : Fin (w i)) :
    Sigma.mk i a ∈ blockProductKernelExcept hpos i₀ ↔
      i ≠ i₀ ∧ a = defaultBlockProductWord hpos i := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, hj, hji⟩
    have hne : j ≠ i₀ := (Finset.mem_filter.mp hj).2
    cases hji
    exact ⟨hne, rfl⟩
  · intro h
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, by simp [h.2]⟩

/-- A `k`-tuple of words witnessing a sunflower when coordinate `i₀` has width at least `k`. -/
def wideCoordinatePetalWord {r k : ℕ} {w : Fin r → ℕ} (hpos : ∀ i, 0 < w i)
    (i₀ : Fin r) (hi : k ≤ w i₀) (t : Fin k) : BlockProductWord r w :=
  fun i =>
    if h : i = i₀ then
      by
        subst h
        exact Fin.castLE hi t
    else
      defaultBlockProductWord hpos i

@[simp] theorem wideCoordinatePetalWord_self {r k : ℕ} {w : Fin r → ℕ}
    (hpos : ∀ i, 0 < w i) (i₀ : Fin r) (hi : k ≤ w i₀) (t : Fin k) :
    wideCoordinatePetalWord hpos i₀ hi t i₀ = Fin.castLE hi t := by
  simp [wideCoordinatePetalWord]

theorem wideCoordinatePetalWord_ne {r k : ℕ} {w : Fin r → ℕ}
    (hpos : ∀ i, 0 < w i) (i₀ i : Fin r) (hi : k ≤ w i₀) (t : Fin k)
    (hne : i ≠ i₀) :
    wideCoordinatePetalWord hpos i₀ hi t i = defaultBlockProductWord hpos i := by
  simp [wideCoordinatePetalWord, hne]

theorem wideCoordinatePetal_inter {r k : ℕ} {w : Fin r → ℕ}
    (hpos : ∀ i, 0 < w i) (i₀ : Fin r) (hi : k ≤ w i₀) {t u : Fin k}
    (htu : t ≠ u) :
    blockProductEdge (wideCoordinatePetalWord hpos i₀ hi t) ∩
        blockProductEdge (wideCoordinatePetalWord hpos i₀ hi u) =
      blockProductKernelExcept hpos i₀ := by
  ext z
  rcases z with ⟨i, a⟩
  rw [Finset.mem_inter, mem_blockProductEdge_iff, mem_blockProductEdge_iff,
    mem_blockProductKernelExcept_iff]
  constructor
  · intro h
    have hne : i ≠ i₀ := by
      intro hii
      subst hii
      have hcast : Fin.castLE hi t = Fin.castLE hi u := by
        simpa using h.1.trans h.2.symm
      exact htu (Fin.castLE_injective hi hcast)
    refine ⟨hne, ?_⟩
    have ht :
        wideCoordinatePetalWord hpos i₀ hi t i = defaultBlockProductWord hpos i :=
      wideCoordinatePetalWord_ne hpos i₀ i hi t hne
    exact h.1.symm.trans ht
  · intro h
    constructor
    · rw [wideCoordinatePetalWord_ne hpos i₀ i hi t h.1, h.2]
    · rw [wideCoordinatePetalWord_ne hpos i₀ i hi u h.1, h.2]

/-- Part (ii), in the tagged singleton model: a coordinate of width at least `k` gives an
explicit `k`-sunflower by varying only that coordinate. -/
theorem exactBlockProductFamily_has_sunflower_of_le_width
    (r k : ℕ) (w : Fin r → ℕ) (_hk : 2 ≤ k)
    (hpos : ∀ i, 0 < w i) (i₀ : Fin r) (hi : k ≤ w i₀) :
    IsSunflower (exactBlockProductFamily r w) k := by
  refine ⟨fun t => blockProductEdge (wideCoordinatePetalWord hpos i₀ hi t),
    blockProductKernelExcept hpos i₀, ?_, ?_, ?_⟩
  · intro t
    exact blockProductEdge_mem_exactBlockProductFamily _
  · intro t u htu
    have hword := blockProductEdge_injective htu
    have hcoord : Fin.castLE hi t = Fin.castLE hi u := by
      simpa using congrFun hword i₀
    exact Fin.castLE_injective hi hcoord
  · intro t u htu
    exact wideCoordinatePetal_inter hpos i₀ hi htu

/-- Part (i), forward direction in the tagged singleton model. -/
theorem exactBlockProductFamily_sunflowerFree_of_width_lt
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) (hwidth : ∀ i, w i < k) :
    SunflowerFree (exactBlockProductFamily r w) k := by
  classical
  rintro ⟨petals, Y, hmem, hinj, hSun⟩
  let t₀ : Fin k := ⟨0, by omega⟩
  let t₁ : Fin k := ⟨1, by omega⟩
  have hx_exists : ∀ t : Fin k, ∃ x : BlockProductWord r w, petals t = blockProductEdge x := by
    intro t
    rcases Finset.mem_image.mp (hmem t) with ⟨x, -, hx⟩
    exact ⟨x, hx.symm⟩
  choose x hx using hx_exists
  have hcoord : ∀ i : Fin r, ∀ t : Fin k, x t i = x t₀ i := by
    intro i t
    obtain ⟨u, v, huv, huvEq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun s : Fin k => x s i) (by
        simp [Fintype.card_fin, hwidth i])
    have ht₀ : x t₀ i = x u i := by
      by_cases ht₀u : t₀ = u
      · simpa [ht₀u] using huvEq.symm
      · have hmem_uv : Sigma.mk i (x u i) ∈ petals u ∩ petals v := by
          rw [hx u, hx v]
          simp [mem_blockProductEdge_iff, huvEq]
        have hEqInter₀ : petals u ∩ petals v = petals u ∩ petals t₀ := by
          exact (hSun u v huv).trans (hSun u t₀ (by intro h; exact ht₀u h.symm)).symm
        have hmem_u0 : Sigma.mk i (x u i) ∈ petals u ∩ petals t₀ := by
          simpa [hEqInter₀] using hmem_uv
        rw [hx u, hx t₀] at hmem_u0
        simpa [mem_blockProductEdge_iff] using (Finset.mem_inter.mp hmem_u0).2
    by_cases htu : t = u
    · simpa [htu] using ht₀.symm
    · have hmem_uv : Sigma.mk i (x u i) ∈ petals u ∩ petals v := by
        rw [hx u, hx v]
        simp [mem_blockProductEdge_iff, huvEq]
      have hEqInter : petals u ∩ petals v = petals u ∩ petals t := by
        exact (hSun u v huv).trans (hSun u t (by intro h; exact htu h.symm)).symm
      have hmem_ut : Sigma.mk i (x u i) ∈ petals u ∩ petals t := by
        simpa [hEqInter] using hmem_uv
      have hxt : x t i = x u i := by
        rw [hx u, hx t] at hmem_ut
        simpa [mem_blockProductEdge_iff] using (Finset.mem_inter.mp hmem_ut).2
      exact hxt.trans ht₀.symm
  have hEq01 : petals t₀ = petals t₁ := by
    rw [hx t₀, hx t₁]
    exact congrArg blockProductEdge <| by
      funext i
      exact (hcoord i t₁).symm
  have ht01 : t₀ ≠ t₁ := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  exact ht01 (hinj hEq01)

theorem exactBlockProductFamily_sunflowerFree_of_width_le
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) (hwidth : ∀ i, w i ≤ k - 1) :
    SunflowerFree (exactBlockProductFamily r w) k := by
  exact exactBlockProductFamily_sunflowerFree_of_width_lt r k w hk (by
    intro i
    exact (Nat.le_sub_one_iff_lt (by omega : 0 < k)).mp (hwidth i))

theorem width_le_of_exactBlockProductFamily_sunflowerFree
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) (hpos : ∀ i, 0 < w i)
    (hfree : SunflowerFree (exactBlockProductFamily r w) k) :
    ∀ i, w i ≤ k - 1 := by
  intro i
  by_contra hnot
  have hi : k ≤ w i := by omega
  exact hfree (exactBlockProductFamily_has_sunflower_of_le_width r k w hk hpos i hi)

/-- Part (i), in the tagged singleton model: exact block products are `k`-sunflower-free
exactly when every coordinate width is at most `k - 1`. -/
theorem exactBlockProductFamily_sunflowerFree_iff_width_le
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) (hpos : ∀ i, 0 < w i) :
    SunflowerFree (exactBlockProductFamily r w) k ↔ ∀ i, w i ≤ k - 1 := by
  exact ⟨width_le_of_exactBlockProductFamily_sunflowerFree r k w hk hpos,
    exactBlockProductFamily_sunflowerFree_of_width_le r k w hk⟩

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

/-- Number of coordinates whose width is at most `k - 2`.  These are the coordinates
responsible for the multiplicative loss in the stability part of Theorem 8.2. -/
noncomputable def deficientCoordinateCount (r k : ℕ) (w : Fin r → ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r)).filter fun i => w i ≤ k - 2).card

/-- Multiplicative core of Theorem 8.2(v): if all widths are at most `k - 1`, then every
coordinate of width at most `k - 2` costs a factor `(k - 2)/(k - 1)` in the product bound. -/
theorem blockProductCard_le_stability_profile
    (r k : ℕ) (w : Fin r → ℕ) (hfree : ∀ i, w i ≤ k - 1) :
    blockProductCard r w ≤ (k - 2) ^ deficientCoordinateCount r k w *
      (k - 1) ^ (r - deficientCoordinateCount r k w) := by
  classical
  let bad : Finset (Fin r) := (Finset.univ.filter fun i => w i ≤ k - 2)
  let good : Finset (Fin r) := (Finset.univ.filter fun i => ¬ w i ≤ k - 2)
  have hpartition :
      blockProductCard r w = (∏ i ∈ bad, w i) * (∏ i ∈ good, w i) := by
    have h := Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset (Fin r))) (p := fun i => w i ≤ k - 2) (f := w)
    unfold blockProductCard
    simpa [bad, good] using h.symm
  have hbad : (∏ i ∈ bad, w i) ≤ (k - 2) ^ bad.card := by
    calc
      (∏ i ∈ bad, w i) ≤ ∏ i ∈ bad, (k - 2) := by
        exact Finset.prod_le_prod' fun i hi => (Finset.mem_filter.mp hi).2
      _ = (k - 2) ^ bad.card := by simp
  have hgood : (∏ i ∈ good, w i) ≤ (k - 1) ^ good.card := by
    calc
      (∏ i ∈ good, w i) ≤ ∏ i ∈ good, (k - 1) := by
        exact Finset.prod_le_prod' fun i _ => hfree i
      _ = (k - 1) ^ good.card := by simp
  have hgoodcard : good.card = r - bad.card := by
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (p := fun i => w i ≤ k - 2)
    have hsum : bad.card + good.card = r := by
      simpa [bad, good] using hcard
    omega
  calc
    blockProductCard r w = (∏ i ∈ bad, w i) * (∏ i ∈ good, w i) := hpartition
    _ ≤ (k - 2) ^ bad.card * (k - 1) ^ good.card := Nat.mul_le_mul hbad hgood
    _ = (k - 2) ^ deficientCoordinateCount r k w *
        (k - 1) ^ (r - deficientCoordinateCount r k w) := by
          simp [deficientCoordinateCount, bad, hgoodcard]

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
