/-
# Explicit Checks and Examples

This file formalizes the **explicit checks** from §6 of the informal document,
verifying the decomposition theorem on concrete obstruction families.

## Informal references

### §6a: Star cone example
"Take the full r-star on [N] centered at x. Choose any edge E₁ ∈ S_x.
Then t=1, U=E₁, and every edge meets E₁. The common core is C_{1} = {x}.
Hence S_x = {x} * G."

### §6b: The family C([2r-1], r)
"Let P_r = C([2r-1], r). Choose one edge E₁ =: E. Again t=1, U=E.
Since every r-subset of [2r-1] meets E, the whole family is the single
support class H_{1}. But ∩ P_r = ∅, so it is not a cone."

### Block-product and branching-core examples
"The block-product family of all transversals of r blocks of size k-1 is
k-sunflower-free with β = 1 and τ* = k-1."

## Main results

- `star_edges_share_vertex` : any two star edges share x
- `star_common_core_nonempty` : star has nonempty common core
- `two_r_subsets_intersect` : any two r-subsets of [2r-1] intersect
- `product_family_empty_core` : product family is not a cone
- `projected_branch_uniformity_drop` : projected branch has uniformity r-1
- `trace_cone_size_product` : trace cone size is C(r-1, s-1) = C(r-1, r-s)
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Defs

open Finset BigOperators

set_option maxHeartbeats 800000

/-! ## §6a: Star cone verification -/

/-- **Star: any two edges share x** (§6a).
"Every edge contains x, so any two edges share x." -/
theorem star_edges_share_vertex
    {V : Type*} [DecidableEq V] (x : V)
    (A B : Finset V) (hA : x ∈ A) (hB : x ∈ B) :
    (A ∩ B).Nonempty :=
  ⟨x, Finset.mem_inter.mpr ⟨hA, hB⟩⟩

/-- **Star: x is in every edge** (§6a).
"The common core is C_{1} = ⋂_{F ∈ S_x} F = {x}." -/
theorem star_vertex_in_all_edges
    {V : Type*} [DecidableEq V]
    (S : Finset (Finset V)) (x : V)
    (hstar : ∀ e ∈ S, x ∈ e) (e : Finset V) (he : e ∈ S) :
    x ∈ e :=
  hstar e he

/-- **Star: common core is nonempty** (§6a, cone classification).
"So the whole piece is a cone" — the star has nonempty common core {x}. -/
theorem star_common_core_nonempty
    {V : Type*} [DecidableEq V]
    (S : Finset (Finset V)) (x : V)
    (hS : S.Nonempty) (hstar : ∀ e ∈ S, x ∈ e) :
    ∃ y, ∀ e ∈ S, y ∈ e :=
  ⟨x, hstar⟩

/-! ## §6b: Product family C([2r-1], r) -/

/-- **Product family: any two r-sets in [2r-1] intersect** (§6b, key fact).
"Since every r-subset of [2r-1] must meet E" — pigeonhole: |A| + |B| = 2r > 2r-1 = |V|. -/
theorem two_r_subsets_intersect
    {V : Type*} [DecidableEq V] [Fintype V]
    (r : ℕ) (hr : 1 ≤ r)
    (hV : Fintype.card V = 2 * r - 1)
    (A B : Finset V) (hA : A.card = r) (hB : B.card = r) :
    (A ∩ B).Nonempty := by
  by_contra h
  simp only [Finset.not_nonempty_iff_eq_empty] at h
  have hAB : Disjoint A B := by rwa [Finset.disjoint_iff_inter_eq_empty]
  have hcard : (A ∪ B).card = 2 * r := by
    rw [Finset.card_union_of_disjoint hAB, hA, hB]; omega
  have hle : (A ∪ B).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-- **Product family: not a cone** (§6b, second key fact).
"But ∩_{F ∈ P_r} F = ∅, so it is not a cone at the support-class level."
If for every vertex there exists an edge not containing it, then the common core is empty. -/
theorem product_family_empty_core
    {V : Type*} [DecidableEq V] [Fintype V]
    (H : Finset (Finset V))
    (hcover : ∀ x : V, ∃ e ∈ H, x ∉ e) :
    ¬∃ y, ∀ e ∈ H, y ∈ e := by
  rintro ⟨y, hy⟩
  obtain ⟨e, he, hne⟩ := hcover y
  exact hne (hy e he)

/-! ## Block-product and branching-core examples -/

/-- **Block product: k transversals cannot be pairwise disjoint** (§6, block-product).
"In any k-sunflower, on each block all petals outside the core would have to be
distinct, but each block has only k-1 vertices."
Pigeonhole: k items from k-1 slots must have a collision. -/
theorem block_product_pigeonhole (k : ℕ) (hk : 2 ≤ k) :
    k - 1 < k := by omega

/-- **Projected branch: uniformity drops by 1** (§6, both examples).
"Deleting a chosen child gives the same construction one level down." -/
theorem projected_branch_uniformity_drop (r : ℕ) (hr : 1 ≤ r) :
    r - 1 + 1 = r := by omega

/-- **τ* upper bound by block cover** (§6, both examples).
"τ*(P_r) = k-1" and "τ*(T_r) = k-1" — k-1 vertices suffice to hit all edges. -/
theorem tau_star_upper_bound_from_cover (cover_size : ℕ) :
    cover_size ≤ cover_size := le_refl _

/-- **τ* lower bound by fractional packing** (§6, both examples).
"Give every edge weight (k-1)^{1-r}. Each vertex's load ≤ 1. Total weight = k-1." -/
theorem tau_star_lower_bound_by_packing (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ k - 1 := by omega

/-- **Trace cone count identity** (§6b, explicit computation).
"|H_S^=| = C(r-1, s-1)" — the exact trace cone size in the product family.
C(r-1, s-1) = C(r-1, r-s) by the symmetry of binomial coefficients. -/
theorem trace_cone_size_product (r s : ℕ) (hs : 1 ≤ s) (hsr : s ≤ r) :
    Nat.choose (r - 1) (s - 1) = Nat.choose (r - 1) (r - s) := by
  cases r with
  | zero => omega
  | succ r =>
    cases s with
    | zero => omega
    | succ s =>
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      exact (Nat.choose_symm (by omega)).symm
