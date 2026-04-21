import FormalConjectures.Problems.Erdos.E20.Foundations
import FormalConjectures.Problems.Erdos.E20.Families
import FormalConjectures.Problems.Erdos.E20.Kernels
import FormalConjectures.Problems.Erdos.E20.Recurrences
import FormalConjectures.Problems.Erdos.E20.Tensors

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace FormalConjectures.Problems.Erdos.E20

/-- Informal declaration "Theorem (exact one-round sunflower theorem)" from the pasted
leaf-stripping note:
this is the compiled nontrivial-cardinality form of the exact one-round theorem proved in
[Kernels/LeafStripping.lean]
(/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E20/Kernels/LeafStripping.lean). -/
theorem pasted_exact_one_round_sunflower_theorem
    {α : Type*} [DecidableEq α] [Fintype α]
    (H : Finset (Finset α)) (K : Finset α) :
    (∀ U ⊆ H, 2 ≤ U.card → IsSunflowerWithKernel U K →
        U.card ≤ oneRoundSunflowerBound H K) ∧
      (2 ≤ oneRoundSunflowerBound H K →
        ∃ U ⊆ H, IsSunflowerWithKernel U K ∧ U.card = oneRoundSunflowerBound H K) :=
  exact_one_round_sunflower_theorem H K

/-- Informal declaration "Exact heavy-set lemma" from the pasted beta-chain note:
`M_t(F) ≥ |F| ∏_{i < t} β_i(F)`.  This is the already-formalized theorem
`heavy_set_betaPrefix_bound`, restated with a docstring matching the pasted statement. -/
theorem pasted_exact_heavy_set_lemma
    {α : Type*} [DecidableEq α] [Fintype α]
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    (H.card : ℚ) * betaPrefix H n t ≤ maxDegreeLevel H t :=
  heavy_set_betaPrefix_bound H hH hne ht

/-- Informal declaration "There is an actual heavy `t`-set attaining the heavy-set lower bound"
from the pasted beta-chain note.  This is the existing theorem `exists_heavy_set_betaPrefix`
with an explicit reference to that informal declaration. -/
theorem pasted_heavy_set_exists
    {α : Type*} [DecidableEq α] [Fintype α]
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    ∃ B ∈ levelSets t, (H.card : ℚ) * betaPrefix H n t ≤ setDegree H B :=
  exists_heavy_set_betaPrefix H hH hne ht

/-- Informal declaration "Local version inside a link" from the pasted beta-chain note:
after passing to a link `F_S`, the same heavy-set lower bound propagates with the shifted
prefix product. -/
theorem pasted_heavy_link_lemma
    {α : Type*} [DecidableEq α] [Fintype α]
    (H : Finset (Finset α)) {n r : ℕ} (S : Finset α)
    (hH : IsRUniform H n) (hdeg : 0 < setDegree H S) (hr : r ≤ n - S.card) :
    (setDegree H S : ℚ) * betaPrefix (linkFamily H S) (n - S.card) r ≤
      maxDegreeLevel (linkFamily H S) r :=
  heavy_link_betaPrefix_bound H S hH hdeg hr

/-- Informal declaration "Recursive upper bound for sunflower-free families" from the pasted
beta-chain note:
this is the formal quotient recursion obtained from a lower bound on the prefix product. -/
theorem pasted_beta_chain_recursive_bound
    {α : Type*} [DecidableEq α] [Fintype α]
    {g : ℕ → ℕ → ℕ} (hg : IsSunflowerSizeBound α g)
    (H : Finset (Finset α)) {n k t : ℕ} {b : ℚ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (hfree : SunflowerFree H k) (ht : t ≤ n)
    (hb : 0 < b) (hβ : b ≤ betaPrefix H n t) :
    (H.card : ℚ) ≤ (g (n - t) k : ℚ) / b :=
  sunflower_size_le_div_of_betaPrefix_lower hg H hH hne hfree ht hb hβ

/-- Informal declaration "Take the simplex family `H_r`" from the pasted 2-core counterexample
note: we formalize that family by reusing the complete-graph dual family on `r + 1` vertices. -/
def simplexFamily (r : ℕ) : Finset (Finset (Finset (Fin (r + 1)))) :=
  completeGraphDualFamily (r + 1)

/-- Informal declaration "each edge of `H_r` has size `r`" from the pasted 2-core
counterexample note. -/
theorem simplexFamily_uniform (r : ℕ) :
    IsRUniform (simplexFamily r) r := by
  simpa [simplexFamily] using completeGraphDualFamily_uniform (m := r + 1)

/-- Informal declaration "`H_r` is `k`-sunflower-free for every `k ≥ 3`" from the pasted
2-core counterexample note. -/
theorem simplexFamily_sunflowerFree (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k) :
    SunflowerFree (simplexFamily r) k := by
  have hm : 3 ≤ r + 1 := by omega
  simpa [simplexFamily] using completeGraphDualFamily_sunflowerFree (m := r + 1) (k := k) hm hk

/-- Informal declaration
"`∑_x d(x)^2 = 2 r (r + 1)` for the simplex family `H_r`" from the pasted 2-core
counterexample note. -/
theorem simplexFamily_degreeSquareSum (r : ℕ) (hr : 2 ≤ r) :
    degreeSquareSum (simplexFamily r) = 2 * (r + 1) * r := by
  have hm : 3 ≤ r + 1 := by omega
  simpa [simplexFamily, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    degreeSquareSum_completeGraphDualFamily (m := r + 1) hm

/-- Informal declaration
"the normalized ratio is exactly `2 / (r + 1)` for the simplex family `H_r`" from the pasted
2-core counterexample note. -/
theorem simplexFamily_normalized_ratio (r : ℕ) (hr : 2 ≤ r) :
    ((degreeSquareSum (simplexFamily r) : ℝ) /
        (((r : ℕ) : ℝ) * (simplexFamily r).card ^ 2)) =
      2 / (r + 1) := by
  have h3 : 3 ≤ r + 1 := by omega
  simpa [simplexFamily] using
    normalized_degreeSquareRatio_completeGraphDualFamily (m := r + 1) h3

/-- Informal declaration
"there is no positive constant `c_k` with `∑_x d(x)^2 ≥ c_k r |H|^2` even on the 2-core class"
from the pasted 2-core counterexample note.  This is the already-formalized complete-graph-dual
counterexample theorem, restated with the user’s phrasing. -/
theorem pasted_no_positive_two_core_branching_constant (k : ℕ) (hk : 3 ≤ k) :
    ∀ c : ℝ, 0 < c →
      ∃ m ≥ 3,
        let H := completeGraphDualFamily m
        SunflowerFree H k ∧
        IsRUniform H (m - 1) ∧
        ((degreeSquareSum H : ℝ) < c * (((m - 1 : ℕ) : ℝ)) * H.card ^ 2) :=
  no_positive_local_branching_constant k hk

/-- Informal declaration
"the parity slice has every bounded-order block marginal equal to the ambient product marginal"
from the pasted projected-branch obstruction note.  The existing theorem below records the
one-coordinate marginal computation that drives the parity-slice obstruction. -/
theorem pasted_parity_slice_coordinate_marginal
    {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]
    (n : ℕ) (p : Fin (n + 2)) (a : G) :
    coordinateMarginal (paritySlice (G := G) (r := n + 2)) p a =
      1 / Fintype.card G :=
  paritySlice_coordinateMarginal (G := G) n p a

/-- Informal declaration
"the parity slice gives the sharp transversal obstruction with `σ = 1 / |G|`" from the pasted
projected-branch obstruction note. -/
theorem pasted_parity_slice_sigma
    {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]
    (n : ℕ) :
    transversalSigma (paritySlice (G := G) (r := n + 2)) =
      1 / Fintype.card G :=
  paritySlice_transversalSigma (G := G) n

/-- Informal declaration
"every bounded prefix marginal of the parity slice is exactly uniform"
from the pasted projected-branch obstruction note. -/
theorem pasted_parity_slice_prefix_uniform
    {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]
    (s n : ℕ) (a : Fin s → G) :
    ((prefixFiber (G := G) s n 0 a).card : ℚ) /
        (paritySlice (G := G) (r := s + (n + 1))).card =
      1 / (Fintype.card G : ℚ) ^ s :=
  paritySlice_prefix_uniform (G := G) s n a

/-- Informal declaration
"if the alphabet has size `< k`, then every transversal family is automatically `k`-sunflower-free"
from the pasted projected-branch obstruction note. -/
theorem pasted_transversal_sunflower_free_below_alphabet_threshold
    {G : Type*} [DecidableEq G] [Fintype G]
    {r k : ℕ} (C : Finset (Fin r → G)) (hk : 2 ≤ k) (hG : Fintype.card G < k) :
    SunflowerFree (transversalFamily C) k :=
  transversalFamily_sunflowerFree_of_card_lt C hk hG

/-- Informal declaration
"the leafless block product `𝓑_{n,k}` has size `(k - 1)^n`"
from the pasted leafless-core note.  Formally we parameterize it by the block count `r`
and block width `q`. -/
theorem pasted_block_product_card
    (r q : ℕ) :
    (blockProductFamily r q).card = q ^ r :=
  card_blockProductFamily r q

/-- Informal declaration
"the block product on `r` blocks of width `q < k` is `k`-sunflower-free"
from the pasted leafless-core note. -/
theorem pasted_block_product_sunflower_free
    (r q k : ℕ) (hk : 2 ≤ k) (hqk : q < k) :
    SunflowerFree (blockProductFamily r q) k :=
  blockProductFamily_sunflowerFree r q k hk hqk

/-- Informal declaration
"for block width at least `2` and at least `2` blocks, leaf stripping fixes the block product"
from the pasted leafless-core note. -/
theorem pasted_block_product_stripping_fixed
    (r q : ℕ) (hr : 2 ≤ r) (hq : 2 ≤ q) :
    strippedSupportFamily (blockProductFamily r q) = blockProductFamily r q :=
  strippedSupport_blockProductFamily_eq r q hr hq

/-- Informal declaration
"the `K_k` tensor-product kernel on `t` rows has size `binom(k,2)^t`"
from the pasted terminal-kernel note. -/
theorem pasted_pair_tensor_card
    (t k : ℕ) :
    (pairTensorFamily t k).card = Nat.choose k 2 ^ t :=
  card_pairTensorFamily t k

/-- Informal declaration
"the `K_k` tensor-product kernel is `k`-sunflower-free"
from the pasted terminal-kernel note. -/
theorem pasted_pair_tensor_sunflower_free
    (t k : ℕ) (hk : 3 ≤ k) :
    SunflowerFree (pairTensorFamily t k) k :=
  pairTensorFamily_sunflowerFree t k hk

/-- Informal declaration
"the `K_k` tensor-product kernel is already terminal, so one stripping round leaves it unchanged"
from the pasted terminal-kernel note. -/
theorem pasted_pair_tensor_stripping_fixed
    (t k : ℕ) (hk : 3 ≤ k) :
    strippedSupportFamily (pairTensorFamily (t + 1) k) = pairTensorFamily (t + 1) k :=
  strippedSupport_pairTensorFamily_eq t k hk

/-- Informal declaration
"the `K_k` tensor-product kernel has no genuine one-out-of-`q` coordinate for any `q`"
from the pasted terminal-kernel note. -/
theorem pasted_pair_tensor_no_one_out_coordinate
    (t k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ Q, IsOneOutSet (pairTensorFamily (t + 1) k) Q :=
  pairTensorFamily_no_oneOutSet t k hk

/-- Informal declaration
"therefore `ρ_k(𝓗_t)=0`" from the pasted terminal-kernel note. -/
theorem pasted_pair_tensor_rho_zero
    (t k : ℕ) (hk : 3 ≤ k) :
    rhoOneOut (pairTensorFamily (t + 1) k) k = 0 :=
  rhoOneOut_pairTensorFamily_eq_zero t k hk

/-- Informal declaration from the pasted terminal-kernel reduction note:
the exact leaf-stripping reduction factor is packaged as the hypothesis that `H` is at most
`(k - 1)^n` times as large as its stripped terminal kernel. -/
abbrev pasted_terminal_kernel_reduction_hypothesis
    {α : Type*} [DecidableEq α] [Fintype α]
    (k n : ℕ) (H : Finset (Finset α)) : Prop :=
  HasTerminalKernelReductionAt k n H

/-- Informal declaration from the pasted terminal-kernel reduction note:
a class of exact terminal kernels carries the exponential base `A` when every `k`-sunflower-free
`m`-uniform member has size at most `A^m`. -/
abbrev pasted_terminal_kernel_class_bound
    {α : Type*} [DecidableEq α] [Fintype α]
    (C : Finset (Finset α) → Prop) (k : ℕ) (A : ℝ) : Prop :=
  HasTerminalKernelClassBound C k A

/-- Informal declaration from the pasted pruning note:
failure of hereditary faithfulness exactifies to a strict unresolved descendant. -/
theorem pasted_exact_support_pruning_exactify
    {Node : Type*} (C : ExactSupportPruningContext Node)
    {x : Node} (hx : C.Unresolved x) (hfaith : ¬ C.HereditarilyFaithful x) :
    ∃ y : Node, C.StrictDescendant y x ∧ C.Unresolved y :=
  C.exactify hx hfaith

/-- Informal declaration from the pasted pruning note:
a nonempty unresolved region contains a terminal unresolved node, and that node
is hereditarily faithful. -/
theorem pasted_exact_support_pruning_terminal_and_faithful
    {Node : Type*} (C : ExactSupportPruningContext Node)
    (h : ∃ x : Node, C.Unresolved x) :
    ∃ x : Node, C.Unresolved x ∧ C.Terminal x ∧ C.HereditarilyFaithful x :=
  C.exists_terminal_unresolved_and_faithful h

/-- Informal declaration from the pasted child-gluing note:
if every indexed child witness is solved, then the parent is solved. -/
theorem pasted_child_gluing_parent_solved
    {Parent Index : Type*} (C : Kernels.ChildGluingContext Parent Index)
    {p : Parent} (h : ∀ i : Index, C.ChildSolved p i) :
    C.ParentSolved p :=
  C.parent_solved_of_children h

/-- Informal declaration from the pasted terminal-kernel reduction note:
if the stripped terminal kernel has rank `m ≤ n`, satisfies the exact reduction factor, and has
size at most `A^m`, then `|H| ≤ ((k - 1) A)^n`. -/
theorem pasted_terminal_kernel_reduction
    {α : Type*} [DecidableEq α] [Fintype α]
    {H : Finset (Finset α)} {n m k : ℕ} {A : ℝ}
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hmn : m ≤ n) (hA : 1 ≤ A)
    (hKbound : ((strippedSupportFamily H).card : ℝ) ≤ A ^ m) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * A) ^ n) :=
  terminalKernelReduction_bound hk hred hmn hA hKbound

/-- Informal declaration from the pasted terminal-kernel reduction note:
the universal reduction lemma for a controlled class of exact terminal kernels. -/
theorem pasted_terminal_kernel_class_reduction
    {α : Type*} [DecidableEq α] [Fintype α]
    {H : Finset (Finset α)} {n m k : ℕ} {A : ℝ}
    {C : Finset (Finset α) → Prop}
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hclass : C (strippedSupportFamily H))
    (hKuniform : IsRUniform (strippedSupportFamily H) m)
    (hKfree : SunflowerFree (strippedSupportFamily H) k)
    (hmn : m ≤ n) (hA : 1 ≤ A)
    (hbound : HasTerminalKernelClassBound C k A) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * A) ^ n) :=
  terminalKernelReduction_bound_of_class hk hred hclass hKuniform hKfree hmn hA hbound

/-- Informal declaration from the pasted terminal-kernel reduction note:
if the stripped terminal kernel is a transversal code family of size at most `A^m`, then the same
reduction gives `|H| ≤ ((k - 1) A)^n`. -/
theorem pasted_terminal_transversal_kernel_reduction
    {G : Type*} [DecidableEq G] [Fintype G]
    {n m k : ℕ} {A : ℝ}
    (H : Finset (Finset (Fin m × G)))
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    {C : Finset (Fin m → G)}
    (hkernel : strippedSupportFamily H = transversalFamily (G := G) C)
    (hmn : m ≤ n) (hA : 1 ≤ A)
    (hCbound : (C.card : ℝ) ≤ A ^ m) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * A) ^ n) :=
  terminalKernelReduction_bound_of_transversalKernel H hk hred hkernel hmn hA hCbound

/-- Informal declaration from the pasted terminal-kernel reduction note:
if the stripped terminal kernel is the full block product on `m` blocks of width `q`, then the
exact reduction factor gives `|H| ≤ ((k - 1) q)^n`. -/
theorem pasted_terminal_block_product_kernel_reduction
    {n m q k : ℕ}
    (H : Finset (Finset (Fin m × Fin q)))
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hkernel : strippedSupportFamily H = blockProductFamily m q)
    (hmn : m ≤ n) (hq : 1 ≤ q) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * q) ^ n) :=
  terminalKernelReduction_bound_of_blockProductKernel H hk hred hkernel hmn hq

/-- Informal declaration from the pasted terminal-kernel reduction note:
in the block-product case with maximal allowed block width `k - 1`, the base becomes
`(k - 1)^(2n)`. -/
theorem pasted_terminal_block_product_square_bound
    {n m k : ℕ}
    (H : Finset (Finset (Fin m × Fin (k - 1))))
    (hk : 2 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hkernel : strippedSupportFamily H = blockProductFamily m (k - 1))
    (hmn : m ≤ n) :
    (H.card : ℝ) ≤ (k - 1 : ℝ) ^ (2 * n) :=
  terminalKernelReduction_bound_of_maxWidthBlockProductKernel H hk hred hkernel hmn

/-- Informal declaration
"if every edge of a kernel `J` meets at most `D` other edges, then `|J| ≤ (D + 1) ν(J)`"
from the pasted bounded-overlap note.

The formal theorem below is the finite witness version used in the current development:
one supplies an explicit maximal matching `M`, and the theorem bounds `|J|` by `(D + 1) |M|`. -/
theorem pasted_bounded_overlap_kernel_bound
    {α : Type*} [DecidableEq α]
    {J M : Finset (Finset α)} {D : ℕ}
    (hM : IsMaximalMatchingIn J M) (hD : MaxEdgeOverlapAtMost J D) :
    J.card ≤ (D + 1) * M.card :=
  card_le_overlap_bound_of_maximalMatching hM hD

/-- Informal declaration
"if `J` is `s`-uniform of maximum vertex degree `Δ`, then `|J| ≤ ((Δ - 1) s + 1) ν(J)`"
from the pasted bounded-degree note.

Again, the formal theorem is stated with an explicit maximal matching witness `M`. -/
theorem pasted_bounded_degree_kernel_bound
    {α : Type*} [DecidableEq α]
    {J M : Finset (Finset α)} {s Δ : ℕ}
    (huniform : IsRUniform J s) (hΔ : MaxVertexDegreeAtMost J Δ)
    (hM : IsMaximalMatchingIn J M) :
    J.card ≤ (s * (Δ - 1) + 1) * M.card :=
  card_le_vertexDegree_bound_of_maximalMatching huniform hΔ hM

/-- Informal declaration
"for a `k`-sunflower-free kernel, bounded degree forces a polynomial bound; in the finite witness
form, if a maximal matching has size at most `k - 1`, then `|J| ≤ (k - 1) ((Δ - 1) s + 1)`"
from the pasted bounded-degree note. -/
theorem pasted_small_matching_bounded_degree_kernel_bound
    {α : Type*} [DecidableEq α]
    {J M : Finset (Finset α)} {s Δ k : ℕ}
    (huniform : IsRUniform J s) (hΔ : MaxVertexDegreeAtMost J Δ)
    (hM : IsMaximalMatchingIn J M) (hMk : M.card ≤ k - 1) :
    J.card ≤ (k - 1) * (s * (Δ - 1) + 1) :=
  card_le_vertexDegree_bound_of_small_maximalMatching huniform hΔ hM hMk

/-- Informal declaration from the pasted terminal-kernel note:
"the family of minimal surviving witnesses" `𝓜(𝓚)`. -/
noncomputable abbrev pasted_minimal_surviving_witnesses
    {α : Type*} [DecidableEq α] [Fintype α]
    (Survives : Finset (Finset α) → Prop) (H : Finset (Finset α)) :
    Finset (Finset α) :=
  minimalSurvivingWitnesses Survives H

/-- Informal declaration from the pasted terminal-kernel note:
"the effective overlap degree" `Δ_eff(𝓚) = |𝓜(𝓚)|`. -/
noncomputable abbrev pasted_effective_overlap_degree
    {α : Type*} [DecidableEq α] [Fintype α]
    (Survives : Finset (Finset α) → Prop) (H : Finset (Finset α)) : ℕ :=
  effectiveOverlapDegree Survives H

/-- Informal declaration from the pasted terminal-kernel note:
once one has extracted a disjoint root/petal witness sunflower of bounded petal size, conditioning
on the root produces a bounded-alphabet block trace skeleton. -/
theorem pasted_bounded_alphabet_skeleton_from_witness_sunflower
    {α : Type*} [DecidableEq α] [Fintype α]
    (Survives : Finset (Finset α) → Prop)
    {H : Finset (Finset α)} {m s : ℕ}
    {D : WitnessSunflowerData Survives H m}
    (hsize : ∀ i, (D.petals i).card ≤ s) :
    ∃ A : Fin m → Finset (Finset α),
      (∀ i, (A i).card ≤ 2 ^ s) ∧
      ∀ w ∈ D.blockTrace, ∀ i, w i ∈ A i :=
  WitnessSunflowerData.exists_boundedAlphabetSkeleton hsize

/-- Informal declaration from the pasted projected-prefix note:
if a projected code has at most `B` visible patterns, then some projected pattern carries at least
an average-sized fiber.  This is the exact uniform counting version of the profitable-prefix
statement. -/
theorem pasted_projected_fiber_large
    {G : Type*} [DecidableEq G]
    {m s : ℕ} (C : Finset (Fin m → G)) (ι : Fin s → Fin m)
    (hC : C.Nonempty) {B : ℕ} (hB : (projectedCode C ι).card ≤ B) :
    ∃ u ∈ projectedCode C ι, C.card ≤ B * (projectedFiber C ι u).card :=
  exists_large_projectedFiber_of_card_bound C ι hC hB

/-- Informal declaration from the pasted projected-prefix / ambient-prefix transfer note:
after choosing one projected pattern, some refinement cell is large up to the exact refinement
count.  Formally this is expressed for arbitrary finite maps `p` and `q`. -/
theorem pasted_projection_refinement_transfer
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (p : α → β) (q : α → γ) (hS : S.Nonempty) {B : ℕ}
    (hB : (S.image p).card ≤ B) :
    ∃ b ∈ S.image p, ∃ c ∈ (fiberOver S p b).image q,
      S.card ≤ B * (((fiberOver S p b).image q).card * (fiberOver (fiberOver S p b) q c).card) :=
  exists_large_projected_then_refinedFiber S p q hS hB

/-- Informal declaration from the pasted support-piece recursion note:
for every fixed support piece `P`, a cross-sunflower exists in the parent tuple-state iff some
sunflower trace tuple on `P` has a child state containing a cross-sunflower. -/
theorem pasted_exact_trace_branch_decomposition
    {α : Type*} [DecidableEq α] {k : ℕ} (G : TupleState α k) (P : Finset α) :
    HasCrossSunflowerTuple G ↔
      ∃ T : Fin k → Finset α,
        IsSunflowerTuple T ∧ HasCrossSunflowerTuple (childState G P T) :=
  hasCrossSunflowerTuple_iff_exists_child P

/-- Informal declaration from the pasted profitable-prefix reduction note:
once a maximal-size function satisfies the exact profitable-drop recurrence, any constant
`C > A * Λ` yields the exponential bound `M(r) ≤ C^r`. -/
theorem pasted_profitable_drop_implies_exponential_bound
    (M : ℕ → ℝ) (A Λ C : ℝ) (T : ℕ)
    (hA : 1 ≤ A) (hΛ : 1 ≤ Λ) (hC : A * Λ < C)
    (hnonneg : ∀ r, 0 ≤ M r)
    (hbase : ∀ r, r ≤ T → M r ≤ C ^ r)
    (hrec : HasProfitableDropRecurrence M A Λ T) :
    ∀ r, M r ≤ C ^ r :=
  exponential_bound_of_hasProfitableDropRecurrence M A Λ C T hA hΛ hC hnonneg hbase hrec

/-- Informal declaration from the pasted parity-slice obstruction note:
if the target profitability base `Λ` is below the alphabet size, then every positive-length prefix
of the parity slice is too light to be `Λ`-profitable. -/
theorem pasted_parity_prefix_not_profitable
    {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]
    {s n Λ : ℕ} (hs : 0 < s) (hΛpos : 0 < Λ) (hΛ : Λ < Fintype.card G)
    (a : Fin s → G) :
    ¬ 1 / (Λ : ℚ) ^ s ≤
        ((prefixFiber (G := G) s n 0 a).card : ℚ) /
          (paritySlice (G := G) (r := s + (n + 1))).card :=
  paritySlice_prefix_not_profitable_of_nat_lt_card (G := G) hs hΛpos hΛ a

/-- Informal declaration from the pasted finite-state note:
the transfer-root candidate is the infimum over all superharmonic constants. -/
noncomputable abbrev pasted_transfer_root
    {Q E : Type*} [Fintype Q] [DecidableEq Q] [Fintype E] [DecidableEq E]
    (A : EdgeShift (Q := Q) (E := E)) : ℝ :=
  A.transferRoot

/-- Informal declaration from the pasted finite-state note:
the transfer matrix counts edges from each state to each next state. -/
noncomputable abbrev pasted_transfer_matrix
    {Q E : Type*} [Fintype Q] [DecidableEq Q] [Fintype E] [DecidableEq E]
    (A : EdgeShift (Q := Q) (E := E)) : Matrix Q Q ℝ :=
  A.transferMatrix

/-- Informal declaration from the pasted finite-state / sliding-window note:
every positive superharmonic weight produces a chain of prefixes whose normalized continuation
counts never drop below the starting value. -/
theorem pasted_finite_state_profitable_chain
    {Q E : Type*} [Fintype Q] [DecidableEq Q] [Fintype E] [DecidableEq E]
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hsuper : A.IsSuperharmonic h Λ) (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q)
    {n : ℕ} {s : Q} (hcount : 0 < A.continuationCount n s) :
    ∃ q : EdgeShift.StateChain Q n, ∃ e : EdgeShift.EdgeChain E n,
      q 0 = s ∧
      (∀ i : Fin n, e i ∈ A.outEdges (q i.castSucc) ∧ A.dst (e i) = q i.succ) ∧
      ∀ t : Fin (n + 1), A.phi h Λ (n - t) (q t) ≥ A.phi h Λ n s :=
  A.exists_phi_chain hsuper hΛ hh hcount

/-- Informal declaration from the pasted de Bruijn/sharpness note:
for the one-state `d`-regular system, the continuation count is exactly `d^n`. -/
theorem pasted_regular_one_state_count (d n : ℕ) :
    (regularOneState d).continuationCount n () = d ^ n :=
  continuationCount_regularOneState d n

/-- Informal declaration from the pasted finite-state / de Bruijn sharpness note:
for the one-state `d`-regular system, the transfer root is exactly `d`. -/
theorem pasted_regular_one_state_transfer_root (d : ℕ) :
    (regularOneState d).transferRoot = d :=
  transferRoot_regularOneState d

/-- Informal declaration from the pasted smallest-counterexample note:
in the two-state system `0 --a,b--> 1 --c--> 0`, the one-step prefix size is exactly one half of
the total two-step continuation count, so the naive unweighted critical-rate bound fails. -/
theorem pasted_two_state_half_prefix :
    (twoStateCounterexample.continuationCount 1 TwoState.one : ℝ) =
      (1 / 2 : ℝ) * twoStateCounterexample.continuationCount 2 TwoState.zero :=
  twoState_firstPrefix_is_half

/-- Informal declaration from the pasted smallest-counterexample note:
`1/2 < 1/√2`, i.e. the naive unweighted critical-rate lower bound fails in the two-state example. -/
theorem pasted_two_state_unweighted_failure :
    (1 / 2 : ℝ) < 1 / Real.sqrt 2 :=
  one_half_lt_inv_sqrt_two

/-- Informal declaration from the pasted automaton-branch note:
the exact prefix fiber over an admissible prefix is the continuation set from the reached state. -/
theorem pasted_automaton_prefix_fiber_card
    {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]
    (A : PartialDFA Q σ) {q r : Q} {t s : ℕ} {u : PartialDFA.Word σ t}
    (hru : A.run q u = some r) :
    (A.prefixFiber q t s u).card = A.continuationCount s r :=
  A.card_prefixFiber hru

/-- Informal declaration from the pasted automaton-branch note:
some length-`t` prefix already carries at least the `N_*(t)^{-1}` average fraction of the full
length-`t + s` branch. -/
theorem pasted_automaton_profitable_prefix
    {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]
    (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    ∃ u ∈ A.admissibleWords q t, ∃ r,
      A.run q u = some r ∧
      A.continuationCount (t + s) q ≤ A.NStar t * A.continuationCount s r :=
  A.exists_heavy_prefix hcount

/-- Informal declaration from the pasted automaton-branch note:
the profitable-prefix theorem in ratio form. -/
theorem pasted_automaton_profitable_prefix_ratio
    {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]
    (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    ∃ u ∈ A.admissibleWords q t,
      (1 : ℚ) / (A.NStar t : ℚ) ≤
        ((A.prefixFiber q t s u).card : ℚ) / (A.continuationCount (t + s) q : ℚ) :=
  A.exists_heavy_prefix_ratio hcount

/-- Informal declaration from the pasted automaton-branch note:
the packaged recurrence `h_A(m,k) ≤ N_*(t) h_A(m - t,k)`. -/
theorem pasted_automaton_branch_recurrence
    {Q σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]
    (A : PartialDFA Q σ) {m t k : ℕ} (ht : t ≤ m) :
    A.hA m k ≤ A.NStar t * A.hA (m - t) k :=
  A.hA_recurrence ht

/-- Informal declaration from the pasted hereditary projection-growth note:
the adaptive descendant-wise recurrence closes in one step. -/
theorem pasted_adaptive_projection_step
    {Q L : ℕ} {K : CodeClass Q}
    (hHered : Hereditary K) (hGrow : HasAdaptiveProjectionBound (Q := Q) (L := L) K) (n : ℕ) :
    maxSize K (n + 1) ≤ L * maxSize K n :=
  maxSize_succ_le_of_adaptiveProjectionBound (Q := Q) (L := L) hHered hGrow n

/-- Informal declaration from the pasted hereditary projection-growth note:
after descendant-wise reordering, the exact exponential base is `λ`. -/
theorem pasted_adaptive_projection_exponential_bound
    {Q L : ℕ} {K : CodeClass Q}
    (hHered : Hereditary K) (hGrow : HasAdaptiveProjectionBound (Q := Q) (L := L) K) :
    ∀ n, maxSize K n ≤ L ^ n :=
  maxSize_le_lambda_pow_of_adaptiveProjectionBound (Q := Q) (L := L) hHered hGrow

/-- Informal declaration from the pasted hereditary projection-growth note:
with the ambient order fixed, one good step contributes `λ` and the others contribute the trivial
alphabet factor `Q`. -/
theorem pasted_fixed_order_projection_step
    {Q L : ℕ} {K : CodeClass Q} {good : ℕ → Prop} [DecidablePred good]
    (hHered : Hereditary K) (hGood : HasFixedOrderProjectionBound (Q := Q) (L := L) K good)
    (n : ℕ) :
    maxSize K (n + 1) ≤ (if good n then L else Q) * maxSize K n :=
  maxSize_succ_le_of_fixedOrderProjectionBound
    (Q := Q) (L := L) (K := K) (good := good) hHered hGood n

/-- Informal declaration from the pasted hereditary projection-growth note:
closed form of the fixed-order recurrence. -/
theorem pasted_fixed_order_projection_closed_form
    {Q L : ℕ} {K : CodeClass Q} {good : ℕ → Prop} [DecidablePred good]
    (hHered : Hereditary K) (hGood : HasFixedOrderProjectionBound (Q := Q) (L := L) K good) :
    ∀ n, maxSize K n ≤ Q ^ (n - goodStepCount good n) * L ^ goodStepCount good n :=
  maxSize_le_of_fixedOrderProjectionBound
    (Q := Q) (L := L) (K := K) (good := good) hHered hGood

/-- Informal declaration from the pasted hereditary projection-growth note:
if at least `a m` of the first `b m` fixed-order steps are `λ`-good, then
`M(b m) ≤ (Q^(b-a) λ^a)^m`. -/
theorem pasted_fixed_order_density_block_bound
    {Q L : ℕ} {K : CodeClass Q} {good : ℕ → Prop} [DecidablePred good]
    (hHered : Hereditary K) (hGood : HasFixedOrderProjectionBound (Q := Q) (L := L) K good)
    (hLQ : L ≤ Q) {a b : ℕ} (hab : a ≤ b)
    (hdense : ∀ m, a * m ≤ goodStepCount good (b * m)) :
    ∀ m, maxSize K (b * m) ≤ (Q ^ (b - a) * L ^ a) ^ m :=
  maxSize_block_le_basePow_of_fixedOrderDensity
    (Q := Q) (L := L) (K := K) (good := good) hHered hGood hLQ hab hdense

/-- Informal declaration from the pasted fixed-memory note:
after choosing one forbidden length-`r` block, every proper `q`-ary `r`-step branch satisfies the
exact block recursion `|L_{n + r}| ≤ (q^r - 1) |L_n|`. -/
theorem pasted_fixed_memory_block_step
    {q r n : ℕ} (X : FixedMemoryBranch q r) :
    (X.language (n + r)).card ≤ (q ^ r - 1) * (X.language n).card :=
  X.card_language_add_le n

/-- Informal declaration from the pasted fixed-memory note:
iterating the one-block recursion gives the closed-form bound
`|L_n| ≤ q^(n mod r) (q^r - 1)^(n div r)`. -/
theorem pasted_fixed_memory_block_bound
    {q r n : ℕ} (X : FixedMemoryBranch q r) :
    (X.language n).card ≤ q ^ (n % r) * (q ^ r - 1) ^ (n / r) :=
  X.card_language_bound n

/-- Informal declaration from the pasted branch-bridge counterexample note:
the explicit terminal counterexample family has size `choose(k,2)^(n+1)`. -/
theorem pasted_branch_bridge_counterexample_card (n k : ℕ) :
    (branchBridgeFamily n k).card = Nat.choose k 2 ^ (n + 1) :=
  card_branchBridgeFamily n k

/-- Informal declaration from the pasted branch-bridge counterexample note:
the explicit counterexample family is `k`-sunflower-free. -/
theorem pasted_branch_bridge_counterexample_sunflower_free (n k : ℕ) (hk : 3 ≤ k) :
    SunflowerFree (branchBridgeFamily n k) k :=
  branchBridgeFamily_sunflowerFree n k hk

/-- Informal declaration from the pasted branch-bridge counterexample note:
the family is already terminal under one-round leaf stripping. -/
theorem pasted_branch_bridge_counterexample_terminal (n k : ℕ) (hk : 3 ≤ k) :
    strippedSupportFamily (branchBridgeFamily n k) = branchBridgeFamily n k :=
  strippedSupport_branchBridgeFamily_eq n k hk

/-- Informal declaration from the pasted branch-bridge counterexample note:
after any conditioning, a branch with at most `b` free bounded local coordinates has size at most
`choose(k,2)^b`. -/
theorem pasted_branch_bridge_bounded_local_branch
    {n k b : ℕ} (C : BranchBridgeConditioning n k) (free : Finset (Fin (n + 1)))
    (base : BranchBridgeWord n k) (hk : 3 ≤ k) (hfree : free.card ≤ b) :
    (boundedLocalCoordinateBranch C free base).card ≤ Nat.choose k 2 ^ b :=
  boundedLocalCoordinateBranch_card_le_of_free_card_le C free base hk hfree

/-- Informal declaration from the pasted `(4,4)` local-tensor note:
the explicit local tensor on `F_2^2` is exactly the indicator of the constant-or-injective
`4`-columns. -/
theorem pasted_local_character_tensor_exact_support (a b c d : V) :
    localCharacterTensor a b c d = localIndicator a b c d :=
  localCharacterTensor_eq_indicator a b c d

/-- Informal declaration from the pasted `(4,4)` local-tensor note:
the user's explicit `F_2`-valued local tensor
`δ(0, x₁ + x₂ + x₃ + x₄) ω(x₁ + x₂, x₁ + x₃) + δ(x₁, x₂) δ(x₁, x₃) δ(x₁, x₄)`
is exactly the indicator of the constant-or-injective `4`-columns. -/
theorem pasted_explicit_local_tensor_exact_support (a b c d : V) :
    explicitLocalTensor a b c d = localIndicatorF2 a b c d :=
  explicitLocalTensor_eq_indicatorF2 a b c d

/-- Informal declaration from the pasted `(4,4)` local-tensor note:
on a `4`-sunflower-free transversal code, the global tensor is diagonal on family tuples. -/
theorem pasted_global_tensor_diagonal_on_sunflower_free
    {n : ℕ} {C : Finset (TensorWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V) C) 4)
    {x : Fin 4 → TensorWord n} (hxC : ∀ t, x t ∈ C) :
    globalTensorTuple x = if ∀ t : Fin 4, x t = x 0 then 1 else 0 :=
  globalTensorTuple_eq_ite_allEqual_of_sunflowerFree hfree hxC

/-- Informal declaration from the pasted `(4,4)` local-tensor note:
for the explicit `F_2`-valued local tensor, the global product tensor is diagonal on tuples from a
`4`-sunflower-free transversal code. -/
theorem pasted_explicit_global_tensor_diagonal_on_sunflower_free
    {n : ℕ} {C : Finset (TensorWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V) C) 4)
    {x : Fin 4 → TensorWord n} (hxC : ∀ t, x t ∈ C) :
    explicitGlobalTensorTuple x = if ∀ t : Fin 4, x t = x 0 then 1 else 0 :=
  explicitGlobalTensorTuple_eq_ite_allEqual_of_sunflowerFree hfree hxC

/-- Informal declaration from the pasted `(4,4)` local-tensor note:
the explicit `2+2` flattening factors through `10^n` local mode choices, so its ordinary matrix
rank is at most `10^n`. -/
theorem pasted_global_character_matrix_rank_bound (n : ℕ) :
    (globalCharacterMatrix n).rank ≤ 10 ^ n :=
  rank_globalCharacterMatrix_le_ten_pow n

/-- Informal declaration from the pasted `(5,5)` diagonal-tensor note:
the explicit local tensor over `F_5` is exactly the indicator of the constant-or-injective
`5`-columns. -/
theorem pasted_quinary_local_tensor_exact_support (a b c d e : V5) :
    explicitLocalTensor5 a b c d e = localIndicator5 a b c d e :=
  explicitLocalTensor5_eq_indicator5 a b c d e

/-- Informal declaration from the pasted `(5,5)` diagonal-tensor note:
on a `5`-sunflower-free transversal code over `F_5`, the global product tensor is diagonal on
family tuples. -/
theorem pasted_quinary_global_tensor_diagonal_on_sunflower_free
    {n : ℕ} {C : Finset (QuinaryWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V5) C) 5)
    {x : Fin 5 → QuinaryWord n} (hxC : ∀ t, x t ∈ C) :
    explicitGlobalTensor5Tuple x = if ∀ t : Fin 5, x t = x 0 then 1 else 0 :=
  explicitGlobalTensor5Tuple_eq_ite_allEqual_of_sunflowerFree hfree hxC

end FormalConjectures.Problems.Erdos.E20
