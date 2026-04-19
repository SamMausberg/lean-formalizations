import FormalConjectures.Problems.Erdos.E20.LeafStripping
import FormalConjectures.Problems.Erdos.E20.Counterexample
import FormalConjectures.Problems.Erdos.E20.TransversalCounterexample
import FormalConjectures.Problems.Erdos.E20.KernelBounds
import FormalConjectures.Problems.Erdos.E20.ExplicitKernels

namespace FormalConjectures.Problems.Erdos.E20

/-- Informal declaration "Theorem (exact one-round sunflower theorem)" from the pasted
leaf-stripping note:
this is the compiled nontrivial-cardinality form of the exact one-round theorem proved in
[LeafStripping.lean]
(/home/sam/lean-formalizations/FormalConjectures/Problems/Erdos/E20/LeafStripping.lean). -/
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

end FormalConjectures.Problems.Erdos.E20
