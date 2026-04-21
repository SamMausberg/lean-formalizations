# Summary of changes for run cb6d35fb-9683-4dcf-a96a-56b06b1805a6

This summary was imported into
`FormalConjectures/Problems/Erdos/E20` from the archived Aristotle project.
References below to `RequestProject/...` are the original archive paths.

## Completed Formalization

I continued the formalization of the hypergraph decomposition theory document, significantly expanding the coverage from 5 files (~854 lines) to 9 files (~1374 lines). This imported summary predates later compendium additions; the current E20 tree still has visible `sorry` placeholders listed in `SORRY_INVENTORY.md`.

### Key improvements over the previous state

1. **Fixed `weighted_recurrence_abstract`** — The previous version was literally `True := trivial`. Replaced with `weighted_recurrence`, a real theorem stating that if level masses satisfy a covering condition (Σ m_j ≥ 1) and links satisfy size bounds, then the total family size satisfies the recurrence.

2. **Added 4 new files** with proper docstrings referencing the informal document:
   - **`Obstructions.lean`** (§3–§4): Star/cone classification, product family empty core, quantitative piece count (2^{k-1}-1), cone uniformity reduction, exponential-from-linear-recurrence theorem, balanced sparse structure.
   - **`Examples.lean`** (§6): Explicit verification on star cones, product family C([2r-1],r) (pigeonhole intersection proof), block-product/branching-core examples, trace cone size identity.
   - **`Correlation.lean`** (§2 Section 3): Vertex/set degree definitions, degree sum identity, correlation-concentration identity Σ d(x)² = Σ |A∩B|, Γ_t function.
   - **`GapAnalysis.lean`** (§4–§5): Core dichotomy, excess zero characterization, projected branch analysis, raw branch τ*=1 observation, linear recurrence → exponential bound, bounded β → exponential sunflower bound.

3. **Proved two non-trivial theorems** — The linear recurrence exponential bound (m(r) ≤ A·m(r-1) + P implies m(r) ≤ A^r·(m(0) + P/(A-1))) required careful induction with field_simp and nlinarith.

### File structure

- `RequestProject/Defs.lean` — Core definitions (133 lines)
- `RequestProject/Decomposition.lean` — Parts A, B, C of decomposition theorem (251 lines)
- `RequestProject/SeedProfile.lean` — Harmonic seed-profile lemma (186 lines)
- `RequestProject/Branching.lean` — Fractional branching theorem and recurrence (139 lines)
- `RequestProject/CoverCriteria.lean` — Fractional cover criterion and LP duality (135 lines)
- `RequestProject/Obstructions.lean` — Obstruction family classification (180 lines)
- `RequestProject/Examples.lean` — Explicit checks on star/product/block-product (134 lines)
- `RequestProject/Correlation.lean` — Correlation-concentration lemmas (74 lines)
- `RequestProject/GapAnalysis.lean` — Gap analysis and missing extensions (133 lines)
- `RequestProject/Main.lean` — Root import file (9 lines)

Every formal declaration has a docstring that explicitly references the corresponding informal declaration (section number, theorem name, or proof paragraph).

# Formalization of Hypergraph Decomposition Theory

## Overview

This project formalizes the mathematical content from the informal document about canonical decomposition of r-uniform hypergraphs with bounded matching number, including the sunflower conjecture framework, seed-profile lemmas, fractional branching theorems, and explicit verification on obstruction families.

## File Structure (9 files, ~1374 lines total)

### `RequestProject/Defs.lean` — Core definitions (133 lines)
Definitions with docstrings referencing the informal document:
- `IsRUniform`, `IndexedMatching`, `IndexedMatching.union`, `IndexedMatching.IsMaximal`
- `supportSet`, `supportClass`, `traceClass`, `profileClass`
- `conePiece`, `commonCore`
- `IsSupportBoundedAlphabet`, `profileExcess`, `matchingNumber`

### `RequestProject/Decomposition.lean` — Canonical decomposition theorem (251 lines)
Parts A, B, C of the decomposition theorem:
- `maximal_matching_every_edge_meets`, `maximal_matching_inter_union_nonempty`
- **Part A:** `supportClass_pairwise_disjoint`, `supportClass_cover`, `biUnion_supportClasses_eq`, `nonempty_subsets_card`, `supportClass_is_support_bounded`
- **Part B:** `traceClass_pairwise_disjoint`, `traceClass_cover`, `edgeTrace_nonempty_of_maximal`, `traceClass_eq_conePiece`
- **Part C:** `profileClass_pairwise_disjoint`, `profileClass_cover`, `profileClass_subset_supportClass`

### `RequestProject/SeedProfile.lean` — Harmonic seed-profile lemma (186 lines)
- `seededProfileSubfamily`, `profileSubfamily` — key subfamily definitions
- `seed_averaging_lemma` — the key averaging/double-counting lemma
- `harmonicNumber` — H_r = Σ 1/i
- `max_degree_lower_bound` — max degree bound via pigeonhole
- `degree_sq_sum_eq_intersection_sum` — correlation-concentration identity
- `beta_ratio_lower_bound` — β(H) ≥ 1/(r·(k-1))

### `RequestProject/Branching.lean` — Fractional branching theorem (139 lines)
- `weighted_recurrence` — the recurrence from weighted seed profiles
- `tau_star_bound` — τ* ≤ r(k-1) unconditionally
- `IsCGood`, `weak_duality_C_good` — C-good LP and weak duality
- `heavyLinkGenFun` — heavy-link generating function
- `exponential_bound_from_bounded_beta` — Σ B^j/j! ≤ e^B - 1
- `level_mass_factorial_bound` — B^j/j! ≤ B^j

### `RequestProject/CoverCriteria.lean` — Fractional cover criterion (135 lines)
- `fractional_cover_criterion` — if cheap cover exists, some block is heavy
- `dual_obstruction` — dual: no heavy block implies no cheap cover
- `general_weak_lp_duality` — general weak LP duality

### `RequestProject/Obstructions.lean` — Obstruction classification (180 lines)
- `starFamily`, `star_is_cone_piece` — star families are cone pieces (§3(i))
- `common_core_empty_of_covers_all` — product families have empty core (§3(ii))
- `quantitative_piece_count` — at most 2^{k-1}-1 pieces (§1 end)
- `zero_loss_decomposition` — zero loss property
- `cone_piece_reduces_uniformity`, `cone_uniformity_strictly_less` — uniformity reduction (§4)
- `exponential_from_linear_recurrence` — m(r) ≤ A·m(r-1)+P ⟹ m(r) ≤ A^r·(m(0)+P/(A-1))
- `IsBalancedSparse` — balanced sparse piece structure
- `cone_sparse_bound_constant` — 2^{k-1}-1 ≥ 1 for k ≥ 2

### `RequestProject/Examples.lean` — Explicit checks (134 lines)
- `star_edges_share_vertex`, `star_common_core_nonempty` — star verification (§6a)
- `two_r_subsets_intersect` — pigeonhole for [2r-1] (§6b)
- `product_family_empty_core` — product family is not a cone (§6b)
- `block_product_pigeonhole` — k transversals can't be disjoint
- `trace_cone_size_product` — C(r-1,s-1) = C(r-1,r-s) (§6b)

### `RequestProject/Correlation.lean` — Correlation-concentration (74 lines)
- `vertexDegree'`, `setDegree` — degree definitions
- `degree_sum_eq_card_sum` — Σ d(x) = Σ |e| (§2 Section 3)
- `degree_sq_sum_eq_intersection_sum'` — Σ d(x)² = Σ |A∩B| (§2 Section 3)
- `gammaLevel` — Γ_t function definition

### `RequestProject/GapAnalysis.lean` — Gap analysis (133 lines)
- `core_dichotomy` — cone/product-like case split (§4 end)
- `excess_zero_means_singletons` — e(a)=0 ↔ all entries 1 (§4)
- `projected_branch_uniformity` — projected branch has lower uniformity (§4)
- `raw_branch_tau_star_one` — raw branch τ*=1 (§4 gap analysis)
- `linear_recurrence_exponential` — linear recurrence → exponential bound (§5)
- `bounded_beta_gives_exponential` — bounded β → exponential bound (§5)
- `cone_sparse_base_constant`, `empty_core_hard_case_classification`

### `RequestProject/Main.lean` — Root import file (9 lines)

## Verification

The project builds cleanly. The current E20 tree is not globally sorry-free; see `SORRY_INVENTORY.md` for the remaining placeholders.
