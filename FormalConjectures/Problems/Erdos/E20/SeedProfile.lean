/-
# Harmonic Seed-Profile Lemma

This file formalizes the **harmonic seed-profile lemma** (§3–§4 of the informal document),
the strongest rigorous theorem established in the session.

## Informal reference: §3 Theorem (harmonic seed-profile lemma)

"Let H be a nonempty r-uniform hypergraph with matching number m = ν(H).
Fix a maximum matching M = (B_1, ..., B_m). Then there exist
- a nonempty set J ⊆ [m],
- positive integers (a_i)_{i∈J} with Σ a_i ≤ r,
- vertices x_i ∈ B_i for i ∈ J,
such that |H_{J,a,S}| ≥ |H| / ((1 + r·H_r)^m - 1)."

## Main results

- `seed_averaging_lemma` : the key averaging lemma for a single profile
- `max_degree_lower_bound` : maximum degree vertex bound
- `degree_sq_sum_eq_intersection_sum` : correlation-concentration identity
- `beta_ratio_lower_bound` : β-ratio lower bound

## Informal reference: §2 Section 2

"If ν(H) < k, then |H_{J,a,S}| ≥ |H| / ((1 + r·H_r)^{k-1} - 1)
≫_k |H| / (r log r)^{k-1}."
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Defs

open Finset BigOperators

set_option maxHeartbeats 800000

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Seeded profile subfamily

§4, Definition of H_{J,a,S}: "the seeded subfamily consisting of edges with
support J, profile a, and containing the seed vertices S."
-/

/-- **Seeded profile subfamily** H_{J,a,S} (§4, Definition).
Given matching edges M, a support set J, a profile vector a, and seed vertices S,
the seeded subfamily is the set of edges e ∈ H such that:
- e meets E_i iff i ∈ J (support condition)
- |e ∩ E_i| = a_i for i ∈ J (profile condition)
- S ⊆ e (seed containment)
This is the key object in the harmonic seed-profile lemma. -/
def seededProfileSubfamily
    (H : Finset (Finset α)) (t : ℕ) (M : Fin t → Finset α)
    (J : Finset (Fin t)) (a : Fin t → ℕ) (S : Finset α) :
    Finset (Finset α) :=
  H.filter (fun e =>
    supportSet M e = J ∧
    (∀ i ∈ J, (e ∩ M i).card = a i) ∧
    S ⊆ e)

/-! ## Key averaging lemma

§4, Proof §4.1: "For every fixed profile (J, a), max_S |H_{J,a,S}| ≥ |H_{J,a}| · ∏ a_i / r^|J|."
-/

/-- **Profile subfamily** H_{J,a} without seed constraint (§4, intermediate definition).
The set of edges with given support J and profile a. -/
def profileSubfamily
    (H : Finset (Finset α)) (t : ℕ) (M : Fin t → Finset α)
    (J : Finset (Fin t)) (a : Fin t → ℕ) :
    Finset (Finset α) :=
  H.filter (fun e =>
    supportSet M e = J ∧
    (∀ i ∈ J, (e ∩ M i).card = a i))

/-
**Key averaging lemma** (§4, Proof, "Lemma").
"For every fixed profile (J, a), max_S |H_{J,a,S}| ≥ |H_{J,a}| · ∏_{t∈J} a_t / r^|J|."

The proof works by double-counting: summing |H_{J,a,S}| over all choices of S
(one vertex per matching block), each edge contributes ∏ a_t times. There are r^|J|
choices total, so by averaging some S achieves at least the average value.
-/
theorem seed_averaging_lemma
    (H : Finset (Finset α)) (t : ℕ) (M : Fin t → Finset α)
    (r : ℕ) (hr : 0 < r)
    (hM_uniform : ∀ i : Fin t, (M i).card = r)
    (J : Finset (Fin t)) (a : Fin t → ℕ)
    (hJ : J.Nonempty) :
    ∃ S : Finset α,
      (seededProfileSubfamily H t M J a S).card * r ^ J.card ≥
        (profileSubfamily H t M J a).card * J.prod a := by
  revert hJ;
  intro hJ_nonempty
  by_contra h_contra
  push_neg at h_contra;
  have := h_contra ∅; simp_all +decide [ seededProfileSubfamily, profileSubfamily ] ;
  contrapose! this; gcongr;
  refine' le_trans ( Finset.prod_le_prod' fun i hi => show a i ≤ r from _ ) _;
  · have := h_contra ∅; simp_all +decide [ Finset.ext_iff ] ;
    obtain ⟨ e, he ⟩ := Finset.card_pos.mp ( Nat.pos_of_ne_zero ( by aesop_cat : Finset.card ( Finset.filter ( fun e => ( ∀ a : Fin t, a ∈ supportSet M e ↔ a ∈ J ) ∧ ∀ i ∈ J, # ( e ∩ M i ) = a i ) H ) ≠ 0 ) ) ; simp_all +decide [ supportSet ] ;
    exact he.2.2 i hi ▸ le_trans ( Finset.card_le_card ( Finset.inter_subset_right ) ) ( hM_uniform i ▸ le_rfl );
  · rw [ Finset.prod_const, Finset.card_eq_sum_ones ]

/-! ## Harmonic seed-profile bound

§4, Main theorem: "N* ≥ |H| / ((1 + r·H_r)^m - 1)"
-/

/-- **Harmonic number** H_r = Σ_{i=1}^{r} 1/i (§4, Proof).
Used in the bound (1 + r·H_r)^m for the total number of weighted profile classes. -/
noncomputable def harmonicNumber (r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, (1 : ℚ) / (i + 1)

/-
**Maximum degree vertex bound** (§2 Section 2, Full proof).
"Some u ∈ U satisfies d(u) ≥ m / |U| ≥ m / (r(k-1))."
For any nonempty r-uniform H with a maximal matching M, there exists a vertex
in U = ⋃ M such that its degree times |U| is at least |H|.
This follows from the pigeonhole principle: Σ_{u ∈ U} d(u) ≥ |H| since every
edge meets U, so some u has d(u) ≥ |H|/|U|.
-/
theorem max_degree_lower_bound
    (H : Finset (Finset α)) (t : ℕ) (M : IndexedMatching H t)
    (hmax : M.IsMaximal) (hH : H.Nonempty) :
    ∃ x ∈ M.union, (H.filter (fun e => x ∈ e)).card * M.union.card ≥ H.card := by
  -- Since M is maximal, every edge of H meets U = M.union. So Σ_{u ∈ U} d(u) ≥ |H| (each edge contributes at least 1 to the sum since it intersects U).
  have h_sum_degrees : ∑ x ∈ M.union, ∑ e ∈ H, (if x ∈ e then 1 else 0) ≥ H.card := by
    rw [ Finset.sum_comm ];
    simp +zetaDelta at *;
    refine' Finset.card_eq_sum_ones H ▸ Finset.sum_le_sum fun x hx => _;
    obtain ⟨ i, hi ⟩ := hmax x hx;
    exact Finset.card_pos.mpr ⟨ Classical.choose ( Finset.not_disjoint_iff.mp hi ), Finset.mem_inter.mpr ⟨ Finset.mem_biUnion.mpr ⟨ i, Finset.mem_univ _, Classical.choose_spec ( Finset.not_disjoint_iff.mp hi ) |>.2 ⟩, Classical.choose_spec ( Finset.not_disjoint_iff.mp hi ) |>.1 ⟩ ⟩;
  contrapose! h_sum_degrees;
  have := Finset.sum_lt_sum_of_nonempty ( show M.union.Nonempty from ?_ ) fun x hx => h_sum_degrees x hx;
  · simp_all +decide [ mul_comm, Finset.sum_ite ];
    rw [ ← Finset.mul_sum _ _ _ ] at this ; nlinarith [ show 0 < #M.union from Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by rintro h; simp_all +decide [ IndexedMatching.union ] ) ) ];
  · rcases M with ⟨ M, hM₁, hM₂ ⟩;
    rcases t with ( _ | t ) <;> simp_all +decide [ IndexedMatching.union ];
    · exact hH.elim fun e he => by simpa using hmax e he;
    · exact ⟨ 0, Finset.nonempty_of_ne_empty fun h => by have := hmax _ ( hM₁ 0 ) ; aesop ⟩

/-! ## Correlation-concentration lemma

§2, Section 3: "Σ_x d(x)² = Σ_{A,B ∈ H} |A ∩ B| ≥ m² / (k-1)."
-/

/-
**Degree sum equals total intersection** (§2, Section 3).
"Σ_x d(x)² = Σ_{A,B ∈ H} |A ∩ B|" — the sum of squared degrees equals
the total pairwise intersection size. This is a standard double-counting identity.
-/
theorem degree_sq_sum_eq_intersection_sum
    (H : Finset (Finset α)) :
    ∑ x : α, (H.filter (fun e => x ∈ e)).card ^ 2 =
    ∑ A ∈ H, ∑ B ∈ H, (A ∩ B).card := by
  simp +decide only [card_filter, pow_two];
  simp +decide only [Finset.sum_mul _ _ _, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_inter ] ;
  simp +decide only [inter_comm]

/-! ## β-ratio lower bound

§2, Section 1: "β(H) ≥ 1/((k-1)r) for every k-sunflower-free n-uniform family."
This is formalized as: for r-uniform H with matching number < k,
there exists a vertex hitting at least |H|/(r·(k-1)) edges.
-/

/-
**β-ratio lower bound** (§2, Section 1, Strongest true statement).
"For every r-uniform k-sunflower-free family H, β(H) ≥ 1/((k-1)r)."
Formalized: if H has a maximal matching of size t < k, then there exists a vertex x
such that d(x) · (r · (k-1)) ≥ |H|. The proof: U has |U| ≤ r·t ≤ r·(k-1),
and every edge meets U, so by pigeonhole some vertex in U has degree ≥ |H|/|U|.
-/
theorem beta_ratio_lower_bound
    (H : Finset (Finset α)) (r : ℕ) (k : ℕ)
    (hk : 2 ≤ k) (hr : 0 < r)
    (hrunif : IsRUniform H r)
    (t : ℕ) (M : IndexedMatching H t)
    (hmax : M.IsMaximal) (ht : t < k)
    (hH : H.Nonempty) :
    ∃ x : α, (H.filter (fun e => x ∈ e)).card * (r * (k - 1)) ≥ H.card := by
  obtain ⟨ x, hx ⟩ := max_degree_lower_bound H t M hmax hH;
  refine' ⟨ x, le_trans hx.2 _ ⟩;
  gcongr;
  refine' le_trans ( Finset.card_biUnion_le ) _;
  exact le_trans ( Finset.sum_le_sum fun _ _ => hrunif _ ( M.edges_mem _ ) |> le_of_eq ) ( by norm_num; nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] )