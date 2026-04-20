/-
# Canonical Support / Trace Decomposition Theorem

This file formalizes the canonical decomposition of an r-uniform hypergraph H
with ν(H) < k, as described in §1–§2 of the informal document.

## Main results

### Maximal matching cover (§2, first paragraph of the proof)
- `maximal_matching_every_edge_meets` : every edge meets the union of matching edges

### Part (A): Exact support partition (§1 Theorem (A), §2 Proof of (A))
- `supportClass_pairwise_disjoint` : support classes are pairwise disjoint
- `supportClass_cover` : every edge belongs to some support class
- `supportClass_is_support_bounded` : each H_I is a support-bounded-alphabet piece

### Part (B): Exact trace-cone refinement (§1 Theorem (B), §2 Proof of (B))
- `traceClass_pairwise_disjoint` : trace classes are pairwise disjoint
- `traceClass_cover` : every edge belongs to some trace class
- `traceClass_eq_conePiece` : each trace class is a cone piece

### Part (C): Optional profile refinement (§1 Theorem (C), §2 Proof of (C))
- `profileClass_pairwise_disjoint` : profile classes are pairwise disjoint
- `profileClass_cover` : every edge belongs to some profile class
-/
import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Defs

open Finset

set_option maxHeartbeats 800000

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Maximal matching cover

§2, first paragraph: "Because M is maximal, every edge of H meets U."
-/

/-- **Maximal matching covering property** (§2, first paragraph of the proof).
If M is a maximal matching in H, then every edge e ∈ H intersects at least one
matching edge. This is because if some edge e were disjoint from all matching edges,
then M ∪ {e} would be a larger matching, contradicting maximality. -/
theorem maximal_matching_every_edge_meets
    {H : Finset (Finset α)} {t : ℕ} (M : IndexedMatching H t)
    (hmax : M.IsMaximal) (e : Finset α) (he : e ∈ H) :
    ∃ i : Fin t, ¬Disjoint e (M.edges i) :=
  hmax e he

/-- **Maximal matching: every edge meets U** (§2, first paragraph).
Equivalent formulation: every edge has nonempty intersection with the union U. -/
theorem maximal_matching_inter_union_nonempty
    {H : Finset (Finset α)} {t : ℕ} (M : IndexedMatching H t)
    (hmax : M.IsMaximal) (e : Finset α) (he : e ∈ H) :
    (e ∩ M.union).Nonempty := by
  obtain ⟨i, hi⟩ := hmax e he
  rw [Finset.not_disjoint_iff] at hi
  obtain ⟨x, hxe, hxM⟩ := hi
  refine ⟨x, Finset.mem_inter.mpr ⟨hxe, ?_⟩⟩
  simp only [IndexedMatching.union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hxM⟩

/-! ## Part (A): Support partition

§1 Theorem (A) / §2 Proof of (A): "For each nonempty I ⊆ [t], define
H_I = {e ∈ H : e ∩ E_i ≠ ∅ ↔ i ∈ I}. Then H = ⊔_{∅≠I⊆[t]} H_I."
-/

/-
**Support classes are pairwise disjoint** (§2, Proof of (A)).
"These classes are pairwise disjoint" — two edges with different support sets
belong to different support classes.
-/
theorem supportClass_pairwise_disjoint
    (H : Finset (Finset α)) (M : Fin t → Finset α)
    (I J : Finset (Fin t)) (hIJ : I ≠ J) :
    Disjoint (supportClass H M I) (supportClass H M J) := by
  exact Finset.disjoint_filter.2 fun e _ heI heJ => hIJ <| heI.symm.trans heJ

/-- **Support class membership** (§2, Proof of (A)).
An edge e belongs to support class H_I if and only if e ∈ H and σ(e) = I. -/
theorem mem_supportClass_iff (H : Finset (Finset α)) (M : Fin t → Finset α)
    (I : Finset (Fin t)) (e : Finset α) :
    e ∈ supportClass H M I ↔ e ∈ H ∧ supportSet M e = I := by
  simp [supportClass, Finset.mem_filter]

/-- **Support classes cover H** (§2, Proof of (A)).
"Their union is all of H" — every edge of H belongs to exactly one support class,
namely the one indexed by its support set σ(e). -/
theorem supportClass_cover (H : Finset (Finset α)) (M : Fin t → Finset α)
    (e : Finset α) (he : e ∈ H) :
    e ∈ supportClass H M (supportSet M e) := by
  simp [supportClass, supportSet, he]

/-- **Support classes with nonempty support cover H under maximal matching** (§2, Proof of (A)).
Under a maximal matching, every edge has nonempty support, so the support classes
indexed by nonempty subsets of [t] cover all of H. -/
theorem supportSet_nonempty_of_maximal
    {H : Finset (Finset α)} {t : ℕ} (M : IndexedMatching H t)
    (hmax : M.IsMaximal) (e : Finset α) (he : e ∈ H) :
    (supportSet M.edges e).Nonempty := by
  obtain ⟨i, hi⟩ := hmax e he
  exact ⟨i, by simp [supportSet, hi]⟩

/-
**Support partition identity** (§1 Theorem (A), §2 Proof of (A)).
"H = ⊔_{∅≠I⊆[t]} H_I" — the union of all support classes recovers H.
-/
theorem biUnion_supportClasses_eq (H : Finset (Finset α)) (M : Fin t → Finset α) :
    (Finset.univ.image (fun e => supportSet M e)).biUnion
      (fun I => supportClass H M I) = H := by
  -- By definition of $supportClass$, every edge of $H$ is in some $supportClass H M I$. Hence, the union of these support classes covers all of $H$.
  ext e
  simp [supportClass]

/-
**Number of nonempty support classes** (§1 Theorem (A)).
"Hence H is partitioned into at most 2^t − 1 ≤ 2^{k−1} − 1 pieces."
The number of nonempty subsets of Fin t is 2^t - 1.
-/
theorem nonempty_subsets_card (t : ℕ) :
    ((Finset.univ : Finset (Finset (Fin t))).filter Finset.Nonempty).card = 2 ^ t - 1 := by
  convert Finset.card_filter ( fun x => ¬x = ∅ ) ( Finset.univ : Finset ( Finset ( Fin t ) ) ) using 2;
  · grind +locals;
  · rw [ Finset.sum_ite ];
    simp +decide [ Finset.filter_ne' ]

/-
**Each support class is a support-bounded-alphabet piece** (§1 Theorem (A), §2 Proof of (A)).
"Relative to the partition V(H) = E_1 ⊔ ⋯ ⊔ E_t ⊔ (V(H) \ U), every edge e ∈ H_I
meets E_i iff i ∈ I. This is exactly the definition of a support-bounded-alphabet piece."
-/
theorem supportClass_is_support_bounded
    (H : Finset (Finset α)) (M : Fin t → Finset α)
    (I : Finset (Fin t)) :
    IsSupportBoundedAlphabet (supportClass H M I) t M I := by
  intro e he i; simp_all +decide [ supportClass ] ;
  unfold supportSet at he; aesop;

/-! ## Part (B): Trace-cone refinement

§1 Theorem (B) / §2 Proof of (B): "For each nonempty S ⊆ U, define
H_S^= = {e ∈ H : e ∩ U = S}. Then H = ⊔_{∅≠S⊆U} H_S^=."
-/

/-
**Trace classes are pairwise disjoint** (§2, Proof of (B)).
Two edges with different traces belong to different trace classes.
-/
theorem traceClass_pairwise_disjoint
    (H : Finset (Finset α)) (U : Finset α) (S T : Finset α)
    (hST : S ≠ T) :
    Disjoint (traceClass H U S) (traceClass H U T) := by
  exact Finset.disjoint_filter.2 fun _ _ _ _ => hST <| by aesop;

/-- **Trace class membership** (§2, Proof of (B)).
An edge e belongs to trace class H_S^= if and only if e ∈ H and e ∩ U = S. -/
theorem mem_traceClass_iff (H : Finset (Finset α)) (U : Finset α)
    (S : Finset α) (e : Finset α) :
    e ∈ traceClass H U S ↔ e ∈ H ∧ e ∩ U = S := by
  simp [traceClass, Finset.mem_filter]

/-- **Trace classes cover H** (§2, Proof of (B)).
Every edge of H belongs to the trace class indexed by its trace e ∩ U. -/
theorem traceClass_cover (H : Finset (Finset α)) (U : Finset α)
    (e : Finset α) (he : e ∈ H) :
    e ∈ traceClass H U (e ∩ U) := by
  simp [traceClass, he]

/-- **Trace is nonempty under maximal matching** (§2, Proof of (B)).
Under a maximal matching, every edge has nonempty trace. -/
theorem edgeTrace_nonempty_of_maximal
    {H : Finset (Finset α)} {t : ℕ} (M : IndexedMatching H t)
    (hmax : M.IsMaximal) (e : Finset α) (he : e ∈ H) :
    (edgeTrace e M.union).Nonempty :=
  maximal_matching_inter_union_nonempty M hmax e he

/-
**Trace class is a cone** (§1 Theorem (B), §2 Proof of (B)).
"Every nonempty H_S^= is a cone: H_S^= = S * G_S" — every trace class is
a cone piece with core S. The petal family is {e \ U : e ∈ H_S^=}.
-/
theorem traceClass_eq_conePiece
    (H : Finset (Finset α)) (U : Finset α) (S : Finset α) (hS : S ⊆ U) :
    traceClass H U S =
      conePiece S ((traceClass H U S).image (· \ U)) := by
  ext e;
  constructor;
  · intro he;
    refine' Finset.mem_image.mpr ⟨ e \ U, _, _ ⟩ <;> simp_all +decide [ traceClass, conePiece ];
    · grind;
    · grind;
  · simp +contextual [ conePiece, traceClass ];
    intro x hx hx' hx''; subst hx'';
    simp +decide [ Finset.ext_iff ];
    exact ⟨ by convert hx using 1; ext a; by_cases ha : a ∈ U <;> aesop, fun a => by by_cases ha : a ∈ U <;> aesop ⟩

/-! ## Part (C): Profile refinement

§1 Theorem (C) / §2 Proof of (C): "For α = (α_1,...,α_t) with 1 ≤ Σα_i ≤ r,
define H_α = {e ∈ H : |e ∩ E_i| = α_i ∀ i}. Then H = ⊔_{α≠0} H_α."
-/

section ProfileRefinement

variable {β : Type*} [DecidableEq β]

/-
**Profile classes are pairwise disjoint** (§2, Proof of (C)).
Two edges with different profile vectors belong to different profile classes.
-/
theorem profileClass_pairwise_disjoint
    (H : Finset (Finset β)) (M : Fin t → Finset β)
    (p q : Fin t → ℕ) (hpq : p ≠ q) :
    Disjoint (profileClass H M p) (profileClass H M q) := by
  exact Finset.disjoint_filter.2 fun _ _ h₁ h₂ => hpq <| h₁.symm.trans h₂

/-- **Profile class membership** (§2, Proof of (C)).
An edge e belongs to profile class H_α iff e ∈ H and |e ∩ E_i| = α_i for all i. -/
theorem mem_profileClass_iff
    (H : Finset (Finset β)) (M : Fin t → Finset β)
    (p : Fin t → ℕ) (e : Finset β) :
    e ∈ profileClass H M p ↔ e ∈ H ∧ profileVec M e = p := by
  simp [profileClass, Finset.mem_filter]

/-- **Profile classes cover H** (§2, Proof of (C)).
"These classes cover H, because every edge determines a unique vector α." -/
theorem profileClass_cover
    (H : Finset (Finset β)) (M : Fin t → Finset β)
    (e : Finset β) (he : e ∈ H) :
    e ∈ profileClass H M (profileVec M e) := by
  simp [profileClass, he]

end ProfileRefinement

/-
**Profile refines support** (§2, Proof of (C)).
The profile class H_α is contained in the support class H_I where
I = {i : α_i > 0}. The profile partition refines the support partition.
-/
theorem profileClass_subset_supportClass
    (H : Finset (Finset α)) (M : Fin t → Finset α) (p : Fin t → ℕ) :
    profileClass H M p ⊆
      supportClass H M (Finset.univ.filter (fun i => 0 < p i)) := by
  intro e he
  rw [mem_profileClass_iff] at he
  obtain ⟨heH, heprofile⟩ := he
  rw [mem_supportClass_iff];
  simp +decide [ ← heprofile, supportSet ];
  simp +decide [ Finset.disjoint_left, profileVec ];
  simp +decide [ Finset.Nonempty, Finset.ext_iff ];
  exact heH