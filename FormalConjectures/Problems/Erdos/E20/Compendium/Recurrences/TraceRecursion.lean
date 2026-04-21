import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Section 4: Support Pieces, Traces, and Exact Trace Recursion

This file formalizes the results from Section 4 of the sunflower compendium
(sunflower_compendium.pdf): "Support pieces, traces, and exact trace recursion."
-/

variable {α : Type} [DecidableEq α] [Fintype α]

/-
**Theorem 4.2 (Exact trace recursion), part 1: the exact identity.**
For every support piece `P` of rank `r` in an `m`-uniform family `G`:
  `|G| = ∑_{τ ∈ Tr_P(G)} |G_τ|`.

This is the fundamental trace decomposition identity: the family `G` partitions
exactly by its traces on `P`.
-/
theorem exact_trace_identity
    (G : Finset (Finset α)) (P : Finset α) (r m : ℕ)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r) :
    G.card = ∑ τ ∈ traceFamily G P, (projectedBranch G P τ).card := by
  rw [ @traceFamily ];
  rw [ Finset.card_eq_sum_ones, Finset.sum_image' ];
  intro A hA; rw [ projectedBranch ] ; simp +decide [ Finset.sum_filter ] ;
  rw [ Finset.card_image_of_injOn ];
  intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
  grind

/-
**Theorem 4.2, part 2: uniformity of projected branches.**
Each projected branch `G_τ` is `(m - r)`-uniform when `G` is `m`-uniform
and `P` is a support piece of rank `r`.
-/
theorem projected_branch_uniform
    (G : Finset (Finset α)) (P : Finset α) (r m : ℕ) (τ : Finset α)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r) (hτ : τ ∈ traceFamily G P) :
    IsUniform (projectedBranch G P τ) (m - r) := by
  intro A' hA';
  obtain ⟨ A, hA, hA' ⟩ := Finset.mem_image.mp hA';
  have := huni A ( Finset.filter_subset _ _ hA );
  have := hsp.2 A ( Finset.filter_subset _ _ hA );
  grind

/-
**Theorem 4.2, part 3: sunflower-freeness of projected branches.**
If `G` is `k`-sunflower-free, then each projected branch `G_τ` is also `k`-sunflower-free.
-/
theorem projected_branch_sunflower_free
    (G : Finset (Finset α)) (P : Finset α) (k : ℕ) (τ : Finset α)
    (hfree : SunflowerFree G k) :
    SunflowerFree (projectedBranch G P τ) k := by
  intro h;
  -- If G_τ contained a k-sunflower with petals A'_1, ..., A'_k having common intersection Y, then for each i there is A_i ∈ G with A_i ∩ P = τ and A'_i = A_i \ P.
  obtain ⟨petals, Y, hpetals, hinjective, hcommon⟩ := h;
  obtain ⟨A, hA⟩ : ∃ A : Fin k → Finset α, (∀ i, A i ∈ G) ∧ (∀ i, A i ∩ P = τ) ∧ (∀ i, petals i = A i \ P) := by
    choose A hA₁ hA₂ using fun i => Finset.mem_image.mp ( hpetals i );
    exact ⟨ A, fun i => Finset.mem_filter.mp ( hA₁ i ) |>.1, fun i => Finset.mem_filter.mp ( hA₁ i ) |>.2, fun i => hA₂ i ▸ rfl ⟩;
  refine' hfree ⟨ A, Y ∪ τ, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  · intro i j hij; have := @hinjective i j; simp_all +decide [ Finset.ext_iff ] ;
  · grind

/-- **Theorem 4.2, consequence: trace recursion bound.**
If `G` is `m`-uniform and `k`-sunflower-free, and `P` is a support piece of rank `r`
with `Tr_P(G)` itself `k`-sunflower-free, then
  `|G| ≤ |Tr_P(G)| · f(m - r, k) ≤ f(r, k) · f(m - r, k)`.

We formalize the first inequality. -/
theorem trace_recursion_bound
    (G : Finset (Finset α)) (P : Finset α) (r m k : ℕ)
    (huni : IsUniform G m) (hsp : IsSupportPiece G P r)
    (hfree : SunflowerFree G k)
    (htrace_free : SunflowerFree (traceFamily G P) k)
    (hsup : BddAbove {c : ℕ | ∃ (β : Type) (_ : DecidableEq β) (_ : Fintype β)
      (F : Finset (Finset β)), IsUniform F (m - r) ∧ SunflowerFree F k ∧ F.card = c}) :
    G.card ≤ (traceFamily G P).card * sunflowerThreshold (m - r) k := by
  have branch_bound : ∀ τ ∈ traceFamily G P,
      (projectedBranch G P τ).card ≤ sunflowerThreshold (m - r) k := by
    intro τ hτ
    have hbranch_uni : IsUniform (projectedBranch G P τ) (m - r) :=
      projected_branch_uniform G P r m τ huni hsp hτ
    have hbranch_free : SunflowerFree (projectedBranch G P τ) k :=
      projected_branch_sunflower_free G P k τ hfree
    have hbranch_card :
        (projectedBranch G P τ).card ≤ sunflowerNumber (m - r) k := by
      unfold sunflowerNumber
      exact le_csSup hsup
        ⟨α, inferInstance, inferInstance, projectedBranch G P τ,
          hbranch_uni, hbranch_free, rfl⟩
    exact le_trans hbranch_card (Nat.le_succ _)
  have hsum :
      (∑ τ ∈ traceFamily G P, (projectedBranch G P τ).card) ≤
        (traceFamily G P).card * sunflowerThreshold (m - r) k := by
    simpa [Nat.mul_comm] using Finset.sum_le_sum branch_bound
  exact (exact_trace_identity G P r m huni hsp).trans_le hsum

/-! ## Proposition 4.3: one-block universality -/

section OneBlockUniversality

/-- Vertex type for the one-block universality construction.

The left summand is the matching edge `A`: it contains a copy of the ambient type `α`
and enough dummy vertices to have size `n`.  The right summand contains the private padding,
keyed by the trace edge `B ∈ H`. -/
abbrev OneBlockVertex (H : Finset (Finset α)) (n r : ℕ) :=
  Sum (Sum α (Fin (n - Fintype.card α))) ({B : Finset α // B ∈ H} × Fin (n - r))

namespace OneBlock

variable (H : Finset (Finset α)) (n r : ℕ)

noncomputable def ambient : Finset (OneBlockVertex H n r) :=
  Finset.univ.image Sum.inl

noncomputable def traceCopy (B : Finset α) : Finset (OneBlockVertex H n r) :=
  B.image fun a => Sum.inl (Sum.inl a)

noncomputable def privateCopy (B : {B : Finset α // B ∈ H}) :
    Finset (OneBlockVertex H n r) :=
  Finset.univ.image fun p : Fin (n - r) => Sum.inr (B, p)

noncomputable def liftedEdge (B : {B : Finset α // B ∈ H}) :
    Finset (OneBlockVertex H n r) :=
  traceCopy H n r B.1 ∪ privateCopy H n r B

noncomputable def liftedPiece : Finset (Finset (OneBlockVertex H n r)) :=
  H.attach.image (liftedEdge H n r)

noncomputable def family : Finset (Finset (OneBlockVertex H n r)) :=
  insert (ambient H n r) (liftedPiece H n r)

theorem card_ambient (hnα : Fintype.card α ≤ n) :
    (ambient H n r).card = n := by
  unfold ambient
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_sum, Nat.add_sub_of_le hnα]
  · intro x y hxy
    simpa using hxy

theorem card_traceCopy (B : Finset α) :
    (traceCopy H n r B).card = B.card := by
  unfold traceCopy
  rw [Finset.card_image_of_injective]
  intro x y hxy
  simpa using hxy

theorem card_privateCopy (B : {B : Finset α // B ∈ H}) :
    (privateCopy H n r B).card = n - r := by
  unfold privateCopy
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    simpa using hxy

theorem disjoint_trace_private (B : {B : Finset α // B ∈ H}) :
    Disjoint (traceCopy H n r B.1) (privateCopy H n r B) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
  rcases Finset.mem_image.mp hx' with ⟨p, _hp, h⟩
  cases h

theorem card_liftedEdge (hnr : r ≤ n) (hr : IsUniform H r)
    (B : {B : Finset α // B ∈ H}) :
    (liftedEdge H n r B).card = n := by
  unfold liftedEdge
  rw [Finset.card_union_of_disjoint (disjoint_trace_private H n r B)]
  rw [card_traceCopy, card_privateCopy, hr B.1 B.2]
  exact Nat.add_sub_of_le hnr

theorem traceCopy_subset_ambient (B : Finset α) :
    traceCopy H n r B ⊆ ambient H n r := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
  exact Finset.mem_image.mpr ⟨Sum.inl a, by simp, rfl⟩

theorem private_disjoint_ambient (B : {B : Finset α // B ∈ H}) :
    Disjoint (privateCopy H n r B) (ambient H n r) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rcases Finset.mem_image.mp hx with ⟨p, _hp, rfl⟩
  rcases Finset.mem_image.mp hx' with ⟨a, _ha, h⟩
  cases h

theorem liftedEdge_inter_ambient (B : {B : Finset α // B ∈ H}) :
    liftedEdge H n r B ∩ ambient H n r = traceCopy H n r B.1 := by
  unfold liftedEdge
  rw [Finset.union_inter_distrib_right]
  rw [Finset.inter_eq_left.mpr (traceCopy_subset_ambient H n r B.1)]
  have hdisj := private_disjoint_ambient H n r B
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
  simp

theorem liftedEdge_mem_liftedPiece (B : {B : Finset α // B ∈ H}) :
    liftedEdge H n r B ∈ liftedPiece H n r := by
  exact Finset.mem_image.mpr ⟨B, by simp, rfl⟩

theorem mem_liftedPiece_iff {E : Finset (OneBlockVertex H n r)} :
    E ∈ liftedPiece H n r ↔ ∃ B : {B : Finset α // B ∈ H}, liftedEdge H n r B = E := by
  constructor
  · intro hE
    rcases Finset.mem_image.mp hE with ⟨B, _hB, rfl⟩
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact liftedEdge_mem_liftedPiece H n r B

theorem traceFamily_liftedPiece :
    traceFamily (liftedPiece H n r) (ambient H n r) =
      H.image (traceCopy H n r) := by
  ext T
  constructor
  · intro hT
    rcases Finset.mem_image.mp hT with ⟨E, hE, rfl⟩
    rcases (mem_liftedPiece_iff (H := H) (n := n) (r := r)).mp hE with ⟨B, rfl⟩
    rw [liftedEdge_inter_ambient]
    exact Finset.mem_image.mpr ⟨B.1, B.2, rfl⟩
  · intro hT
    rcases Finset.mem_image.mp hT with ⟨B, hB, rfl⟩
    let B' : {B : Finset α // B ∈ H} := ⟨B, hB⟩
    exact Finset.mem_image.mpr
      ⟨liftedEdge H n r B', liftedEdge_mem_liftedPiece H n r B', by
        rw [liftedEdge_inter_ambient]⟩

theorem traceCopy_injective : Function.Injective (traceCopy H n r) := by
  intro B C hBC
  ext a
  constructor <;> intro ha
  · have : Sum.inl (Sum.inl a) ∈ traceCopy H n r C := by
      rw [← hBC]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    simpa [traceCopy] using this
  · have : Sum.inl (Sum.inl a) ∈ traceCopy H n r B := by
      rw [hBC]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    simpa [traceCopy] using this

theorem liftedEdge_injective : Function.Injective (liftedEdge H n r) := by
  intro B C hBC
  have htrace :
      traceCopy H n r B.1 = traceCopy H n r C.1 := by
    calc
      traceCopy H n r B.1 = liftedEdge H n r B ∩ ambient H n r := by
        rw [liftedEdge_inter_ambient]
      _ = liftedEdge H n r C ∩ ambient H n r := by rw [hBC]
      _ = traceCopy H n r C.1 := by rw [liftedEdge_inter_ambient]
  apply Subtype.ext
  exact traceCopy_injective H n r htrace

theorem liftedEdge_inter_liftedEdge_of_ne
    {B C : {B : Finset α // B ∈ H}} (hne : B ≠ C) :
    liftedEdge H n r B ∩ liftedEdge H n r C =
      traceCopy H n r (B.1 ∩ C.1) := by
  ext x
  rcases x with x | x
  · rcases x with a | p
    · simp [liftedEdge, traceCopy, privateCopy]
    · simp [liftedEdge, traceCopy, privateCopy]
  · rcases x with ⟨D, p⟩
    by_cases hDB : D = B
    · by_cases hDC : D = C
      · subst D
        exact False.elim (hne hDC)
      · have hCB : C ≠ B := by
          intro hCB
          exact hDC (by rw [hDB, ← hCB])
        simp [liftedEdge, traceCopy, privateCopy, hDB, hCB]
    · by_cases hDC : D = C
      · have hBC : B ≠ C := by
          intro hBC
          exact hDB (by rw [hDC, ← hBC])
        simp [liftedEdge, traceCopy, privateCopy, hBC, hDC]
      · have hBD : B ≠ D := by
          intro hBD
          exact hDB hBD.symm
        have hCD : C ≠ D := by
          intro hCD
          exact hDC hCD.symm
        simp [liftedEdge, traceCopy, privateCopy, hBD, hCD]

theorem exists_two_ne_of_three_le {k : ℕ} (hk : 3 ≤ k) (i : Fin k) :
    ∃ j l : Fin k, j ≠ i ∧ l ≠ i ∧ j ≠ l := by
  have hcard : 2 ≤ (Finset.univ.erase i).card := by
    simp [Fintype.card_fin]
    omega
  have hnonempty : (Finset.univ.erase i).Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  rcases hnonempty with ⟨j, hj⟩
  have hj_ne_i : j ≠ i := by
    exact (Finset.mem_erase.mp hj).1
  have hcard2 : 0 < ((Finset.univ.erase i).erase j).card := by
    have hjmem : j ∈ Finset.univ.erase i := hj
    rw [Finset.card_erase_of_mem hjmem]
    omega
  rcases Finset.card_pos.mp hcard2 with ⟨l, hl⟩
  have hl₁ := Finset.mem_erase.mp hl
  have hl₂ := Finset.mem_erase.mp hl₁.2
  exact ⟨j, l, hj_ne_i, hl₂.1, by exact Ne.symm hl₁.1⟩

theorem family_sunflowerFree (k : ℕ) (hk : 3 ≤ k) (hfree : SunflowerFree H k) :
    SunflowerFree (family H n r) k := by
  intro hSun
  rcases hSun with ⟨petals, Y, hpetals_mem, hinj, hpair⟩
  by_cases hA : ∃ i : Fin k, petals i = ambient H n r
  · rcases hA with ⟨i, hiA⟩
    rcases exists_two_ne_of_three_le hk i with ⟨j, l, hji, hli, hjl⟩
    have hj_ne_A : petals j ≠ ambient H n r := by
      intro h
      exact hji (hinj (h.trans hiA.symm))
    have hl_ne_A : petals l ≠ ambient H n r := by
      intro h
      exact hli (hinj (h.trans hiA.symm))
    have hjG : petals j ∈ liftedPiece H n r := by
      have := hpetals_mem j
      simp [family, hj_ne_A] at this
      exact this
    have hlG : petals l ∈ liftedPiece H n r := by
      have := hpetals_mem l
      simp [family, hl_ne_A] at this
      exact this
    rcases (mem_liftedPiece_iff (H := H) (n := n) (r := r)).mp hjG with ⟨Bj, hBj⟩
    rcases (mem_liftedPiece_iff (H := H) (n := n) (r := r)).mp hlG with ⟨Bl, hBl⟩
    have htracej :
        traceCopy H n r Bj.1 = Y := by
      calc
        traceCopy H n r Bj.1 = liftedEdge H n r Bj ∩ ambient H n r := by
          rw [liftedEdge_inter_ambient]
        _ = petals j ∩ petals i := by rw [hBj, hiA]
        _ = Y := hpair j i hji
    have htracel :
        traceCopy H n r Bl.1 = Y := by
      calc
        traceCopy H n r Bl.1 = liftedEdge H n r Bl ∩ ambient H n r := by
          rw [liftedEdge_inter_ambient]
        _ = petals l ∩ petals i := by rw [hBl, hiA]
        _ = Y := hpair l i hli
    have hBjl : Bj = Bl := by
      apply Subtype.ext
      exact traceCopy_injective H n r (htracej.trans htracel.symm)
    have hp_eq : petals j = petals l := by
      rw [← hBj, ← hBl, hBjl]
    exact hjl (hinj hp_eq)
  · have hGmem : ∀ i : Fin k, petals i ∈ liftedPiece H n r := by
      intro i
      have hmem := hpetals_mem i
      have hne : petals i ≠ ambient H n r := by
        intro hi
        exact hA ⟨i, hi⟩
      simp [family, hne] at hmem
      exact hmem
    choose B hB using fun i => (mem_liftedPiece_iff (H := H) (n := n) (r := r)).mp (hGmem i)
    have hBmem : ∀ i, (B i).1 ∈ H := fun i => (B i).2
    have hBinj : Function.Injective (fun i : Fin k => (B i).1) := by
      intro i j hij
      have hsub : B i = B j := Subtype.ext hij
      apply hinj
      calc
        petals i = liftedEdge H n r (B i) := (hB i).symm
        _ = liftedEdge H n r (B j) := by rw [hsub]
        _ = petals j := hB j
    let z : Fin k := ⟨0, by omega⟩
    let o : Fin k := ⟨1, by omega⟩
    have hzo : z ≠ o := by
      intro h
      have hv := congrArg Fin.val h
      simp [z, o] at hv
    apply hfree
    refine ⟨fun i => (B i).1, (B z).1 ∩ (B o).1, hBmem, hBinj, ?_⟩
    intro i j hij
    have hBij : B i ≠ B j := by
      intro h
      exact hij (hBinj (Subtype.ext_iff.mp h))
    have hBzo : B z ≠ B o := by
      intro h
      have h01 : z = o :=
        hBinj (Subtype.ext_iff.mp h)
      exact hzo h01
    have hinter_ij :
        traceCopy H n r ((B i).1 ∩ (B j).1) = Y := by
      calc
        traceCopy H n r ((B i).1 ∩ (B j).1)
            = liftedEdge H n r (B i) ∩ liftedEdge H n r (B j) :=
                (liftedEdge_inter_liftedEdge_of_ne (H := H) (n := n) (r := r) hBij).symm
        _ = petals i ∩ petals j := by rw [hB i, hB j]
        _ = Y := hpair i j hij
    have hinter_zo :
        traceCopy H n r ((B z).1 ∩ (B o).1) = Y := by
      calc
        traceCopy H n r ((B z).1 ∩ (B o).1)
            = liftedEdge H n r (B z) ∩ liftedEdge H n r (B o) :=
                (liftedEdge_inter_liftedEdge_of_ne (H := H) (n := n) (r := r) hBzo).symm
        _ = petals z ∩ petals o := by rw [hB z, hB o]
        _ = Y := hpair z o hzo
    exact traceCopy_injective H n r (hinter_ij.trans hinter_zo.symm)

theorem family_uniform (hnα : Fintype.card α ≤ n) (hnr : r ≤ n) (hr : IsUniform H r) :
    IsUniform (family H n r) n := by
  intro E hE
  by_cases hEA : E = ambient H n r
  · rw [hEA]
    exact card_ambient H n r hnα
  · have hG : E ∈ liftedPiece H n r := by
      simpa [family, hEA] using hE
    rcases (mem_liftedPiece_iff (H := H) (n := n) (r := r)).mp hG with ⟨B, rfl⟩
    exact card_liftedEdge H n r hnr hr B

theorem liftedPiece_trace_rank (hr : IsUniform H r) :
    ∀ E ∈ liftedPiece H n r, (E ∩ ambient H n r).card = r := by
  intro E hE
  rcases (mem_liftedPiece_iff (H := H) (n := n) (r := r)).mp hE with ⟨B, rfl⟩
  rw [liftedEdge_inter_ambient, card_traceCopy, hr B.1 B.2]

theorem liftedPiece_edges_meet_ambient (hr : IsUniform H r) (hrpos : 1 ≤ r) :
    ∀ E ∈ liftedPiece H n r, (E ∩ ambient H n r).Nonempty := by
  intro E hE
  have hcard := liftedPiece_trace_rank H n r hr E hE
  rw [← hcard] at hrpos
  exact Finset.card_pos.mp hrpos

theorem empty_trace_core (hHne : H.Nonempty)
    (hcore : ∀ x : α, ¬ (∀ A ∈ H, x ∈ A)) :
    ∀ x ∈ ambient H n r, ¬ (∀ E ∈ liftedPiece H n r, x ∈ E) := by
  intro x hx hall
  rcases Finset.mem_image.mp hx with ⟨a | p, _ha, rfl⟩
  · exact hcore a (by
      intro B hB
      let B' : {B : Finset α // B ∈ H} := ⟨B, hB⟩
      have hmem := hall (liftedEdge H n r B') (liftedEdge_mem_liftedPiece H n r B')
      simpa [liftedEdge, traceCopy, privateCopy] using hmem)
  · rcases hHne with ⟨B, hB⟩
    let B' : {B : Finset α // B ∈ H} := ⟨B, hB⟩
    have hmem := hall (liftedEdge H n r B') (liftedEdge_mem_liftedPiece H n r B')
    simpa [liftedEdge, traceCopy, privateCopy] using hmem

end OneBlock

/-- **Proposition 4.3 (One-block universality of empty-core support pieces).**
One-block universality of empty-core support pieces.

This formal version makes explicit the harmless renaming step in the informal proof:
the finite ambient type carrying `H` must fit inside the chosen `n`-set `A`.
The returned data are:

* an `n`-set `A`;
* the nontrivial support-piece family `G = {E_B : B ∈ H}`;
* the full family `F = {A} ∪ G`;
* uniformity and sunflower-freeness of `F`;
* maximality of the one-edge matching `{A}`, expressed by every other edge meeting `A`;
* exact trace recovery of `H` on `A`, through an injective trace copy;
* empty common core of the trace piece over `A`.
-/
theorem support_piece_universality
    (H : Finset (Finset α)) (r k : ℕ)
    (hHne : H.Nonempty) (hrpos : 1 ≤ r) (hr : IsUniform H r)
    (hk : 3 ≤ k) (hfree : SunflowerFree H k)
    (hcore : ∀ x : α, ¬ (∀ A ∈ H, x ∈ A)) :
    ∀ n : ℕ, Fintype.card α ≤ n → r ≤ n →
      ∃ (A : Finset (OneBlockVertex H n r))
        (G F : Finset (Finset (OneBlockVertex H n r)))
        (trace : Finset α → Finset (OneBlockVertex H n r)),
        A.card = n ∧
        IsUniform F n ∧
        SunflowerFree F k ∧
        A ∈ F ∧
        G ⊆ F ∧
        (∀ E ∈ F, E ≠ A → E ∈ G ∧ (E ∩ A).Nonempty) ∧
        (∀ E ∈ G, (E ∩ A).card = r) ∧
        Function.Injective trace ∧
        traceFamily G A = H.image trace ∧
        (∀ x ∈ A, ¬ (∀ E ∈ G, x ∈ E)) ∧
        H.card ≤ F.card := by
  intro n hnα hnr
  let A : Finset (OneBlockVertex H n r) := OneBlock.ambient H n r
  let G : Finset (Finset (OneBlockVertex H n r)) := OneBlock.liftedPiece H n r
  let F : Finset (Finset (OneBlockVertex H n r)) := OneBlock.family H n r
  let trace : Finset α → Finset (OneBlockVertex H n r) := OneBlock.traceCopy H n r
  refine ⟨A, G, F, trace, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact OneBlock.card_ambient H n r hnα
  · exact OneBlock.family_uniform H n r hnα hnr hr
  · exact OneBlock.family_sunflowerFree H n r k hk hfree
  · simp [F, OneBlock.family, A]
  · intro E hE
    simp [F, G, OneBlock.family, hE]
  · intro E hE hEA
    have hG : E ∈ G := by
      simpa [F, G, OneBlock.family, A, hEA] using hE
    exact ⟨hG, OneBlock.liftedPiece_edges_meet_ambient H n r hr hrpos E hG⟩
  · exact OneBlock.liftedPiece_trace_rank H n r hr
  · exact OneBlock.traceCopy_injective H n r
  · exact OneBlock.traceFamily_liftedPiece H n r
  · exact OneBlock.empty_trace_core H n r hHne hcore
  · have hsub : G ⊆ F := by
      intro E hE
      simp [F, G, OneBlock.family, hE]
    have hGcard : G.card = H.card := by
      simp [G, OneBlock.liftedPiece]
      rw [Finset.card_image_of_injective]
      · simp
      · exact OneBlock.liftedEdge_injective H n r
    rw [← hGcard]
    exact Finset.card_le_card hsub

end OneBlockUniversality

end FormalConjectures.Problems.Erdos.E20.Compendium
