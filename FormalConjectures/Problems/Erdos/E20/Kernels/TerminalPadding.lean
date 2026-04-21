import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open Finset

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-!
# Terminal Kernel Padding

This file proves the finite padding step for terminal kernels in the `Compendium` API.

A rank-at-most-`n` terminal kernel `F` is sent to an `n`-uniform family by adjoining fresh
private vertices to each edge.  The construction preserves cardinality and sunflower-freeness,
and one round of Compendium leaf stripping recovers the original kernel.
-/

variable {α : Type*} [DecidableEq α]

/-- The finite padding index set of an edge `A`: one private slot for each missing element. -/
def terminalPaddingIndexSet (n : ℕ) (A : Finset α) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun i => i.1 < n - A.card

/-- The padded ground type: original vertices plus edge-keyed private vertices. -/
abbrev TerminalPaddingVertex (α : Type*) (n : ℕ) :=
  α ⊕ (Finset α × Fin n)

/-- Pad one edge to size `n`, using private vertices keyed by the edge itself. -/
def terminalPaddingEdge (n : ℕ) (A : Finset α) :
    Finset (TerminalPaddingVertex α n) :=
  A.image Sum.inl ∪
    (terminalPaddingIndexSet n A).image fun i => Sum.inr (A, i)

/-- Pad every edge in a family. -/
def terminalPaddedFamily (n : ℕ) (F : Finset (Finset α)) :
    Finset (Finset (TerminalPaddingVertex α n)) :=
  F.image (terminalPaddingEdge n)

/-- Lift one unpadded edge into the padded ground type without adding private vertices. -/
def terminalLiftEdge (n : ℕ) (A : Finset α) :
    Finset (TerminalPaddingVertex α n) :=
  A.image Sum.inl

/-- The lifted copy of an unpadded family inside the padded ground type. -/
def terminalLiftFamily (n : ℕ) (F : Finset (Finset α)) :
    Finset (Finset (TerminalPaddingVertex α n)) :=
  F.image (terminalLiftEdge n)

omit [DecidableEq α] in
@[simp] theorem mem_terminalPaddingIndexSet {n : ℕ} {A : Finset α} {i : Fin n} :
    i ∈ terminalPaddingIndexSet n A ↔ i.1 < n - A.card := by
  simp [terminalPaddingIndexSet]

omit [DecidableEq α] in
theorem card_terminalPaddingIndexSet {n : ℕ} {A : Finset α} :
    (terminalPaddingIndexSet n A).card = n - A.card := by
  unfold terminalPaddingIndexSet
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Nat.sub_le n A.card)

@[simp] theorem mem_terminalPaddingEdge_left {n : ℕ} {A : Finset α} {x : α} :
    Sum.inl x ∈ terminalPaddingEdge n A ↔ x ∈ A := by
  simp [terminalPaddingEdge]

@[simp] theorem mem_terminalPaddingEdge_right {n : ℕ} {A B : Finset α} {i : Fin n} :
    Sum.inr (B, i) ∈ terminalPaddingEdge n A ↔ B = A ∧ i.1 < n - A.card := by
  simp [terminalPaddingEdge, and_left_comm, eq_comm]

theorem terminalPaddingEdge_injective (n : ℕ) :
    Function.Injective (terminalPaddingEdge (α := α) n) := by
  intro A B hAB
  ext x
  have hx := congrArg (fun E : Finset (TerminalPaddingVertex α n) => Sum.inl x ∈ E) hAB
  simpa using hx

theorem card_terminalPaddingEdge {n : ℕ} {A : Finset α} (hA : A.card ≤ n) :
    (terminalPaddingEdge n A).card = n := by
  rw [terminalPaddingEdge, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ Sum.inl_injective]
    rw [Finset.card_image_of_injective]
    · rw [card_terminalPaddingIndexSet]
      omega
    · intro i j hij
      exact Prod.ext_iff.mp (Sum.inr.inj hij) |>.2
  · rw [Finset.disjoint_left]
    intro x hx_left hx_right
    rcases Finset.mem_image.mp hx_left with ⟨a, -, ha⟩
    rcases Finset.mem_image.mp hx_right with ⟨i, -, hi⟩
    cases ha.trans hi.symm

theorem terminalPaddedFamily_card {n : ℕ} (F : Finset (Finset α)) :
    (terminalPaddedFamily n F).card = F.card := by
  rw [terminalPaddedFamily, Finset.card_image_of_injective]
  exact terminalPaddingEdge_injective n

theorem terminalPaddedFamily_uniform {n : ℕ} {F : Finset (Finset α)}
    (hrank : ∀ A ∈ F, A.card ≤ n) :
    IsUniform (terminalPaddedFamily n F) n := by
  intro E hE
  rcases Finset.mem_image.mp hE with ⟨A, hA, rfl⟩
  exact card_terminalPaddingEdge (hrank A hA)

/-- The original vertices in a set on the padded ground type. -/
def terminalOriginalPart {n : ℕ} (S : Finset (TerminalPaddingVertex α n)) : Finset α :=
  S.biUnion fun v =>
    match v with
    | Sum.inl x => {x}
    | Sum.inr _ => ∅

@[simp] theorem mem_terminalOriginalPart {n : ℕ}
    {S : Finset (TerminalPaddingVertex α n)} {x : α} :
    x ∈ terminalOriginalPart S ↔ Sum.inl x ∈ S := by
  simp [terminalOriginalPart]

@[simp] theorem terminalOriginalPart_image_inl {n : ℕ} (S : Finset α) :
    terminalOriginalPart ((S.image Sum.inl) : Finset (TerminalPaddingVertex α n)) = S := by
  ext x
  simp [terminalOriginalPart]

theorem terminalPaddingEdge_inter {n : ℕ} {A B : Finset α} (hAB : A ≠ B) :
    terminalPaddingEdge n A ∩ terminalPaddingEdge n B = (A ∩ B).image Sum.inl := by
  ext v
  cases v with
  | inl x =>
      simp
  | inr p =>
      rcases p with ⟨C, i⟩
      constructor
      · intro hv
        rcases Finset.mem_inter.mp hv with ⟨hA, hB⟩
        rcases mem_terminalPaddingEdge_right.mp hA with ⟨hCA, -⟩
        rcases mem_terminalPaddingEdge_right.mp hB with ⟨hCB, -⟩
        exact False.elim (hAB (hCA.symm.trans hCB))
      · intro hv
        simp at hv

theorem terminalPaddedFamily_sunflowerFree {n k : ℕ} {F : Finset (Finset α)}
    (hfree : SunflowerFree F k) :
    SunflowerFree (terminalPaddedFamily n F) k := by
  rintro ⟨petals, Y, hpetals_mem, hpetals_inj, hpetals_inter⟩
  choose original horiginal_mem horiginal_eq using fun i =>
    Finset.mem_image.mp (hpetals_mem i)
  have horiginal_inj : Function.Injective original := by
    intro i j hij
    apply hpetals_inj
    calc
      petals i = terminalPaddingEdge n (original i) := (horiginal_eq i).symm
      _ = terminalPaddingEdge n (original j) := by rw [hij]
      _ = petals j := horiginal_eq j
  refine hfree ⟨original, terminalOriginalPart Y, horiginal_mem, horiginal_inj, ?_⟩
  intro i j hij
  have horiginal_ne : original i ≠ original j := fun h => hij (horiginal_inj h)
  have himage_eq : ((original i ∩ original j).image Sum.inl :
      Finset (TerminalPaddingVertex α n)) = Y := by
    calc
      ((original i ∩ original j).image Sum.inl : Finset (TerminalPaddingVertex α n))
          = terminalPaddingEdge n (original i) ∩ terminalPaddingEdge n (original j) :=
            (terminalPaddingEdge_inter (n := n) horiginal_ne).symm
      _ = petals i ∩ petals j := by rw [horiginal_eq i, horiginal_eq j]
      _ = Y := hpetals_inter i j hij
  have hpart := congrArg (terminalOriginalPart (α := α) (n := n)) himage_eq
  simpa using hpart

theorem terminalLiftEdge_injective (n : ℕ) :
    Function.Injective (terminalLiftEdge (α := α) n) := by
  intro A B hAB
  ext x
  have hx := congrArg (fun E : Finset (TerminalPaddingVertex α n) => Sum.inl x ∈ E) hAB
  simpa [terminalLiftEdge] using hx

theorem terminalLiftFamily_card {n : ℕ} (F : Finset (Finset α)) :
    (terminalLiftFamily n F).card = F.card := by
  rw [terminalLiftFamily, Finset.card_image_of_injective]
  exact terminalLiftEdge_injective n

theorem familyDegree_terminalPaddedFamily_left {n : ℕ}
    (F : Finset (Finset α)) (x : α) :
    familyDegree (terminalPaddedFamily n F) {Sum.inl x} = familyDegree F {x} := by
  rw [familyDegree, terminalPaddedFamily, Finset.filter_image]
  rw [Finset.card_image_of_injective _ (terminalPaddingEdge_injective n)]
  congr 1
  ext A
  simp

theorem familyDegree_terminalPaddedFamily_right_of_mem {n : ℕ}
    {F : Finset (Finset α)} {A : Finset α} (hA : A ∈ F) {i : Fin n}
    (hi : i ∈ terminalPaddingIndexSet n A) :
    familyDegree (terminalPaddedFamily n F) {Sum.inr (A, i)} = 1 := by
  rw [familyDegree, terminalPaddedFamily, Finset.filter_image]
  rw [Finset.card_image_of_injective _ (terminalPaddingEdge_injective n)]
  have hfilter :
      (F.filter fun B => {Sum.inr (A, i)} ⊆ terminalPaddingEdge n B) = {A} := by
    have hi' : i.1 < n - A.card := by simpa using hi
    ext B
    constructor
    · intro hB
      have hmem : Sum.inr (A, i) ∈ terminalPaddingEdge n B :=
        (Finset.mem_filter.mp hB).2 (by simp)
      exact Finset.mem_singleton.mpr (mem_terminalPaddingEdge_right.mp hmem).1.symm
    · intro hBA
      have hBA' : B = A := by simpa using hBA
      subst B
      exact Finset.mem_filter.mpr ⟨hA, by simpa using hi'⟩
  rw [hfilter]
  simp

theorem not_mem_familyLeaves_terminalPaddedFamily_left [Fintype α] {n : ℕ}
    {F : Finset (Finset α)} (hleaves : familyLeaves F = ∅) (x : α) :
    Sum.inl x ∉ familyLeaves (terminalPaddedFamily n F) := by
  intro hx
  have hdeg_padded : familyDegree (terminalPaddedFamily n F) {Sum.inl x} = 1 := by
    simpa [familyLeaves] using (Finset.mem_filter.mp hx).2
  have hdeg_original : familyDegree F {x} = 1 := by
    simpa [familyDegree_terminalPaddedFamily_left (n := n) F x] using hdeg_padded
  have hx_original : x ∈ familyLeaves F := by
    simp [familyLeaves, hdeg_original]
  rw [hleaves] at hx_original
  simp at hx_original

theorem mem_familyLeaves_terminalPaddedFamily_right [Fintype α] {n : ℕ}
    {F : Finset (Finset α)} {A : Finset α} (hA : A ∈ F) {i : Fin n}
    (hi : i ∈ terminalPaddingIndexSet n A) :
    Sum.inr (A, i) ∈ familyLeaves (terminalPaddedFamily n F) := by
  have hdeg := familyDegree_terminalPaddedFamily_right_of_mem (n := n) hA hi
  simp [familyLeaves, hdeg]

theorem terminalPaddingEdge_sdiff_familyLeaves [Fintype α] {n : ℕ}
    {F : Finset (Finset α)} (hleaves : familyLeaves F = ∅)
    {A : Finset α} (hA : A ∈ F) :
    terminalPaddingEdge n A \ familyLeaves (terminalPaddedFamily n F) =
      terminalLiftEdge n A := by
  ext v
  cases v with
  | inl x =>
      simp [terminalLiftEdge, not_mem_familyLeaves_terminalPaddedFamily_left
        (n := n) (F := F) hleaves x]
  | inr p =>
      rcases p with ⟨B, i⟩
      constructor
      · intro hv
        rcases Finset.mem_sdiff.mp hv with ⟨hmem, hnot_leaf⟩
        rcases mem_terminalPaddingEdge_right.mp hmem with ⟨hBA, hi⟩
        subst B
        have hi_mem : i ∈ terminalPaddingIndexSet n A := by simpa using hi
        exact False.elim
          (hnot_leaf (mem_familyLeaves_terminalPaddedFamily_right (n := n) hA hi_mem))
      · intro hv
        simp [terminalLiftEdge] at hv

theorem stripOnce_terminalPaddedFamily [Fintype α] {n : ℕ}
    {F : Finset (Finset α)} (hleaves : familyLeaves F = ∅) :
    stripOnce (terminalPaddedFamily n F) = terminalLiftFamily n F := by
  ext E
  constructor
  · intro hE
    rcases Finset.mem_image.mp hE with ⟨P, hP, hPE⟩
    rcases Finset.mem_image.mp hP with ⟨A, hA, hAP⟩
    refine Finset.mem_image.mpr ⟨A, hA, ?_⟩
    calc
      terminalLiftEdge n A
          = terminalPaddingEdge n A \ familyLeaves (terminalPaddedFamily n F) :=
            (terminalPaddingEdge_sdiff_familyLeaves (n := n) hleaves hA).symm
      _ = P \ familyLeaves (terminalPaddedFamily n F) := by rw [hAP]
      _ = E := hPE
  · intro hE
    rcases Finset.mem_image.mp hE with ⟨A, hA, hAE⟩
    refine Finset.mem_image.mpr ⟨terminalPaddingEdge n A, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    · calc
        terminalPaddingEdge n A \ familyLeaves (terminalPaddedFamily n F)
            = terminalLiftEdge n A :=
              terminalPaddingEdge_sdiff_familyLeaves (n := n) hleaves hA
        _ = E := hAE

theorem exists_terminalPaddedFamily [Fintype α] {n k : ℕ}
    {F : Finset (Finset α)}
    (hrank : ∀ A ∈ F, A.card ≤ n) (hfree : SunflowerFree F k)
    (hleaves : familyLeaves F = ∅) :
    ∃ G : Finset (Finset (TerminalPaddingVertex α n)),
      IsUniform G n ∧ SunflowerFree G k ∧ G.card = F.card ∧
        stripOnce G = terminalLiftFamily n F := by
  refine ⟨terminalPaddedFamily n F, ?_, ?_, ?_, ?_⟩
  · exact terminalPaddedFamily_uniform hrank
  · exact terminalPaddedFamily_sunflowerFree hfree
  · exact terminalPaddedFamily_card F
  · exact stripOnce_terminalPaddedFamily hleaves

/-- The witness set used by `sunflowerNumber`. -/
def uniformSunflowerFreeCardSet (n k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ (α : Type) (_ : DecidableEq α) (_ : Fintype α)
    (F : Finset (Finset α)), IsUniform F n ∧ SunflowerFree F k ∧ F.card = m}

/-- The witness set used by `terminalKernelNumber`. -/
def terminalKernelCardSet (n k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ (α : Type) (_ : DecidableEq α) (_ : Fintype α)
    (F : Finset (Finset α)),
    (∀ A ∈ F, A.card ≤ n) ∧ SunflowerFree F k ∧
    familyLeaves F = ∅ ∧ F.card = m}

theorem card_mem_uniformSunflowerFreeCardSet_of_rank_sunflowerFree
    {β : Type} [DecidableEq β] [Finite β]
    {n k : ℕ} {F : Finset (Finset β)}
    (hrank : ∀ A ∈ F, A.card ≤ n) (hfree : SunflowerFree F k) :
    F.card ∈ uniformSunflowerFreeCardSet n k := by
  letI : Fintype β := Fintype.ofFinite β
  refine ⟨TerminalPaddingVertex β n, inferInstance, inferInstance,
    terminalPaddedFamily n F, ?_, ?_, ?_⟩
  · exact terminalPaddedFamily_uniform hrank
  · exact terminalPaddedFamily_sunflowerFree hfree
  · exact terminalPaddedFamily_card F

theorem sunflowerFree_empty_of_pos {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) :
    SunflowerFree (∅ : Finset (Finset α)) k := by
  rintro ⟨petals, _Y, hpetals, _hinj, _hinter⟩
  simpa using hpetals ⟨0, hk⟩

theorem terminalKernelCardSet_nonempty {n k : ℕ} (hk : 1 ≤ k) :
    (terminalKernelCardSet n k).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨PUnit, inferInstance, inferInstance, ∅, ?_, ?_, ?_, rfl⟩
  · intro A hA
    simp at hA
  · exact sunflowerFree_empty_of_pos (α := PUnit) hk
  · simp [familyLeaves, familyDegree]

/-- Every terminal rank-at-most-`n` witness pads to an `n`-uniform witness of the same size.

The extra `BddAbove` hypothesis is exactly the one needed to use `le_csSup` with the current
`sunflowerNumber` definition.  The concrete padding theorem above does not require it. -/
theorem terminalKernelNumber_le_sunflowerNumber_of_bddAbove {n k : ℕ}
    (hk : 1 ≤ k) (hsun_bdd : BddAbove (uniformSunflowerFreeCardSet n k)) :
    terminalKernelNumber n k ≤ sunflowerNumber n k := by
  change sSup (terminalKernelCardSet n k) ≤ sSup (uniformSunflowerFreeCardSet n k)
  refine csSup_le (terminalKernelCardSet_nonempty (n := n) (k := k) hk) ?_
  intro m hm
  rcases hm with ⟨β, decβ, finβ, F, hrank, hfree, _hleaves, rfl⟩
  letI : DecidableEq β := decβ
  letI : Fintype β := finβ
  exact le_csSup hsun_bdd
    (card_mem_uniformSunflowerFreeCardSet_of_rank_sunflowerFree
      (n := n) (k := k) (F := F) hrank hfree)

end FormalConjectures.Problems.Erdos.E20.Compendium
