import FormalConjectures.Util.ProblemImports

/-!
# Shared definitions for Erdős Problem 61 notes

This folder formalizes fully checked cores from `eh_forum_trimmed_v9.tex`.
The definitions here are intentionally small and local: they support the
finite Boolean, blockade, and rooted-`P4` counting arguments used in the note.
-/

open Finset
open scoped BigOperators

namespace Erdos61

variable {α β γ : Type*}

/-- Two finite sets are anticomplete with respect to a binary relation. -/
def Anticomplete (R : α → β → Prop) (A : Finset α) (B : Finset β) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ R a b

/-- Two finite sets are complete with respect to a binary relation. -/
def CompleteTo (R : α → β → Prop) (A : Finset α) (B : Finset β) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, R a b

/-- A finite relation trace on `A`, represented by the set of points related to `x`. -/
def traceFinset [DecidableEq β] (R : α → β → Prop) [DecidableRel R]
    (A : Finset β) (x : α) : Finset β :=
  A.filter fun y => R x y

/-- The fiber of a map over a finite support. -/
def fiberOver [DecidableEq β] (S : Finset α) (f : α → β) (y : β) : Finset α :=
  S.filter fun x => f x = y

@[simp] lemma mem_fiberOver_iff [DecidableEq β]
    {S : Finset α} {f : α → β} {y : β} {x : α} :
    x ∈ fiberOver S f y ↔ x ∈ S ∧ f x = y := by
  simp [fiberOver]

theorem biUnion_image_fiberOver_eq [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    (S.image f).biUnion (fun y => fiberOver S f y) = S := by
  ext x
  constructor
  · intro hx
    rcases mem_biUnion.mp hx with ⟨y, _hy, hxy⟩
    exact (mem_fiberOver_iff.mp hxy).1
  · intro hx
    exact mem_biUnion.mpr ⟨f x, mem_image.mpr ⟨x, hx, rfl⟩, by simp [fiberOver, hx]⟩

theorem card_eq_sum_card_fiberOver_image [DecidableEq β]
    (S : Finset α) (f : α → β) :
    S.card = ∑ y ∈ S.image f, (fiberOver S f y).card := by
  classical
  have hdisj :
      ((S.image f : Finset β) : Set β).PairwiseDisjoint (fun y => fiberOver S f y) := by
    simpa [fiberOver] using
      (Set.pairwiseDisjoint_filter f (↑(S.image f) : Set β) S)
  calc
    S.card = ((S.image f).biUnion fun y => fiberOver S f y).card := by
      rw [biUnion_image_fiberOver_eq]
    _ = ∑ y ∈ S.image f, (fiberOver S f y).card := by
      exact card_biUnion hdisj

/--
If a finite set is mapped to few values, some fiber has at least the average
size.  The conclusion is stated multiplicatively to avoid division.
-/
theorem exists_large_fiber [DecidableEq β]
    (S : Finset α) (f : α → β) (hS : S.Nonempty) :
    ∃ y ∈ S.image f, S.card ≤ (S.image f).card * (fiberOver S f y).card := by
  classical
  have hImage : (S.image f).Nonempty := by
    rcases hS with ⟨x, hx⟩
    exact ⟨f x, mem_image.mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, hymax⟩ :=
    exists_max_image (S.image f) (fun y => (fiberOver S f y).card) hImage
  refine ⟨y, hy, ?_⟩
  calc
    S.card = ∑ y' ∈ S.image f, (fiberOver S f y').card :=
      card_eq_sum_card_fiberOver_image S f
    _ ≤ ∑ _y' ∈ S.image f, (fiberOver S f y).card := by
      refine sum_le_sum ?_
      intro y' hy'
      exact hymax y' hy'
    _ = (S.image f).card * (fiberOver S f y).card := by simp

/-- A convenient threshold form of `exists_large_fiber`. -/
theorem exists_fiber_card_ge [DecidableEq β]
    (S : Finset α) (f : α → β) {q s : ℕ}
    (hS : S.Nonempty) (himage : (S.image f).card ≤ q) (hcard : q * s ≤ S.card) :
    ∃ y ∈ S.image f, s ≤ (fiberOver S f y).card := by
  classical
  rcases exists_large_fiber S f hS with ⟨y, hy, hlarge⟩
  refine ⟨y, hy, ?_⟩
  by_contra hnot
  have hlt : (fiberOver S f y).card < s := Nat.lt_of_not_ge hnot
  have hqpos : 0 < q := by
    by_contra hqnot
    have hq : q = 0 := Nat.eq_zero_of_not_pos hqnot
    have hImage0 : (S.image f).card = 0 := Nat.eq_zero_of_le_zero (by simpa [hq] using himage)
    exact (S.image_nonempty.mpr hS).ne_empty (card_eq_zero.mp hImage0)
  have hle : S.card < q * s := by
    calc
      S.card ≤ (S.image f).card * (fiberOver S f y).card := hlarge
      _ ≤ q * (fiberOver S f y).card := Nat.mul_le_mul_right _ himage
      _ < q * s := Nat.mul_lt_mul_of_pos_left hlt hqpos
  · exact Nat.not_lt_of_ge hcard hle

lemma anticomplete_filter_not (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    Anticomplete R A (B.filter fun b => ∀ a ∈ A, ¬ R a b) := by
  intro a ha b hb
  exact (mem_filter.mp hb).2 a ha

lemma anticomplete_filter_not_left (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    Anticomplete R (A.filter fun a => ∀ b ∈ B, ¬ R a b) B := by
  intro a ha b hb
  exact (mem_filter.mp ha).2 b hb

lemma card_union_bad_sets_lt
    {ι α : Type*} (I : Finset ι) (X : Finset α)
    (Bad : ι → Finset α) (hBadSub : ∀ i ∈ I, Bad i ⊆ X)
    {s : ℕ} (hBad : ∀ i ∈ I, (Bad i).card < s)
    (hRoom : I.card * s < X.card) :
    ∃ x ∈ X, ∀ i ∈ I, x ∉ Bad i := by
  classical
  let U : Finset α := I.biUnion Bad
  have hUsub : U ⊆ X := by
    intro x hx
    rcases mem_biUnion.mp hx with ⟨i, hi, hxBad⟩
    exact hBadSub i hi hxBad
  have hUcard_le : U.card ≤ I.card * s := by
    calc
      U.card ≤ ∑ i ∈ I, (Bad i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ I, s := by
        exact sum_le_sum fun i hi => Nat.le_of_lt (hBad i hi)
      _ = I.card * s := by simp
  have hUne : U ≠ X := by
    intro hEq
    have : X.card ≤ I.card * s := by
      rw [← hEq]
      exact hUcard_le
    exact Nat.not_lt_of_ge this hRoom
  have hproper : U ⊂ X := ⟨hUsub, fun hXU => hUne (Subset.antisymm hUsub hXU)⟩
  rcases exists_of_ssubset hproper with ⟨x, hxX, hxU⟩
  refine ⟨x, hxX, ?_⟩
  intro i hi hxBad
  exact hxU (mem_biUnion.mpr ⟨i, hi, hxBad⟩)

end Erdos61
