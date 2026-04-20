import Mathlib

open Finset
open scoped Classical

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Projection and Refinement Transfer

This file formalizes the exact counting statements behind the user's
"projected-prefix theorem" and "ambient-prefix transfer" note.

Rather than building the bookkeeping into one specific code model, we work with an arbitrary
finite support `S` and arbitrary finite-valued maps:

* `p : α → β` plays the role of the projected-prefix map;
* `q : α → γ` plays the role of the ambient-prefix refinement map inside a fixed `p`-fiber.

The main outputs are exact finite counting lemmas:

* some `p`-fiber has cardinality at least the average fiber size;
* inside any fixed `p`-fiber, some `q`-refinement fiber has cardinality at least the average
  refinement size.

These are the uniform-mass specializations of the user's weighted profitable-prefix assertions.
-/

section GenericFibers

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The fiber of a finite support `S` over a value `y` of a map `f`. -/
def fiberOver (S : Finset α) (f : α → β) (y : β) : Finset α :=
  S.filter fun x => f x = y

@[simp] theorem mem_fiberOver_iff {S : Finset α} {f : α → β} {y : β} {x : α} :
    x ∈ fiberOver S f y ↔ x ∈ S ∧ f x = y := by
  simp [fiberOver]

theorem biUnion_image_fiberOver_eq (S : Finset α) (f : α → β) :
    (S.image f).biUnion (fun y => fiberOver S f y) = S := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hx⟩
    exact (mem_fiberOver_iff.mp hx).1
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, by simp [fiberOver, hx]⟩

theorem card_eq_sum_card_fiberOver_image (S : Finset α) (f : α → β) :
    S.card = ∑ y ∈ S.image f, (fiberOver S f y).card := by
  have hdisj :
      ((S.image f : Finset β) : Set β).PairwiseDisjoint (fun y => fiberOver S f y) := by
    simpa [fiberOver] using
      (Set.pairwiseDisjoint_filter f (↑(S.image f) : Set β) S)
  calc
    S.card = ((S.image f).biUnion fun y => fiberOver S f y).card := by
      rw [biUnion_image_fiberOver_eq]
    _ = ∑ y ∈ S.image f, (fiberOver S f y).card := by
      exact Finset.card_biUnion hdisj

/-- Some fiber has cardinality at least the average fiber size over `S.image f`.

Equivalently, there is `y` with
`S.card ≤ |image(f)| * |fiber_y|`. -/
theorem exists_large_fiber
    (S : Finset α) (f : α → β) (hS : S.Nonempty) :
    ∃ y ∈ S.image f, S.card ≤ (S.image f).card * (fiberOver S f y).card := by
  have hImage : (S.image f).Nonempty := by
    rcases hS with ⟨x, hx⟩
    exact ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, hymax⟩ :=
    Finset.exists_max_image (S.image f) (fun y => (fiberOver S f y).card) hImage
  refine ⟨y, hy, ?_⟩
  calc
    S.card = ∑ y' ∈ S.image f, (fiberOver S f y').card := card_eq_sum_card_fiberOver_image S f
    _ ≤ ∑ _y' ∈ S.image f, (fiberOver S f y).card := by
      refine Finset.sum_le_sum ?_
      intro y' hy'
      exact hymax y' hy'
    _ = (S.image f).card * (fiberOver S f y).card := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Inside any fixed `p`-fiber, some `q`-refinement fiber has cardinality at least the average
refinement size.

This is the exact counting core of the user's ambient-prefix transfer theorem, with the
refinement count given by `|(fiberOver S p b).image q|`. -/
theorem exists_large_refinementFiber
    (S : Finset α) (p : α → β) (q : α → γ) {b : β}
    (hb : b ∈ S.image p) :
    ∃ c ∈ (fiberOver S p b).image q,
      (fiberOver S p b).card ≤
        ((fiberOver S p b).image q).card * (fiberOver (fiberOver S p b) q c).card := by
  rcases Finset.mem_image.mp hb with ⟨x, hxS, rfl⟩
  have hFiber : (fiberOver S p (p x)).Nonempty := by
    exact ⟨x, by simp [fiberOver, hxS]⟩
  simpa using exists_large_fiber (fiberOver S p (p x)) q hFiber

/-- Abstract projected-prefix plus ambient-refinement transfer.

If `p` has at most `B` patterns on `S`, then one `p`-fiber is `B`-profitable; if `q` is then used
to refine that chosen fiber, some refinement cell is large up to the exact refinement count
`|(fiberOver S p b).image q|`. -/
theorem exists_large_projected_then_refinedFiber
    (S : Finset α) (p : α → β) (q : α → γ) (hS : S.Nonempty) {B : ℕ}
    (hB : (S.image p).card ≤ B) :
    ∃ b ∈ S.image p, ∃ c ∈ (fiberOver S p b).image q,
      S.card ≤ B * (((fiberOver S p b).image q).card * (fiberOver (fiberOver S p b) q c).card) := by
  obtain ⟨b, hb, hbLarge⟩ := exists_large_fiber S p hS
  obtain ⟨c, hc, hcLarge⟩ := exists_large_refinementFiber S p q hb
  refine ⟨b, hb, c, hc, ?_⟩
  calc
    S.card ≤ (S.image p).card * (fiberOver S p b).card := hbLarge
    _ ≤ B * (fiberOver S p b).card := by
      exact Nat.mul_le_mul_right _ hB
    _ ≤ B * (((fiberOver S p b).image q).card * (fiberOver (fiberOver S p b) q c).card) := by
      exact Nat.mul_le_mul_left _ hcLarge

end GenericFibers

section WordCodes

variable {G : Type*} [DecidableEq G]

/-- Coordinate projection of a word onto a selected coordinate map `ι`. -/
def selectCoords {m s : ℕ} (ι : Fin s → Fin m) (x : Fin m → G) : Fin s → G :=
  fun i => x (ι i)

/-- The corresponding finite code projection. -/
def projectedCode {m s : ℕ} (C : Finset (Fin m → G)) (ι : Fin s → Fin m) :
    Finset (Fin s → G) :=
  C.image (selectCoords ι)

/-- The fiber of a code over a selected coordinate pattern. -/
def projectedFiber {m s : ℕ} (C : Finset (Fin m → G)) (ι : Fin s → Fin m)
    (u : Fin s → G) : Finset (Fin m → G) :=
  fiberOver C (selectCoords ι) u

theorem exists_large_projectedFiber_of_card_bound
    {m s : ℕ} (C : Finset (Fin m → G)) (ι : Fin s → Fin m)
    (hC : C.Nonempty) {B : ℕ} (hB : (projectedCode C ι).card ≤ B) :
    ∃ u ∈ projectedCode C ι, C.card ≤ B * (projectedFiber C ι u).card := by
  obtain ⟨u, hu, hlarge⟩ := exists_large_fiber C (selectCoords ι) hC
  refine ⟨u, by simpa [projectedCode] using hu, ?_⟩
  calc
    C.card ≤ (C.image (selectCoords ι)).card * (fiberOver C (selectCoords ι) u).card := hlarge
    _ ≤ B * (fiberOver C (selectCoords ι) u).card := by
      exact Nat.mul_le_mul_right _ hB
    _ = B * (projectedFiber C ι u).card := by
      simp [projectedFiber]

end WordCodes

end FormalConjectures.Problems.Erdos.E20
