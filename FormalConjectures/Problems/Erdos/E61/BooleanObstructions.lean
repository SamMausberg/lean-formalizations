import FormalConjectures.Problems.Erdos.E61.RootedP4

/-!
# Boolean rectangle obstructions

This file packages the finite rectangle-trace constructions used in
`prop:boolean-obstructions`: arbitrarily large stars and matchings are
shattered by rectangle traces, and the matching example has `2^m` one-sided
trace choices.
-/

open Finset

namespace Erdos61

/-- The `m`-edge star used in the Boolean local obstruction. -/
def booleanStarEdges (m : ℕ) : Finset (PUnit × Fin m) :=
  (Finset.univ : Finset (Fin m)).image fun i => (PUnit.unit, i)

/-- The `m`-edge matching used in the Boolean local obstruction. -/
def booleanMatchingEdges (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ : Finset (Fin m)).image fun i => (i, i)

@[simp] theorem card_booleanStarEdges (m : ℕ) :
    (booleanStarEdges m).card = m := by
  rw [booleanStarEdges, card_image_of_injOn]
  · simp
  · intro i _ j _ hij
    exact Prod.ext_iff.mp hij |>.2

@[simp] theorem card_booleanMatchingEdges (m : ℕ) :
    (booleanMatchingEdges m).card = m := by
  rw [booleanMatchingEdges, card_image_of_injOn]
  · simp
  · intro i _ j _ hij
    exact Prod.ext_iff.mp hij |>.1

/-- Rectangle traces shatter an arbitrary finite star. -/
theorem boolean_star_edges_shattered (m : ℕ) :
    ShatteredByRectangles (booleanStarEdges m) (booleanStarEdges m) := by
  simpa [booleanStarEdges] using
    star_edges_shattered_by_rectangles (PUnit.unit) (Finset.univ : Finset (Fin m))
      (booleanStarEdges m) (by intro e he; exact he)

/-- Rectangle traces shatter an arbitrary finite matching. -/
theorem boolean_matching_edges_shattered (m : ℕ) :
    ShatteredByRectangles (booleanMatchingEdges m) (booleanMatchingEdges m) := by
  simpa [booleanMatchingEdges] using
    matching_edges_shattered_by_rectangles
      (fun i : Fin m => i) (fun i : Fin m => i) (Finset.univ : Finset (Fin m))
      (by intro i _ j _ h; exact h) (by intro i _ j _ h; exact h)
      (booleanMatchingEdges m) (by intro e he; exact he)

/-- The family of all one-sided traces in the matching cube. -/
def booleanTraceFamily (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powerset

@[simp] theorem card_booleanTraceFamily (m : ℕ) :
    (booleanTraceFamily m).card = 2 ^ m := by
  simp [booleanTraceFamily]

/-- Star form of `prop:boolean-obstructions` at the rectangle-trace level. -/
theorem boolean_star_obstruction_finite (m : ℕ) :
    ∃ E : Finset (PUnit × Fin m),
      E.card = m ∧ ShatteredByRectangles E E := by
  exact ⟨booleanStarEdges m, by simp, boolean_star_edges_shattered m⟩

/--
Matching form of `prop:boolean-obstructions` at the rectangle-trace level,
including the exact `2^m` count of one-sided trace choices.
-/
theorem boolean_matching_obstruction_finite (m : ℕ) :
    ∃ E : Finset (Fin m × Fin m), ∃ T : Finset (Finset (Fin m)),
      E.card = m ∧ T.card = 2 ^ m ∧ ShatteredByRectangles E E := by
  exact ⟨booleanMatchingEdges m, booleanTraceFamily m, by simp, by simp,
    boolean_matching_edges_shattered m⟩

end Erdos61
