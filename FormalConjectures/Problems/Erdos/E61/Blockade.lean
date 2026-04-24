import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Blockade synchronization cores

This file formalizes the finite counting arguments behind
`lem:failed-coordinate` and `prop:coordinate-synchronizes` from the TeX note.
The analytic exponent bookkeeping in the paper is represented here by explicit
integer parameters `s` and `t`.
-/

open Finset
open scoped BigOperators

namespace Erdos61

variable {ι α β : Type*}

/--
Finite core of `lem:failed-coordinate`.

If every `x ∈ X` has fewer than `t` correct neighbors in `Y`, then after choosing
`s` vertices from `X`, the union of their correct neighborhoods has size at most
`s * t`.  If at least `s` vertices of `Y` remain, we get an `s` by `s` pair with
no correct relation.
-/
theorem failed_coordinate_cleans_finite
    (R : α → β → Prop) [DecidableRel R]
    (X : Finset α) (Y : Finset β) {s t : ℕ}
    (hsX : s ≤ X.card)
    (hsmall : ∀ x ∈ X, (Y.filter fun y => R x y).card < t)
    (hroom : s * t + s ≤ Y.card) :
    ∃ X' : Finset α, X' ⊆ X ∧ X'.card = s ∧
      ∃ Y' : Finset β, Y' ⊆ Y ∧ Y'.card = s ∧ Anticomplete R X' Y' := by
  classical
  rcases exists_subset_card_eq hsX with ⟨X', hX'sub, hX'card⟩
  let U : Finset β := X'.biUnion fun x => Y.filter fun y => R x y
  have hUsub : U ⊆ Y := by
    intro y hy
    rcases mem_biUnion.mp hy with ⟨x, hxX', hyx⟩
    exact (mem_filter.mp hyx).1
  have hUcard_le : U.card ≤ s * t := by
    calc
      U.card ≤ ∑ x ∈ X', (Y.filter fun y => R x y).card := card_biUnion_le
      _ ≤ ∑ _x ∈ X', t := by
        refine sum_le_sum ?_
        intro x hxX'
        exact Nat.le_of_lt (hsmall x (hX'sub hxX'))
      _ = X'.card * t := by simp
      _ = s * t := by rw [hX'card]
  have hsdiff_card : s ≤ (Y \ U).card := by
    rw [card_sdiff_of_subset hUsub]
    omega
  rcases exists_subset_card_eq hsdiff_card with ⟨Y', hY'sub_sdiff, hY'card⟩
  have hY'sub : Y' ⊆ Y := by
    intro y hy
    exact (mem_sdiff.mp (hY'sub_sdiff hy)).1
  have hanti : Anticomplete R X' Y' := by
    intro x hxX' y hyY' hxy
    have hyU : y ∈ U := by
      exact mem_biUnion.mpr ⟨x, hxX', mem_filter.mpr ⟨hY'sub hyY', hxy⟩⟩
    exact (mem_sdiff.mp (hY'sub_sdiff hyY')).2 hyU
  exact ⟨X', hX'sub, hX'card, Y', hY'sub, hY'card, hanti⟩

/--
Finite core of `prop:coordinate-synchronizes`.

For each coordinate `j`, let the bad vertices be those not satisfying `Good j`.
If each bad set has size `< s` and the block has room beyond all bad sets, one
vertex is good for every coordinate.
-/
theorem coordinatewise_synchronizes_finite
    (J : Finset ι) (X : Finset α) (Good : ι → α → Prop)
    [∀ j, DecidablePred (Good j)] {s : ℕ}
    (hbad : ∀ j ∈ J, (X.filter fun x => ¬ Good j x).card < s)
    (hroom : J.card * s < X.card) :
    ∃ x ∈ X, ∀ j ∈ J, Good j x := by
  classical
  let Bad : ι → Finset α := fun j => X.filter fun x => ¬ Good j x
  rcases card_union_bad_sets_lt J X Bad
      (by intro j hj x hx; exact (mem_filter.mp hx).1)
      hbad hroom with ⟨x, hxX, hxnot⟩
  refine ⟨x, hxX, ?_⟩
  intro j hj
  by_contra hnot
  exact hxnot j hj (mem_filter.mpr ⟨hxX, hnot⟩)

end Erdos61
