import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Ordered cutpoint cores

This file formalizes the suffix-row extraction step used in the paper's
one-switch and cutpoint-canonization arguments.
-/

namespace Erdos61

open Finset

/-- A relation has suffix rows on natural-number indices. -/
def HasSuffixRows (R : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃i j k : ℕ⦄, i < j → j ≤ k → R i j → R i k

/--
If row `a r` has one true entry before the next selected representative, suffix
monotonicity makes it true to every later representative.
-/
theorem suffix_rows_force_later_representatives
    {m : ℕ} {R : ℕ → ℕ → Prop} (hR : HasSuffixRows R)
    (a witness : Fin m → ℕ)
    (ha_w : ∀ r, a r < witness r)
    (hw_a : ∀ r s, r < s → witness r ≤ a s)
    (htrue : ∀ r, R (a r) (witness r)) :
    ∀ r s, r < s → R (a r) (a s) := by
  intro r s hrs
  exact hR (ha_w r) (hw_a r s hrs) (htrue r)

/-- A block with no true ordered pair gives a constant-false ordered subblock. -/
theorem no_true_pairs_constant_false {ι : Type*} {R : ι → ι → Prop} (I : Finset ι)
    (hfalse : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ R x y) :
    ∀ x ∈ I, ∀ y ∈ I, x ≠ y → R x y = False := by
  intro x hx y hy hxy
  exact propext ⟨fun h => (hfalse x hx y hy hxy h).elim, False.elim⟩

/--
Block form of the one-switch extraction lemma.

The order is split into `m` ordered blocks, each of size at least `m`.
For a relation with suffix rows, either one block contains an `m`-set on which
all ordered pairs are false, or choosing one true row from each block gives an
`m`-set on which all ordered pairs are true.
-/
theorem one_switch_extraction_from_ordered_blocks
    {R : ℕ → ℕ → Prop} (hR : HasSuffixRows R)
    {m : ℕ} (block : Fin m → Finset ℕ)
    (hlarge : ∀ r, m ≤ (block r).card)
    (hordered : ∀ ⦃r s : Fin m⦄, r < s →
      ∀ x ∈ block r, ∀ y ∈ block s, x < y) :
    ∃ I : Finset ℕ, I ⊆ (Finset.univ : Finset (Fin m)).biUnion block ∧ m ≤ I.card ∧
      ((∀ x ∈ I, ∀ y ∈ I, x < y → R x y) ∨
        ∀ x ∈ I, ∀ y ∈ I, x < y → ¬ R x y) := by
  classical
  by_cases hfalseBlock :
      ∃ r : Fin m, ∀ x ∈ block r, ∀ y ∈ block r, x < y → ¬ R x y
  · rcases hfalseBlock with ⟨r, hrfalse⟩
    rcases exists_subset_card_eq (hlarge r) with ⟨I, hIsub, hIcard⟩
    refine ⟨I, ?_, by omega, Or.inr ?_⟩
    · intro x hx
      exact mem_biUnion.mpr ⟨r, mem_univ r, hIsub hx⟩
    · intro x hx y hy hxy
      exact hrfalse x (hIsub hx) y (hIsub hy) hxy
  · have htrueBlock :
        ∀ r : Fin m, ∃ a ∈ block r, ∃ w ∈ block r, a < w ∧ R a w := by
      intro r
      by_contra hnot
      exact hfalseBlock ⟨r, by
        intro x hx y hy hxy hxyR
        exact hnot ⟨x, hx, y, hy, hxy, hxyR⟩⟩
    choose a ha w hw haw htrue using htrueBlock
    let I : Finset ℕ := Finset.univ.image a
    have hainj : Set.InjOn a (Finset.univ : Finset (Fin m)) := by
      intro r hr s hs hrs
      by_contra hne
      rcases lt_or_gt_of_ne hne with hrs_lt | hsr_lt
      · have hlt : a r < a s := hordered hrs_lt (a r) (ha r) (a s) (ha s)
        omega
      · have hlt : a s < a r := hordered hsr_lt (a s) (ha s) (a r) (ha r)
        omega
    refine ⟨I, ?_, ?_, Or.inl ?_⟩
    · intro x hx
      rcases mem_image.mp hx with ⟨r, _hr, rfl⟩
      exact mem_biUnion.mpr ⟨r, mem_univ r, ha r⟩
    · change m ≤ (Finset.univ.image a).card
      rw [card_image_of_injOn hainj, card_univ, Fintype.card_fin]
    · intro x hx y hy hxy
      rcases mem_image.mp hx with ⟨r, _hr, rfl⟩
      rcases mem_image.mp hy with ⟨s, _hs, rfl⟩
      have hrs_ne : r ≠ s := by
        intro hrs
        subst s
        omega
      rcases lt_or_gt_of_ne hrs_ne with hrs_lt | hsr_lt
      · exact hR (haw r) (Nat.le_of_lt (hordered hrs_lt (w r) (hw r) (a s) (ha s)))
          (htrue r)
      · have hlt : a s < a r := hordered hsr_lt (a s) (ha s) (a r) (ha r)
        omega

end Erdos61
