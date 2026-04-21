import FormalConjectures.Problems.Erdos.E20.Families.BalancedMultislice

namespace FormalConjectures.Problems.Erdos.E20

open Finset BigOperators

/-!
# Quantitative support-box density obstruction for the balanced multislice

`BalancedMultislice.lean` proves that a nonempty support box with a live
coordinate cannot be entirely balanced.  This file records a finite quantitative
strengthening: if the support box contains one balanced word, then every live
coordinate produces a distinct one-coordinate perturbation which remains in the
box and is not balanced.

Consequently, inside such a box,

`balanced_count + live_coordinate_count ≤ box_count`.

This is an exact finite support-box obstruction.  It is not the asymptotic
`C_q / sqrt r` estimate from the paper notes.
-/

lemma exists_mem_ne_of_mem_liveCoordinates {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q) {i : Fin n}
    (hi : i ∈ liveCoordinates S) :
    ∃ b : Fin q, b ∈ S i ∧ b ≠ x i := by
  classical
  have hcard : 1 < (S i).card := by
    have htwo : 2 ≤ (S i).card := mem_liveCoordinates.mp hi
    omega
  rcases Finset.exists_mem_ne hcard (x i) with ⟨b, hbS, hbne⟩
  exact ⟨b, hbS, hbne⟩

/-- A deterministic allowed symbol different from `x i` at a live coordinate. -/
noncomputable def liveCoordinateAlternative {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q)
    (i : Fin n) (hi : i ∈ liveCoordinates S) : Fin q :=
  Classical.choose (exists_mem_ne_of_mem_liveCoordinates S x hi)

lemma liveCoordinateAlternative_mem {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q)
    {i : Fin n} (hi : i ∈ liveCoordinates S) :
    liveCoordinateAlternative S x i hi ∈ S i :=
  (Classical.choose_spec (exists_mem_ne_of_mem_liveCoordinates S x hi)).1

lemma liveCoordinateAlternative_ne {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q)
    {i : Fin n} (hi : i ∈ liveCoordinates S) :
    liveCoordinateAlternative S x i hi ≠ x i :=
  (Classical.choose_spec (exists_mem_ne_of_mem_liveCoordinates S x hi)).2

/-- Changing one coordinate of a balanced word to a different symbol makes it unbalanced. -/
lemma update_not_mem_balancedWords_of_ne {n q : ℕ} {x : Fin n → Fin q}
    (hxbal : x ∈ balancedWords n q) (i : Fin n) {b : Fin q}
    (hbne : b ≠ x i) :
    Function.update x i b ∉ balancedWords n q := by
  intro hybal_mem
  have hxbal' : IsBalancedWord x := mem_balancedWords.mp hxbal
  have hybal' : IsBalancedWord (Function.update x i b) := mem_balancedWords.mp hybal_mem
  have hcount :
      symbolCount (Function.update x i b) (x i) = symbolCount x (x i) - 1 :=
    symbolCount_update_ne x i b hbne
  have hxcount : symbolCount x (x i) = n / q := hxbal' (x i)
  have hycount : symbolCount (Function.update x i b) (x i) = n / q := hybal' (x i)
  have hpos : 0 < symbolCount x (x i) := by
    rw [symbolCount]
    exact Finset.card_pos.mpr ⟨i, by simp⟩
  have hlt : symbolCount x (x i) - 1 < symbolCount x (x i) :=
    Nat.sub_one_lt (Nat.ne_of_gt hpos)
  rw [hycount, hxcount] at hcount
  have hlt' : n / q - 1 < n / q := by
    simpa [hxcount] using hlt
  rw [← hcount] at hlt'
  exact lt_irrefl _ hlt'

/-- The live-coordinate perturbations of a fixed word in a support box. -/
noncomputable def liveCoordinateUnbalancedUpdates {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q) :
    Finset (Fin n → Fin q) :=
  (Finset.univ : Finset {i : Fin n // i ∈ liveCoordinates S}).image
    (fun i => Function.update x i.1 (liveCoordinateAlternative S x i.1 i.2))

lemma liveCoordinateUpdate_injective {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q) :
    Function.Injective
      (fun i : {i : Fin n // i ∈ liveCoordinates S} =>
        Function.update x i.1 (liveCoordinateAlternative S x i.1 i.2)) := by
  intro i j hij_update
  by_cases hij : i.1 = j.1
  · exact Subtype.ext hij
  · have hval : liveCoordinateAlternative S x i.1 i.2 = x i.1 := by
      have hcoord := congrFun hij_update i.1
      simpa [Function.update, hij] using hcoord
    exact False.elim ((liveCoordinateAlternative_ne S x i.2) hval)

@[simp] theorem card_liveCoordinateUnbalancedUpdates {n q : ℕ}
    (S : Fin n → Finset (Fin q)) (x : Fin n → Fin q) :
    (liveCoordinateUnbalancedUpdates S x).card = (liveCoordinates S).card := by
  classical
  unfold liveCoordinateUnbalancedUpdates
  rw [Finset.card_image_of_injective _ (liveCoordinateUpdate_injective S x)]
  simp

theorem liveCoordinateUnbalancedUpdates_subset_supportBoxWords {n q : ℕ}
    {S : Fin n → Finset (Fin q)} {x : Fin n → Fin q}
    (hxbox : x ∈ supportBoxWords n q S) :
    liveCoordinateUnbalancedUpdates S x ⊆ supportBoxWords n q S := by
  classical
  intro y hy
  rw [liveCoordinateUnbalancedUpdates] at hy
  rcases Finset.mem_image.mp hy with ⟨i, _hiuniv, rfl⟩
  exact supportBoxWords.update_mem hxbox i.1 (liveCoordinateAlternative_mem S x i.2)

theorem card_liveCoordinates_le_card_supportBoxWords_of_mem {n q : ℕ}
    {S : Fin n → Finset (Fin q)} {x : Fin n → Fin q}
    (hxbox : x ∈ supportBoxWords n q S) :
    (liveCoordinates S).card ≤ (supportBoxWords n q S).card := by
  classical
  let U := liveCoordinateUnbalancedUpdates S x
  have hUcard : U.card = (liveCoordinates S).card := by
    simp [U]
  calc
    (liveCoordinates S).card = U.card := hUcard.symm
    _ ≤ (supportBoxWords n q S).card :=
      Finset.card_le_card
        (liveCoordinateUnbalancedUpdates_subset_supportBoxWords
          (S := S) (x := x) hxbox)

theorem card_liveCoordinates_le_card_supportBoxWords_of_nonempty {n q : ℕ}
    {S : Fin n → Finset (Fin q)}
    (hbox : (supportBoxWords n q S).Nonempty) :
    (liveCoordinates S).card ≤ (supportBoxWords n q S).card := by
  rcases hbox with ⟨x, hxbox⟩
  exact card_liveCoordinates_le_card_supportBoxWords_of_mem (S := S) (x := x) hxbox

theorem liveCoordinateUnbalancedUpdates_subset_unbalancedWords {n q : ℕ}
    {S : Fin n → Finset (Fin q)} {x : Fin n → Fin q}
    (hxbal : x ∈ balancedWords n q) :
    liveCoordinateUnbalancedUpdates S x ⊆
      (Finset.univ.filter fun y : Fin n → Fin q => y ∉ balancedWords n q) := by
  classical
  intro y hy
  rw [liveCoordinateUnbalancedUpdates] at hy
  rcases Finset.mem_image.mp hy with ⟨i, _hiuniv, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨by simp,
      update_not_mem_balancedWords_of_ne hxbal i.1
        (liveCoordinateAlternative_ne S x i.2)⟩

theorem disjoint_balancedWords_inter_supportBox_liveCoordinateUnbalancedUpdates {n q : ℕ}
    {S : Fin n → Finset (Fin q)} {x : Fin n → Fin q}
    (hxbal : x ∈ balancedWords n q) :
    Disjoint ((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q)
      (liveCoordinateUnbalancedUpdates S x) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyA hyU
  rw [liveCoordinateUnbalancedUpdates] at hyU
  rcases Finset.mem_image.mp hyU with ⟨i, _hiuniv, rfl⟩
  exact
    (update_not_mem_balancedWords_of_ne hxbal i.1
      (liveCoordinateAlternative_ne S x i.2)) (Finset.mem_filter.mp hyA).2

/--
Finite quantitative obstruction: if a support box contains a balanced word, then
the number of balanced words in the box plus the number of live coordinates is
at most the size of the box.
-/
theorem card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox_of_mem
    {n q : ℕ} {S : Fin n → Finset (Fin q)} {x : Fin n → Fin q}
    (hxbox : x ∈ supportBoxWords n q S) (hxbal : x ∈ balancedWords n q) :
    ((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card +
        (liveCoordinates S).card ≤
      (supportBoxWords n q S).card := by
  classical
  let A := (supportBoxWords n q S).filter fun y => y ∈ balancedWords n q
  let U := liveCoordinateUnbalancedUpdates S x
  have hUcard : U.card = (liveCoordinates S).card := by
    simp [U]
  have hdisj : Disjoint A U := by
    simpa [A, U] using
      disjoint_balancedWords_inter_supportBox_liveCoordinateUnbalancedUpdates
        (S := S) (x := x) hxbal
  have hsub : A ∪ U ⊆ supportBoxWords n q S := by
    intro y hy
    rcases Finset.mem_union.mp hy with hyA | hyU
    · exact (Finset.mem_filter.mp hyA).1
    · exact
        (liveCoordinateUnbalancedUpdates_subset_supportBoxWords
          (S := S) (x := x) hxbox) hyU
  calc
    ((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card +
        (liveCoordinates S).card = A.card + U.card := by
          simp [A, hUcard]
    _ = (A ∪ U).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (supportBoxWords n q S).card := Finset.card_le_card hsub

theorem card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox_of_nonempty
    {n q : ℕ} {S : Fin n → Finset (Fin q)}
    (hbalancedBox :
      (((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).Nonempty)) :
    ((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card +
        (liveCoordinates S).card ≤
      (supportBoxWords n q S).card := by
  rcases hbalancedBox with ⟨x, hx⟩
  exact
    card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox_of_mem
      (S := S) (x := x) (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2

theorem card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox
    {n q : ℕ} {S : Fin n → Finset (Fin q)}
    (hbox : (supportBoxWords n q S).Nonempty) :
    ((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card +
        (liveCoordinates S).card ≤
      (supportBoxWords n q S).card := by
  classical
  let A := (supportBoxWords n q S).filter fun y => y ∈ balancedWords n q
  change A.card + (liveCoordinates S).card ≤ (supportBoxWords n q S).card
  by_cases hbalancedBox : A.Nonempty
  · simpa [A] using
      card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox_of_nonempty
        (S := S) hbalancedBox
  · have hAcard : A.card = 0 := by
      exact Nat.eq_zero_of_not_pos fun hpos => hbalancedBox (Finset.card_pos.mp hpos)
    have hLive :=
      card_liveCoordinates_le_card_supportBoxWords_of_nonempty (S := S) hbox
    simpa [hAcard] using hLive

theorem card_balancedWords_inter_supportBox_le_card_supportBox_sub_liveCoordinates_of_nonempty
    {n q : ℕ} {S : Fin n → Finset (Fin q)}
    (hbalancedBox :
      (((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).Nonempty)) :
    ((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card ≤
      (supportBoxWords n q S).card - (liveCoordinates S).card :=
  Nat.le_sub_of_add_le
    (card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox_of_nonempty
      (S := S) hbalancedBox)

/--
Rational-density form of the finite deficit:
`balanced_density ≤ 1 - live_coordinate_count / box_size`, whenever the box
contains a balanced word.
-/
theorem balancedWords_supportBox_density_le_one_sub_liveCoordinates_div_of_nonempty
    {n q : ℕ} {S : Fin n → Finset (Fin q)}
    (hbalancedBox :
      (((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).Nonempty)) :
    (((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card : ℚ) /
        (supportBoxWords n q S).card ≤
      1 - ((liveCoordinates S).card : ℚ) / (supportBoxWords n q S).card := by
  classical
  let A := (supportBoxWords n q S).filter fun y => y ∈ balancedWords n q
  let B := supportBoxWords n q S
  let L := liveCoordinates S
  change (A.card : ℚ) / (B.card : ℚ) ≤
    1 - (L.card : ℚ) / (B.card : ℚ)
  have hmain : A.card + L.card ≤ B.card := by
    simpa [A, B, L] using
      card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox_of_nonempty
        (S := S) hbalancedBox
  have hBpos_nat : 0 < B.card := by
    rcases hbalancedBox with ⟨x, hx⟩
    exact Finset.card_pos.mpr ⟨x, by simpa [B] using (Finset.mem_filter.mp hx).1⟩
  have hBpos_rat : (0 : ℚ) < (B.card : ℚ) := by
    exact_mod_cast hBpos_nat
  have hmain_rat : (A.card : ℚ) + (L.card : ℚ) ≤ (B.card : ℚ) := by
    exact_mod_cast hmain
  have hdiv : ((A.card : ℚ) + (L.card : ℚ)) / (B.card : ℚ) ≤ 1 := by
    rw [div_le_one hBpos_rat]
    exact hmain_rat
  have hsplit :
      ((A.card : ℚ) + (L.card : ℚ)) / (B.card : ℚ) =
        (A.card : ℚ) / (B.card : ℚ) + (L.card : ℚ) / (B.card : ℚ) := by
    ring
  rw [hsplit] at hdiv
  linarith

/--
Unconditional nonempty-box density form of the finite deficit:
`balanced_density ≤ 1 - live_coordinate_count / box_size`.
-/
theorem balancedWords_supportBox_density_le_one_sub_liveCoordinates_div
    {n q : ℕ} {S : Fin n → Finset (Fin q)}
    (hbox : (supportBoxWords n q S).Nonempty) :
    (((supportBoxWords n q S).filter fun y => y ∈ balancedWords n q).card : ℚ) /
        (supportBoxWords n q S).card ≤
      1 - ((liveCoordinates S).card : ℚ) / (supportBoxWords n q S).card := by
  classical
  let A := (supportBoxWords n q S).filter fun y => y ∈ balancedWords n q
  let B := supportBoxWords n q S
  let L := liveCoordinates S
  change (A.card : ℚ) / (B.card : ℚ) ≤
    1 - (L.card : ℚ) / (B.card : ℚ)
  have hmain : A.card + L.card ≤ B.card := by
    simpa [A, B, L] using
      card_balancedWords_inter_supportBox_add_liveCoordinates_le_card_supportBox
        (S := S) hbox
  have hBpos_nat : 0 < B.card := by
    exact Finset.card_pos.mpr (by simpa [B] using hbox)
  have hBpos_rat : (0 : ℚ) < (B.card : ℚ) := by
    exact_mod_cast hBpos_nat
  have hmain_rat : (A.card : ℚ) + (L.card : ℚ) ≤ (B.card : ℚ) := by
    exact_mod_cast hmain
  have hdiv : ((A.card : ℚ) + (L.card : ℚ)) / (B.card : ℚ) ≤ 1 := by
    rw [div_le_one hBpos_rat]
    exact hmain_rat
  have hsplit :
      ((A.card : ℚ) + (L.card : ℚ)) / (B.card : ℚ) =
        (A.card : ℚ) / (B.card : ℚ) + (L.card : ℚ) / (B.card : ℚ) := by
    ring
  rw [hsplit] at hdiv
  linarith

end FormalConjectures.Problems.Erdos.E20
