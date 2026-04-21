import FormalConjectures.Problems.Erdos.E20.Compendium.Models.CodeModels

open scoped BigOperators Pointwise
open Finset

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FormalConjectures.Problems.Erdos.E20.Compendium

noncomputable section

/-- All coordinatewise choices of `q` symbols from an alphabet of size `Q`. -/
def coordinateSubsetSelections (Q q m : ℕ) : Finset (Fin m → Finset (Fin Q)) :=
  Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Fin Q)).powersetCard q

@[simp] theorem mem_coordinateSubsetSelections_iff {Q q m : ℕ}
    {A : Fin m → Finset (Fin Q)} :
    A ∈ coordinateSubsetSelections Q q m ↔ ∀ j, (A j).card = q := by
  classical
  simp [coordinateSubsetSelections, Finset.mem_powersetCard]

@[simp] theorem coordinateSubsetSelections_card (Q q m : ℕ) :
    (coordinateSubsetSelections Q q m).card = (Q.choose q) ^ m := by
  classical
  simp [coordinateSubsetSelections, Finset.card_powersetCard]

private theorem powersetCard_univ_filter_mem_card
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) {q : ℕ} (hq : 0 < q) :
    (((Finset.univ : Finset α).powersetCard q).filter fun A => a ∈ A).card =
      (Fintype.card α - 1).choose (q - 1) := by
  classical
  have himage :
      (((Finset.univ : Finset α).powersetCard q).filter fun A => a ∈ A) =
        ((Finset.univ.erase a).powersetCard (q - 1)).image (fun B => insert a B) := by
    ext A
    constructor
    · intro hA
      rcases Finset.mem_filter.mp hA with ⟨hApow, haA⟩
      refine Finset.mem_image.mpr ⟨A.erase a, ?_, ?_⟩
      · refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro y hy
          exact by
            simpa [Finset.mem_erase] using (Finset.mem_erase.mp hy).1
        · have hcardA := (Finset.mem_powersetCard.mp hApow).2
          rw [Finset.card_erase_of_mem haA, hcardA]
      · rw [Finset.insert_erase haA]
    · intro hA
      rcases Finset.mem_image.mp hA with ⟨B, hB, hBA⟩
      rw [← hBA]
      refine Finset.mem_filter.mpr ⟨?_, by simp⟩
      refine Finset.mem_powersetCard.mpr ⟨by intro y hy; simp, ?_⟩
      have hBsub := (Finset.mem_powersetCard.mp hB).1
      have hBcard := (Finset.mem_powersetCard.mp hB).2
      have haB : a ∉ B := by
        intro ha
        have : a ∈ (Finset.univ : Finset α).erase a := hBsub ha
        exact (notMem_erase a (Finset.univ : Finset α)) this
      have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
      rw [Finset.card_insert_of_notMem haB, hBcard, hq1]
  rw [himage, Finset.card_image_of_injOn]
  · simp [Finset.card_powersetCard]
  · intro B hB D hD hBD
    have hBsub := (Finset.mem_powersetCard.mp hB).1
    have hDsub := (Finset.mem_powersetCard.mp hD).1
    have haB : a ∉ B := by
      intro ha
      have : a ∈ (Finset.univ : Finset α).erase a := hBsub ha
      exact (notMem_erase a (Finset.univ : Finset α)) this
    have haD : a ∉ D := by
      intro ha
      have : a ∈ (Finset.univ : Finset α).erase a := hDsub ha
      exact (notMem_erase a (Finset.univ : Finset α)) this
    change insert a B = insert a D at hBD
    calc
      B = (insert a B).erase a := (Finset.erase_insert haB).symm
      _ = (insert a D).erase a := by rw [hBD]
      _ = D := Finset.erase_insert haD

theorem qSubset_choices_containing_card {Q q : ℕ} (a : Fin Q) (hq : 0 < q) :
    (((Finset.univ : Finset (Fin Q)).powersetCard q).filter fun A => a ∈ A).card =
      (Q - 1).choose (q - 1) := by
  simpa using powersetCard_univ_filter_mem_card (a := a) (q := q) hq

theorem coordinateSubsetSelections_filter_containing_eq {Q q m : ℕ}
    (x : Fin m → Fin Q) :
    (coordinateSubsetSelections Q q m).filter (fun A => ∀ j, x j ∈ A j) =
      Fintype.piFinset fun j : Fin m =>
        ((Finset.univ : Finset (Fin Q)).powersetCard q).filter fun A => x j ∈ A := by
  classical
  ext A
  simp only [mem_filter, mem_coordinateSubsetSelections_iff, Fintype.mem_piFinset,
    mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨hcard, hmem⟩ j
    exact ⟨hcard j, hmem j⟩
  · intro h
    exact ⟨fun j => (h j).1, fun j => (h j).2⟩

theorem coordinateSubsetSelections_containing_card {Q q m : ℕ}
    (x : Fin m → Fin Q) (hq : 0 < q) :
    ((coordinateSubsetSelections Q q m).filter (fun A => ∀ j, x j ∈ A j)).card =
      ((Q - 1).choose (q - 1)) ^ m := by
  classical
  rw [coordinateSubsetSelections_filter_containing_eq]
  simp [qSubset_choices_containing_card, hq]

private theorem card_filter_eq_sum_ite {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Double-counting identity for coordinatewise `q`-subset deletion.  The left side sums survivor
counts over all selections, and the right side counts each original codeword with the number of
selections containing all of its coordinates. -/
theorem sum_coordinateSubsetSurvivors_card_eq {Q q m : ℕ}
    (C : Finset (Fin m → Fin Q)) (hq : 0 < q) :
    (∑ A ∈ coordinateSubsetSelections Q q m, (coordinateSubsetSurvivors C A).card) =
      C.card * ((Q - 1).choose (q - 1)) ^ m := by
  classical
  calc
    (∑ A ∈ coordinateSubsetSelections Q q m, (coordinateSubsetSurvivors C A).card)
        = ∑ A ∈ coordinateSubsetSelections Q q m,
            ∑ x ∈ C, if (∀ j, x j ∈ A j) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [coordinateSubsetSurvivors, card_filter_eq_sum_ite]
    _ = ∑ x ∈ C,
            ∑ A ∈ coordinateSubsetSelections Q q m,
              if (∀ j, x j ∈ A j) then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ((Q - 1).choose (q - 1)) ^ m := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← card_filter_eq_sum_ite]
          exact coordinateSubsetSelections_containing_card x hq
    _ = C.card * ((Q - 1).choose (q - 1)) ^ m :=
          Finset.sum_const_nat (s := C)
            (m := ((Q - 1).choose (q - 1)) ^ m)
            (f := fun _ => ((Q - 1).choose (q - 1)) ^ m)
            (by intro x hx; rfl)

/-- The deterministic deletion bound, summed over all coordinatewise choices. -/
theorem sum_coordinateSubsetSurvivors_card_le {Q q k m : ℕ}
    {C : Finset (Fin m → Fin Q)} (hfree : CodeModelFree Q k m C) :
    (∑ A ∈ coordinateSubsetSelections Q q m, (coordinateSubsetSurvivors C A).card) ≤
      (coordinateSubsetSelections Q q m).card * codeModelNumber q k m := by
  classical
  calc
    (∑ A ∈ coordinateSubsetSelections Q q m, (coordinateSubsetSurvivors C A).card)
        ≤ ∑ A ∈ coordinateSubsetSelections Q q m, codeModelNumber q k m := by
          apply Finset.sum_le_sum
          intro A hA
          exact coordinateSubset_survivor_card_le_codeModelNumber hfree A
            (mem_coordinateSubsetSelections_iff.mp hA)
    _ = (coordinateSubsetSelections Q q m).card * codeModelNumber q k m :=
          Finset.sum_const_nat (s := coordinateSubsetSelections Q q m)
            (m := codeModelNumber q k m)
            (f := fun _ => codeModelNumber q k m)
            (by intro A hA; rfl)

theorem randomizedDeletion_counting_inequality {Q q k m : ℕ}
    {C : Finset (Fin m → Fin Q)} (hfree : CodeModelFree Q k m C) (hq : 0 < q) :
    C.card * ((Q - 1).choose (q - 1)) ^ m ≤
      (Q.choose q) ^ m * codeModelNumber q k m := by
  calc
    C.card * ((Q - 1).choose (q - 1)) ^ m
        = ∑ A ∈ coordinateSubsetSelections Q q m,
            (coordinateSubsetSurvivors C A).card :=
          (sum_coordinateSubsetSurvivors_card_eq C hq).symm
    _ ≤ (coordinateSubsetSelections Q q m).card * codeModelNumber q k m :=
          sum_coordinateSubsetSurvivors_card_le hfree
    _ = (Q.choose q) ^ m * codeModelNumber q k m := by
          rw [coordinateSubsetSelections_card]

theorem choose_ratio_cast {Q q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    ((Q.choose q : ℚ) / (((Q - 1).choose (q - 1) : ℕ) : ℚ)) =
      (Q : ℚ) / (q : ℚ) := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hpred : q - 1 ≤ Q - 1 := Nat.sub_le_sub_right hqQ 1
  have hdenpos : 0 < (Q - 1).choose (q - 1) := Nat.choose_pos hpred
  have hden : (((Q - 1).choose (q - 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hdenpos.ne'
  have hqne : (q : ℚ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hnat := Nat.add_one_mul_choose_eq (Q - 1) (q - 1)
  have hnat' : Q * (Q - 1).choose (q - 1) = Q.choose q * q := by
    have hQ1 : Q - 1 + 1 = Q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hQ)
    have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
    simpa [hQ1, hq1] using hnat
  have hcast :
      (Q : ℚ) * (((Q - 1).choose (q - 1) : ℕ) : ℚ) =
        (Q.choose q : ℚ) * (q : ℚ) := by
    exact_mod_cast hnat'
  rw [div_eq_div_iff hden hqne]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcast.symm

/-- Per-code rational randomized-deletion inequality. -/
theorem randomizedDeletion_code_card_le_rat_of_le {Q q k m : ℕ}
    (hq : 0 < q) (hqQ : q ≤ Q) {C : Finset (Fin m → Fin Q)}
    (hfree : CodeModelFree Q k m C) :
    (C.card : ℚ) ≤
      (((Q : ℚ) / (q : ℚ)) ^ m) * (codeModelNumber q k m : ℚ) := by
  let A : ℕ := ((Q - 1).choose (q - 1)) ^ m
  let B : ℕ := (Q.choose q) ^ m
  let F : ℕ := codeModelNumber q k m
  have hnat : C.card * A ≤ B * F := by
    dsimp [A, B, F]
    exact randomizedDeletion_counting_inequality hfree hq
  have hApos_nat : 0 < A := by
    dsimp [A]
    exact pow_pos (Nat.choose_pos (Nat.sub_le_sub_right hqQ 1)) m
  have hApos : (0 : ℚ) < (A : ℚ) := by
    exact_mod_cast hApos_nat
  have hle_rat : (C.card : ℚ) * (A : ℚ) ≤ (B : ℚ) * (F : ℚ) := by
    exact_mod_cast hnat
  have hratio :
      (B : ℚ) / (A : ℚ) = ((Q : ℚ) / (q : ℚ)) ^ m := by
    dsimp [A, B]
    rw [Nat.cast_pow, Nat.cast_pow, ← div_pow, choose_ratio_cast hq hqQ]
  have htarget_mul :
      ((((Q : ℚ) / (q : ℚ)) ^ m) * (F : ℚ)) * (A : ℚ) = (B : ℚ) * (F : ℚ) := by
    calc
      ((((Q : ℚ) / (q : ℚ)) ^ m) * (F : ℚ)) * (A : ℚ)
          = (((B : ℚ) / (A : ℚ)) * (F : ℚ)) * (A : ℚ) := by
              rw [← hratio]
      _ = (B : ℚ) * (F : ℚ) := by
              field_simp [ne_of_gt hApos]
  have hle_target :
      (C.card : ℚ) * (A : ℚ) ≤
        ((((Q : ℚ) / (q : ℚ)) ^ m) * (F : ℚ)) * (A : ℚ) := by
    simpa [htarget_mul] using hle_rat
  have hcancel := (mul_le_mul_iff_of_pos_right hApos).mp hle_target
  simpa [F] using hcancel

theorem codeModelNumber_le_rat_of_code_bound {Q k m : ℕ} {R : ℚ}
    (hR : 0 ≤ R)
    (hbound : ∀ (C : Finset (Fin m → Fin Q)),
      CodeModelFree Q k m C → (C.card : ℚ) ≤ R) :
    (codeModelNumber Q k m : ℚ) ≤ R := by
  let S : Set ℕ := {c | ∃ (C : Finset (Fin m → Fin Q)),
    C.card = c ∧ CodeModelFree Q k m C}
  change ((sSup S : ℕ) : ℚ) ≤ R
  by_cases hne : S.Nonempty
  · have hmem : sSup S ∈ S := Nat.sSup_mem hne (codeModelNumber_bddAbove Q k m)
    rcases hmem with ⟨C, hCcard, hCfree⟩
    rw [← hCcard]
    exact hbound C hCfree
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hS, hR]

/-- General rational randomized-deletion lift from alphabet size `Q` down to `q`. -/
theorem randomizedDeletion_codeModelNumber_le_rat_of_le {Q q k m : ℕ}
    (hq : 0 < q) (hqQ : q ≤ Q) :
    (codeModelNumber Q k m : ℚ) ≤
      (((Q : ℚ) / (q : ℚ)) ^ m) * (codeModelNumber q k m : ℚ) := by
  apply codeModelNumber_le_rat_of_code_bound
  · exact mul_nonneg
      (pow_nonneg (div_nonneg (by positivity) (by positivity)) m)
      (by positivity)
  · intro C hfree
    exact randomizedDeletion_code_card_le_rat_of_le hq hqQ hfree

/-- The randomized-deletion averaging inequality in the form used for adding `t` symbols. -/
theorem randomizedDeletion_codeModelNumber_le_rat {q t k m : ℕ} (hq : 0 < q) :
    (codeModelNumber (q + t) k m : ℚ) ≤
      ((((q + t : ℕ) : ℚ) / (q : ℚ)) ^ m) * (codeModelNumber q k m : ℚ) :=
  randomizedDeletion_codeModelNumber_le_rat_of_le (Q := q + t) (q := q) (k := k) (m := m)
    hq (by omega)

/-- Real-valued form of `randomizedDeletion_codeModelNumber_le_rat`. -/
theorem randomizedDeletion_codeModelNumber_le_real {q t k m : ℕ} (hq : 0 < q) :
    (codeModelNumber (q + t) k m : ℝ) ≤
      ((((q + t : ℕ) : ℝ) / (q : ℝ)) ^ m) * (codeModelNumber q k m : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).2
    (randomizedDeletion_codeModelNumber_le_rat (q := q) (t := t) (k := k) (m := m) hq)
  simpa using h

end

end FormalConjectures.Problems.Erdos.E20.Compendium
