import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Computations

/-!
# Rigidity of the Guidepost `3 × 4` Seed

This file formalizes the exact finite rigidity computation for the seed triple
`(79200, 227205, 1258560)` discussed in the notes.

The main outputs are:

* the exact factor-pair sum image `Σ(148005)`,
* the exact factor-pair difference image `Δ(1031355)`,
* their four-point intersection `{954, 1062, 1178, 1402}`, and
* the exact common factor-difference set
  `D(79200) ∩ D(227205) ∩ D(1258560) = {36, 468, 692, 1028}`.

In particular, the known `3 × 4` seed is rigid: it has exactly four common
positive secants, so there is no fifth common secant for this row triple.
-/

open Finset

namespace Erdos885
namespace GuidepostRigidity

/-- The first row value of the guidepost seed. -/
def guidepostRowA : ℕ := 79200

/-- The second row value of the guidepost seed. -/
def guidepostRowB : ℕ := 227205

/-- The third row value of the guidepost seed. -/
def guidepostRowC : ℕ := 1258560

/-- The first row gap `227205 - 79200 = 148005`. -/
def guidepostGapA : ℕ := guidepostRowB - guidepostRowA

/-- The second row gap `1258560 - 227205 = 1031355`. -/
def guidepostGapB : ℕ := guidepostRowC - guidepostRowB

theorem guidepostGapA_value : guidepostGapA = 148005 := by
  native_decide

theorem guidepostGapB_value : guidepostGapB = 1031355 := by
  native_decide

/-- The finite sum image `Σ(N) = {d + e : d e = N, d < e}`. -/
def sigmaImage (N : ℕ) : Finset ℕ :=
  ((Nat.divisors N).filter fun d => d < N / d).image fun d => d + N / d

/-- The finite difference image `Δ(N) = {e - d : d e = N, d < e}`. -/
def deltaImage (N : ℕ) : Finset ℕ :=
  ((Nat.divisors N).filter fun d => d < N / d).image fun d => N / d - d

/-- The explicit sum image `Σ(148005)`. -/
def guidepostSigma : Finset ℕ := sigmaImage guidepostGapA

/-- The explicit difference image `Δ(1031355)`. -/
def guidepostDelta : Finset ℕ := deltaImage guidepostGapB

/-- The four middle values surviving the factor-pair sieve. -/
def guidepostMiddleValues : Finset ℕ := guidepostSigma ∩ guidepostDelta

/-- The secants obtained by the square test `d² = m² - 4b` on the four middle
values. -/
def guidepostSquareSecants : Finset ℕ :=
  guidepostMiddleValues.image fun m => Nat.sqrt (m * m - 4 * guidepostRowB)

/-- The common factor-differences of the guidepost seed, enumerated up to the
four surviving middle values. -/
def guidepostCommonSecants : Finset ℕ :=
  guidepostSquareSecants

set_option linter.style.nativeDecide false in
  theorem guidepostSigma_eq :
    guidepostSigma =
      {774, 794, 838, 922, 954, 1062, 1178, 1382, 1402, 1594, 2214, 2342, 2746,
        3334, 3834, 4518, 6458, 9882, 11398, 13466, 16454, 29606, 49338, 148006} := by
  native_decide

set_option linter.style.nativeDecide false in
  theorem guidepostDelta_eq :
    guidepostDelta =
      {954, 1062, 1178, 1286, 1402, 2278, 2426, 4582, 4826, 5094, 7866, 8262, 8698,
        15802, 22874, 23942, 25114, 26406, 68742, 79322, 114586, 206266, 343782,
        1031354} := by
  native_decide

set_option linter.style.nativeDecide false in
theorem guidepostMiddleValues_eq :
    guidepostMiddleValues = {954, 1062, 1178, 1402} := by
  native_decide

theorem guidepostSquareTest_954 :
    954 ^ 2 - 4 * guidepostRowB = 36 ^ 2 := by
  norm_num [guidepostRowB]

theorem guidepostSquareTest_1062 :
    1062 ^ 2 - 4 * guidepostRowB = 468 ^ 2 := by
  norm_num [guidepostRowB]

theorem guidepostSquareTest_1178 :
    1178 ^ 2 - 4 * guidepostRowB = 692 ^ 2 := by
  norm_num [guidepostRowB]

theorem guidepostSquareTest_1402 :
    1402 ^ 2 - 4 * guidepostRowB = 1028 ^ 2 := by
  norm_num [guidepostRowB]

set_option linter.style.nativeDecide false in
theorem guidepostSquareSecants_eq :
    guidepostSquareSecants = {36, 468, 692, 1028} := by
  native_decide

theorem guidepostCommonSecants_eq :
    guidepostCommonSecants = {36, 468, 692, 1028} := by
  simpa [guidepostCommonSecants] using guidepostSquareSecants_eq

/-- A positive factor-difference is always strictly smaller than the
underlying integer. -/
theorem mem_factorDiffSet_lt {d n : ℕ} (hd : d ∈ factorDiffSet n) : d < n := by
  rcases hd with ⟨a, b, ha, hb, hab, h | h⟩
  · have h1a : 1 ≤ a := Nat.succ_le_of_lt ha
    have hb_le_n : b ≤ n := by
      calc
        b = 1 * b := by simp
        _ ≤ a * b := by
          simpa [Nat.mul_comm] using (Nat.mul_le_mul_right b h1a)
        _ = n := hab
    have hd_lt_b : d < b := by
      rw [← h]
      exact Nat.sub_lt hb ha
    exact lt_of_lt_of_le hd_lt_b hb_le_n
  · have h1b : 1 ≤ b := Nat.succ_le_of_lt hb
    have ha_le_n : a ≤ n := by
      calc
        a = a * 1 := by simp
        _ ≤ a * b := by
          simpa using (Nat.mul_le_mul_left a h1b)
        _ = n := hab
    have hd_lt_a : d < a := by
      rw [← h]
      exact Nat.sub_lt ha hb
    exact lt_of_lt_of_le hd_lt_a ha_le_n

/-- Any positive factor-difference can be oriented as `n = r (r + d)` with
`r > 0`. -/
theorem oriented_factor_pair_of_factorDiff {d n : ℕ} (hdpos : 0 < d) (hd : d ∈ factorDiffSet n) :
    ∃ r : ℕ, 0 < r ∧ n = r * (r + d) := by
  rcases hd with ⟨a, b, ha, hb, hab, h | h⟩
  · refine ⟨a, ha, ?_⟩
    have hb_eq : b = a + d := by omega
    calc
      n = a * b := hab.symm
      _ = a * (a + d) := by rw [hb_eq]
  · refine ⟨b, hb, ?_⟩
    have ha_eq : a = b + d := by omega
    calc
      n = a * b := hab.symm
      _ = b * (b + d) := by rw [ha_eq]; ring

/-- A common secant of the guidepost triple yields a middle value in the exact
finite divisor matrix `Σ(148005) ∩ Δ(1031355)`. -/
theorem guidepost_middle_value_of_common_secant {d : ℕ}
    (hdpos : 0 < d)
    (hdA : d ∈ factorDiffSet guidepostRowA)
    (hdB : d ∈ factorDiffSet guidepostRowB)
    (hdC : d ∈ factorDiffSet guidepostRowC) :
    ∃ m : ℕ, m ∈ guidepostMiddleValues ∧ m * m = d * d + 4 * guidepostRowB := by
  obtain ⟨r, hr, har⟩ := oriented_factor_pair_of_factorDiff hdpos hdA
  obtain ⟨s, hs, hbs⟩ := oriented_factor_pair_of_factorDiff hdpos hdB
  obtain ⟨t, ht, hct⟩ := oriented_factor_pair_of_factorDiff hdpos hdC
  have hrs : r < s := by
    by_contra hrs'
    have hsr : s ≤ r := Nat.le_of_not_gt hrs'
    have hba : guidepostRowB ≤ guidepostRowA := by
      nlinarith [har, hbs, hsr]
    have hab_rows : guidepostRowA < guidepostRowB := by native_decide
    omega
  have hst : s < t := by
    by_contra hst'
    have hts : t ≤ s := Nat.le_of_not_gt hst'
    have hcb : guidepostRowC ≤ guidepostRowB := by
      nlinarith [hbs, hct, hts]
    have hbc_rows : guidepostRowB < guidepostRowC := by native_decide
    omega
  let m := 2 * s + d
  have hAfac : guidepostGapA = (s - r) * (s + r + d) := by
    have hs : s = r + (s - r) := by omega
    have hsum :
        guidepostGapA + guidepostRowA = (s - r) * (s + r + d) + guidepostRowA := by
      calc
        guidepostGapA + guidepostRowA = guidepostRowB := by native_decide
        _ = s * (s + d) := hbs
        _ = (s - r) * (s + r + d) + r * (r + d) := by
              rw [hs]
              rw [Nat.add_sub_cancel_left r (s - r)]
              ring_nf
        _ = (s - r) * (s + r + d) + guidepostRowA := by rw [har]
    exact Nat.add_right_cancel hsum
  have hBfac : guidepostGapB = (t - s) * (t + s + d) := by
    have ht' : t = s + (t - s) := by omega
    have hsum :
        guidepostGapB + guidepostRowB = (t - s) * (t + s + d) + guidepostRowB := by
      calc
        guidepostGapB + guidepostRowB = guidepostRowC := by native_decide
        _ = t * (t + d) := hct
        _ = (t - s) * (t + s + d) + s * (s + d) := by
              rw [ht']
              rw [Nat.add_sub_cancel_left s (t - s)]
              ring_nf
        _ = (t - s) * (t + s + d) + guidepostRowB := by rw [hbs]
    exact Nat.add_right_cancel hsum
  have hmSigma : m ∈ guidepostSigma := by
    unfold guidepostSigma sigmaImage
    refine Finset.mem_image.mpr ?_
    refine ⟨s - r, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨by rw [hAfac]; exact dvd_mul_right (s - r) (s + r + d),
          by native_decide⟩
      · rw [hAfac, Nat.mul_div_right _ (Nat.sub_pos_of_lt hrs)]
        omega
    · rw [hAfac, Nat.mul_div_right _ (Nat.sub_pos_of_lt hrs)]
      simp [m]
      omega
  have hmDelta : m ∈ guidepostDelta := by
    unfold guidepostDelta deltaImage
    refine Finset.mem_image.mpr ?_
    refine ⟨t - s, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨by rw [hBfac]; exact dvd_mul_right (t - s) (t + s + d),
          by native_decide⟩
      · rw [hBfac, Nat.mul_div_right _ (Nat.sub_pos_of_lt hst)]
        omega
    · rw [hBfac, Nat.mul_div_right _ (Nat.sub_pos_of_lt hst)]
      simp [m]
      omega
  refine ⟨m, Finset.mem_inter.mpr ⟨hmSigma, hmDelta⟩, ?_⟩
  dsimp [m]
  nlinarith [hbs]

theorem guidepost_36_mem_factorDiffSet_A : 36 ∈ factorDiffSet guidepostRowA := by
  refine ⟨264, 300, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowA]

theorem guidepost_36_mem_factorDiffSet_B : 36 ∈ factorDiffSet guidepostRowB := by
  refine ⟨459, 495, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowB]

theorem guidepost_36_mem_factorDiffSet_C : 36 ∈ factorDiffSet guidepostRowC := by
  refine ⟨1104, 1140, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowC]

theorem guidepost_468_mem_factorDiffSet_A : 468 ∈ factorDiffSet guidepostRowA := by
  refine ⟨132, 600, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowA]

theorem guidepost_468_mem_factorDiffSet_B : 468 ∈ factorDiffSet guidepostRowB := by
  refine ⟨297, 765, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowB]

theorem guidepost_468_mem_factorDiffSet_C : 468 ∈ factorDiffSet guidepostRowC := by
  refine ⟨912, 1380, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowC]

theorem guidepost_692_mem_factorDiffSet_A : 692 ∈ factorDiffSet guidepostRowA := by
  refine ⟨100, 792, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowA]

theorem guidepost_692_mem_factorDiffSet_B : 692 ∈ factorDiffSet guidepostRowB := by
  refine ⟨243, 935, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowB]

theorem guidepost_692_mem_factorDiffSet_C : 692 ∈ factorDiffSet guidepostRowC := by
  refine ⟨828, 1520, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowC]

theorem guidepost_1028_mem_factorDiffSet_A : 1028 ∈ factorDiffSet guidepostRowA := by
  refine ⟨72, 1100, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowA]

theorem guidepost_1028_mem_factorDiffSet_B : 1028 ∈ factorDiffSet guidepostRowB := by
  refine ⟨187, 1215, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowB]

theorem guidepost_1028_mem_factorDiffSet_C : 1028 ∈ factorDiffSet guidepostRowC := by
  refine ⟨720, 1748, by decide, by decide, ?_, ?_⟩ <;> norm_num [guidepostRowC]

theorem guidepost_positive_common_factorDiffSet_iff {d : ℕ} :
    0 < d →
      (d ∈ factorDiffSet guidepostRowA ∩ factorDiffSet guidepostRowB ∩ factorDiffSet guidepostRowC ↔
      d = 36 ∨ d = 468 ∨ d = 692 ∨ d = 1028) := by
  intro hdpos
  constructor
  · intro hd
    rcases hd with ⟨hdAB, hdC⟩
    rcases hdAB with ⟨hdA, hdB⟩
    obtain ⟨m, hm, hmSq⟩ :=
      guidepost_middle_value_of_common_secant hdpos hdA hdB hdC
    rw [guidepostMiddleValues_eq] at hm
    simp at hm
    rcases hm with rfl | rfl | rfl | rfl
    · left
      have h954 : 954 * 954 = 36 * 36 + 4 * guidepostRowB := by
        norm_num [guidepostRowB]
      have hd2 : d * d = 36 * 36 := by
        nlinarith [hmSq, h954]
      have hsqrt : d = Nat.sqrt (36 * 36) := by
        simpa [Nat.sqrt_eq] using congrArg Nat.sqrt hd2
      norm_num at hsqrt
      exact hsqrt
    · right; left
      have h954 : 1062 * 1062 = 468 * 468 + 4 * guidepostRowB := by
        norm_num [guidepostRowB]
      have hd2 : d * d = 468 * 468 := by
        nlinarith [hmSq, h954]
      have hsqrt : d = Nat.sqrt (468 * 468) := by
        simpa [Nat.sqrt_eq] using congrArg Nat.sqrt hd2
      norm_num at hsqrt
      exact hsqrt
    · right; right; left
      have h954 : 1178 * 1178 = 692 * 692 + 4 * guidepostRowB := by
        norm_num [guidepostRowB]
      have hd2 : d * d = 692 * 692 := by
        nlinarith [hmSq, h954]
      have hsqrt : d = Nat.sqrt (692 * 692) := by
        simpa [Nat.sqrt_eq] using congrArg Nat.sqrt hd2
      norm_num at hsqrt
      exact hsqrt
    · right; right; right
      have h954 : 1402 * 1402 = 1028 * 1028 + 4 * guidepostRowB := by
        norm_num [guidepostRowB]
      have hd2 : d * d = 1028 * 1028 := by
        nlinarith [hmSq, h954]
      have hsqrt : d = Nat.sqrt (1028 * 1028) := by
        simpa [Nat.sqrt_eq] using congrArg Nat.sqrt hd2
      norm_num at hsqrt
      exact hsqrt
  · intro hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨⟨guidepost_36_mem_factorDiffSet_A, guidepost_36_mem_factorDiffSet_B⟩,
        guidepost_36_mem_factorDiffSet_C⟩
    · exact ⟨⟨guidepost_468_mem_factorDiffSet_A, guidepost_468_mem_factorDiffSet_B⟩,
        guidepost_468_mem_factorDiffSet_C⟩
    · exact ⟨⟨guidepost_692_mem_factorDiffSet_A, guidepost_692_mem_factorDiffSet_B⟩,
        guidepost_692_mem_factorDiffSet_C⟩
    · exact ⟨⟨guidepost_1028_mem_factorDiffSet_A, guidepost_1028_mem_factorDiffSet_B⟩,
        guidepost_1028_mem_factorDiffSet_C⟩

theorem guidepostCommonSecants_card : guidepostCommonSecants.card = 4 := by
  rw [guidepostCommonSecants_eq]
  native_decide

theorem guidepost_seed_rigid :
    guidepostCommonSecants = {36, 468, 692, 1028} ∧ guidepostCommonSecants.card = 4 := by
  exact ⟨guidepostCommonSecants_eq, guidepostCommonSecants_card⟩

end GuidepostRigidity
end Erdos885
