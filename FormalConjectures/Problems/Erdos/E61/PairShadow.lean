import FormalConjectures.Problems.Erdos.E61.Cutpoint

/-!
# Determinate pair-shadow extraction

This file formalizes a finite ordered core of `prop:determinate-pair-shadow`.
Once a pair-shadow value is determined for every ordered pair that has enough
room to be completed to the chosen tuple positions, a regularly spaced
subsequence is pure for that value.
-/

namespace Erdos61

open Finset

/-- Indices spaced by `g` unused positions after deleting `r` initial positions. -/
def pairShadowSubsequence (r g M : ℕ) : Finset ℕ :=
  (range M).image fun k => r + k * (g + 1)

theorem pairShadowSubsequence_card (r g M : ℕ) :
    (pairShadowSubsequence r g M).card = M := by
  classical
  unfold pairShadowSubsequence
  rw [card_image_of_injOn]
  · simp
  · intro k _hk l _hl hkl
    have hmul : k * (g + 1) = l * (g + 1) := Nat.add_left_cancel hkl
    exact Nat.mul_right_cancel (Nat.succ_pos g) hmul

theorem mem_pairShadowSubsequence_iff {r g M y : ℕ} :
    y ∈ pairShadowSubsequence r g M ↔ ∃ k < M, y = r + k * (g + 1) := by
  classical
  constructor
  · intro hy
    rcases mem_image.mp hy with ⟨k, hk, hky⟩
    exact ⟨k, mem_range.mp hk, hky.symm⟩
  · rintro ⟨k, hkM, rfl⟩
    exact mem_image.mpr ⟨k, mem_range.mpr hkM, rfl⟩

theorem pairShadowSubsequence_lt_bound {r g s M N y : ℕ}
    (hy : y ∈ pairShadowSubsequence r g M)
    (hroom : M = 0 ∨ r + (M - 1) * (g + 1) + s < N) :
    y + s < N := by
  rcases mem_pairShadowSubsequence_iff.mp hy with ⟨k, hkM, rfl⟩
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le k) hkM
  have hk_le : k ≤ M - 1 := by omega
  have hmul_le : k * (g + 1) ≤ (M - 1) * (g + 1) := Nat.mul_le_mul_right _ hk_le
  have hroom' : r + (M - 1) * (g + 1) + s < N := by
    rcases hroom with hzero | hlt
    · omega
    · exact hlt
  omega

theorem pairShadowSubsequence_gap {r g M a b : ℕ}
    (ha : a ∈ pairShadowSubsequence r g M) (hb : b ∈ pairShadowSubsequence r g M)
    (hab : a < b) :
    r ≤ a ∧ a + g < b := by
  rcases mem_pairShadowSubsequence_iff.mp ha with ⟨ka, _hkaM, rfl⟩
  rcases mem_pairShadowSubsequence_iff.mp hb with ⟨kb, _hkbM, hb_eq⟩
  subst b
  have hka_lt_kb : ka < kb := by
    by_contra hnot
    have hkb_le : kb ≤ ka := Nat.le_of_not_gt hnot
    have hmul_le : kb * (g + 1) ≤ ka * (g + 1) := Nat.mul_le_mul_right _ hkb_le
    omega
  constructor
  · omega
  · have hstep : ka * (g + 1) + g < (ka + 1) * (g + 1) := by
      nlinarith [Nat.succ_pos g]
    have hle : (ka + 1) * (g + 1) ≤ kb * (g + 1) := by
      exact Nat.mul_le_mul_right _ hka_lt_kb
    omega

/--
Finite determinate pair-shadow extraction.

If every pair of indices that can be completed with `r` earlier, `g` middle,
and `s` later vertices has Boolean value `e`, then a regularly spaced
subsequence is pure for that value.
-/
theorem determinate_pair_shadow_spaced_subsequence
    (E : ℕ → ℕ → Bool) (e : Bool) {r g s M N : ℕ}
    (hdet : ∀ a b, a < b → r ≤ a → a + g < b → b + s < N → E a b = e)
    (hroom : M = 0 ∨ r + (M - 1) * (g + 1) + s < N) :
    ∃ Y : Finset ℕ, Y.card = M ∧ (∀ y ∈ Y, y < N) ∧
      ∀ a ∈ Y, ∀ b ∈ Y, a < b → E a b = e := by
  refine ⟨pairShadowSubsequence r g M, pairShadowSubsequence_card r g M, ?_, ?_⟩
  · intro y hy
    have hy_bound := pairShadowSubsequence_lt_bound (s := s) (N := N) hy hroom
    omega
  · intro a ha b hb hab
    have hgap := pairShadowSubsequence_gap ha hb hab
    exact hdet a b hab hgap.1 hgap.2 (pairShadowSubsequence_lt_bound hb hroom)

end Erdos61
