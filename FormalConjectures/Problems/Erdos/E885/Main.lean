/- 
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports
import FormalConjectures.Problems.Erdos.E885.Findings

/-!
# Erdős Problem 885

*References:*
- [erdosproblems.com/885](https://www.erdosproblems.com/885)
- [ErRo97] Erdős, P. and Rosenfeld, M., The factor-difference set of integers. (1997)
- [Ji99] Jiménez-Urroz, J., A note on a conjecture of Erdős and Rosenfeld. (1999)
- [Br19] Bremner, A., On a problem of Erdős related to common factor differences. (2019)
-/

open Nat Set Finset
open FormalConjectures

namespace Erdos885

/--
For integer `n ≥ 1` we define the factor difference set of `n` by
`D(n) = {|a - b| : n = a * b}`.
-/
abbrev factorDifferenceSet : ℕ → Set ℕ := factorDiffSet

lemma mem_factorDifferenceSet_lt_succ {d n : ℕ} (hd : d ∈ factorDifferenceSet n) : d < n + 1 := by
  rcases hd with ⟨a, b, ha, hb, hab, hdiff | hdiff⟩
  · have hn : 0 < n := by
      simpa [hab] using Nat.mul_pos ha hb
    have hb_le_n : b ≤ n := Nat.le_of_dvd hn ⟨a, by simpa [Nat.mul_comm] using hab.symm⟩
    have hd_le_b : d ≤ b := by
      rw [← hdiff]
      exact Nat.sub_le _ _
    exact Nat.lt_succ_of_le (hd_le_b.trans hb_le_n)
  · have hn : 0 < n := by
      simpa [hab] using Nat.mul_pos ha hb
    have ha_le_n : a ≤ n := Nat.le_of_dvd hn ⟨b, by simpa using hab.symm⟩
    have hd_le_a : d ≤ a := by
      rw [← hdiff]
      exact Nat.sub_le _ _
    exact Nat.lt_succ_of_le (hd_le_a.trans ha_le_n)

lemma factorDifferenceSet_finite (n : ℕ) : (factorDifferenceSet n).Finite := by
  refine (Set.finite_Iio (n + 1)).subset ?_
  intro d hd
  exact mem_factorDifferenceSet_lt_succ hd

lemma factorDifferenceSet_intersection_finite {Ns : Finset ℕ} {n : ℕ} (hn : n ∈ Ns) :
    (⋂ m ∈ Ns, factorDifferenceSet m).Finite := by
  refine (factorDifferenceSet_finite n).subset ?_
  intro d hd
  exact Set.mem_iInter₂.mp hd n hn

lemma finset_subset_ncard_le {s : Finset ℕ} {t : Set ℕ} (hst : (s : Set ℕ) ⊆ t) (ht : t.Finite) :
    s.card ≤ t.ncard := by
  simpa using (Set.ncard_le_ncard hst ht)

/--
Is it true that, for every `k ≥ 1`, there exist integers `N₁ < ... < N_k` such that
`|⋂ i, D(Nᵢ)| ≥ k`?
-/
@[category research open_problem, AMS 11]
theorem erdos_885 : answer(sorry) ↔ ∀ k ≥ 1,
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k := by
  sorry

namespace variants

/--
Erdős and Rosenfeld [ErRo97] proved this is true for `k = 2`.
-/
@[category research solved, AMS 11]
theorem k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  refine ⟨{12, 42}, ?_, by simp, ?_⟩
  · intro n hn
    simp at hn
    omega
  · let I : Set ℕ := ⋂ n ∈ ({12, 42} : Finset ℕ), factorDifferenceSet n
    have hI_finite : I.Finite := by
      simpa [I] using
        (factorDifferenceSet_intersection_finite (Ns := ({12, 42} : Finset ℕ)) (n := 12) (by simp))
    have hsubset : (({1, 11} : Finset ℕ) : Set ℕ) ⊆ I := by
      intro d hd
      have hd' : d = 1 ∨ d = 11 := by
        simpa using hd
      rcases hd' with rfl | rfl
      · simp [I, factorDifferenceSet, one_mem_factorDiffSet_12, one_mem_factorDiffSet_42]
      · simp [I, factorDifferenceSet, eleven_mem_factorDiffSet_12, eleven_mem_factorDiffSet_42]
    have hcard : ({1, 11} : Finset ℕ).card ≤ I.ncard := finset_subset_ncard_le hsubset hI_finite
    simpa [I] using hcard

/--
Jiménez-Urroz [Ji99] proved this for `k = 3`.
-/
@[category research solved, AMS 11]
theorem k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  refine ⟨{112, 952, 3240}, ?_, by simp, ?_⟩
  · intro n hn
    simp at hn
    omega
  · let I : Set ℕ := ⋂ n ∈ ({112, 952, 3240} : Finset ℕ), factorDifferenceSet n
    have hI_finite : I.Finite := by
      simpa [I] using
        (factorDifferenceSet_intersection_finite
          (Ns := ({112, 952, 3240} : Finset ℕ)) (n := 112) (by simp))
    have hsubset : (({6, 54, 111} : Finset ℕ) : Set ℕ) ⊆ I := by
      intro d hd
      have hd' : d = 6 ∨ d = 54 ∨ d = 111 := by
        simpa [or_assoc] using hd
      rcases hd' with rfl | rfl | rfl
      · simp [I, factorDifferenceSet,
          six_mem_factorDiffSet_112, six_mem_factorDiffSet_952, six_mem_factorDiffSet_3240]
      · simp [I, factorDifferenceSet,
          fiftyfour_mem_factorDiffSet_112, fiftyfour_mem_factorDiffSet_952,
          fiftyfour_mem_factorDiffSet_3240]
      · simp [I, factorDifferenceSet,
          oneonone_mem_factorDiffSet_112, oneonone_mem_factorDiffSet_952,
          oneonone_mem_factorDiffSet_3240]
    have hcard : ({6, 54, 111} : Finset ℕ).card ≤ I.ncard := by
      exact finset_subset_ncard_le hsubset hI_finite
    simpa [I] using hcard

/--
Current strongest explicit witness in this repository: a triple with four common
factor differences.

This is not the literature `k = 4` theorem, which is cited above but not yet
formalized in this repo.
-/
@[category research partial_result, AMS 11]
theorem three_by_four_configuration :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨{13608, 29848, 65968}, ?_, by simp, ?_⟩
  · intro n hn
    simp at hn
    omega
  · let I : Set ℕ := ⋂ n ∈ ({13608, 29848, 65968} : Finset ℕ), factorDifferenceSet n
    have hI_finite : I.Finite := by
      simpa [I] using
        (factorDifferenceSet_intersection_finite
          (Ns := ({13608, 29848, 65968} : Finset ℕ)) (n := 13608) (by simp))
    have hsubset : (({18, 282, 477, 1122} : Finset ℕ) : Set ℕ) ⊆ I := by
      intro d hd
      have hd' : d = 18 ∨ d = 282 ∨ d = 477 ∨ d = 1122 := by
        simpa [or_assoc] using hd
      rcases hd' with rfl | rfl | rfl | rfl
      · simp [I, factorDifferenceSet,
          eighteen_mem_factorDiffSet_13608, eighteen_mem_factorDiffSet_29848,
          eighteen_mem_factorDiffSet_65968]
      · simp [I, factorDifferenceSet,
          twoeightytwo_mem_factorDiffSet_13608, twoeightytwo_mem_factorDiffSet_29848,
          twoeightytwo_mem_factorDiffSet_65968]
      · simp [I, factorDifferenceSet,
          foursevenseven_mem_factorDiffSet_13608, foursevenseven_mem_factorDiffSet_29848,
          foursevenseven_mem_factorDiffSet_65968]
      · simp [I, factorDifferenceSet,
          oneonetwotwo_mem_factorDiffSet_13608, oneonetwotwo_mem_factorDiffSet_29848,
          oneonetwotwo_mem_factorDiffSet_65968]
    have hcard : ({18, 282, 477, 1122} : Finset ℕ).card ≤ I.ncard :=
      finset_subset_ncard_le hsubset hI_finite
    simpa [I] using hcard

end variants
end Erdos885
