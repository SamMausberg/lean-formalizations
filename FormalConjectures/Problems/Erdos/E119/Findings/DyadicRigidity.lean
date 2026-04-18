import FormalConjectures.Problems.Erdos.E119.Findings.Defs

/-!
# Erdős 119 Findings: Dyadic Rigidity Bounds

This file isolates the exact finite-set inequalities behind the additive affine-rank theorem
from the user-supplied source note.
-/

open scoped BigOperators symmDiff

namespace Erdos119
namespace Findings

/--
Formalizes the bound `|C_j \setminus G_j| ≤ D_j` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 1, equation `(4)`, in its abstract finite-set form:
if two sets of size `n` have intersection of size at least `n - D`, then at most `D`
elements of the first set lie outside the second.
-/
theorem card_sdiff_le_of_card_inter_ge {α : Type*} [DecidableEq α] {s t : Finset α} {n D : ℕ}
    (hs : s.card = n) (hinter : n - D ≤ (s ∩ t).card) : (s \ t).card ≤ D := by
  have hcard : (s \ t).card = n - (s ∩ t).card := by
    rw [Finset.card_sdiff, hs, Finset.inter_comm]
  have hinter_le : (s ∩ t).card ≤ n := by
    rw [← hs]
    exact Finset.card_le_card Finset.inter_subset_left
  rw [hcard]
  omega

/--
Formalizes the bound `|C_j △ R_j| ≤ 2 D_j` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 1, equation `(3)`, in its abstract finite-set form.
-/
theorem card_symmDiff_le_twice_of_card_inter_ge {α : Type*} [DecidableEq α]
    {s t : Finset α} {n D : ℕ}
    (hs : s.card = n) (ht : t.card = n) (hinter : n - D ≤ (s ∩ t).card) :
    (s ∆ t).card ≤ 2 * D := by
  have hsle : (s \ t).card ≤ D := card_sdiff_le_of_card_inter_ge hs hinter
  have hinter' : n - D ≤ (t ∩ s).card := by
    simpa [Finset.inter_comm] using hinter
  have htle : (t \ s).card ≤ D := card_sdiff_le_of_card_inter_ge ht hinter'
  have hsymm :
      s ∆ t = (s \ t) ∪ (t \ s) := by
    ext x
    simp [Finset.mem_symmDiff]
  have hdisj : Disjoint (s \ t) (t \ s) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  calc
    (s ∆ t).card = ((s \ t) ∪ (t \ s)).card := by simp [hsymm]
    _ = (s \ t).card + (t \ s).card := by
          rw [Finset.card_union_of_disjoint]
          exact hdisj
    _ ≤ D + D := by omega
    _ = 2 * D := by omega

end Findings
end Erdos119
