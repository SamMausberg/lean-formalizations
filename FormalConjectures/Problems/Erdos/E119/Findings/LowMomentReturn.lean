import Mathlib

/-!
# Erdős 119 Findings: Finite-State Return Step

This file formalizes the finite pigeonhole step behind the low-moment return decomposition
from the user-supplied source note.
-/

namespace Erdos119
namespace Findings

/--
Formalizes the repeated-cell pigeonhole step from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 8 ("Low-moment return decomposition"), Theorem A:
if `P + 1` prefix states are quantized into at most `P` cells, then two distinct
prefix indices land in the same cell.
-/
theorem exists_repeated_cell_of_card_le {β : Type*} [Fintype β] {P : ℕ}
    (hβ : Fintype.card β ≤ P) (f : Fin (P + 1) → β) :
    ∃ a b : Fin (P + 1), a < b ∧ f a = f b := by
  have hlt : Fintype.card β < Fintype.card (Fin (P + 1)) := by
    simpa using Nat.lt_succ_of_le hβ
  obtain ⟨x, y, hxy, hmap⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  rcases lt_or_gt_of_ne hxy with hltxy | hltyx
  · exact ⟨x, y, hltxy, hmap⟩
  · exact ⟨y, x, hltyx, hmap.symm⟩

end Findings
end Erdos119
