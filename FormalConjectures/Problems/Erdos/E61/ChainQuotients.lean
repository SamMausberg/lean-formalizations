import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Chain-interface quotient obstruction

This file formalizes the finite row-distinguishing core of
`prop:chain-quotients`: in the chain bipartite interface, every two left-side
vertices have different neighborhoods, so any side-respecting homogeneous
quotient must keep all left rows distinct.
-/

namespace Erdos61

/-- The chain bipartite relation: left row `i` is adjacent to right column `j` iff `j ≤ i`. -/
def chainRel {m : ℕ} (i j : Fin m) : Prop :=
  j ≤ i

/-- Raw directed relation for the chain bipartite graph. -/
def chainBipartiteRel (m : ℕ) : Sum (Fin m) (Fin m) → Sum (Fin m) (Fin m) → Prop
  | Sum.inl i, Sum.inr j => chainRel i j
  | _, _ => False

/-- The finite chain bipartite graph. -/
def chainBipartiteGraph (m : ℕ) : SimpleGraph (Sum (Fin m) (Fin m)) :=
  SimpleGraph.fromRel (chainBipartiteRel m)

@[simp] theorem chainBipartite_adj_left_right {m : ℕ} (i j : Fin m) :
    (chainBipartiteGraph m).Adj (Sum.inl i) (Sum.inr j) ↔ j ≤ i := by
  simp [chainBipartiteGraph, chainBipartiteRel, chainRel, SimpleGraph.fromRel_adj]

@[simp] theorem chainBipartite_adj_right_left {m : ℕ} (i j : Fin m) :
    (chainBipartiteGraph m).Adj (Sum.inr j) (Sum.inl i) ↔ j ≤ i := by
  rw [(chainBipartiteGraph m).adj_comm]
  simp

@[simp] theorem chainBipartite_not_adj_left_left {m : ℕ} (i j : Fin m) :
    ¬ (chainBipartiteGraph m).Adj (Sum.inl i) (Sum.inl j) := by
  simp [chainBipartiteGraph, chainBipartiteRel, SimpleGraph.fromRel_adj]

@[simp] theorem chainBipartite_not_adj_right_right {m : ℕ} (i j : Fin m) :
    ¬ (chainBipartiteGraph m).Adj (Sum.inr i) (Sum.inr j) := by
  simp [chainBipartiteGraph, chainBipartiteRel, SimpleGraph.fromRel_adj]

/--
If `i < j`, the right vertex `j` distinguishes the two left rows: it is
adjacent to row `j` and not to row `i`.
-/
theorem chain_left_rows_distinguished {m : ℕ} {i j : Fin m} (hij : i < j) :
    (chainBipartiteGraph m).Adj (Sum.inl j) (Sum.inr j) ∧
      ¬ (chainBipartiteGraph m).Adj (Sum.inl i) (Sum.inr j) := by
  constructor
  · simp
  · simpa using not_le_of_gt hij

/--
Any quotient map on the left side whose classes have identical right
neighborhoods is injective.
-/
theorem chain_left_quotient_injective {m : ℕ} {κ : Type*} {q : Fin m → κ}
    (hhom : ∀ i j : Fin m, q i = q j → ∀ b : Fin m,
      (chainRel i b ↔ chainRel j b)) :
    Function.Injective q := by
  intro i j hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hsame := hhom i j hq j
    have hfalse : ¬ chainRel i j := not_le_of_gt hij
    exact hfalse (hsame.mpr le_rfl)
  · have hsame := hhom j i hq.symm i
    have hfalse : ¬ chainRel j i := not_le_of_gt hji
    exact hfalse (hsame.mpr le_rfl)

/-- Consequently, such a side-respecting homogeneous quotient has at least `m` left classes. -/
theorem chain_left_quotient_card_ge {m : ℕ} {κ : Type*} [Fintype κ] {q : Fin m → κ}
    (hhom : ∀ i j : Fin m, q i = q j → ∀ b : Fin m,
      (chainRel i b ↔ chainRel j b)) :
    m ≤ Fintype.card κ := by
  rw [← Fintype.card_fin m]
  exact Fintype.card_le_of_injective q (chain_left_quotient_injective hhom)

end Erdos61
