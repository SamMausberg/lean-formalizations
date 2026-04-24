import FormalConjectures.Problems.Erdos.E61.Affine

/-!
# Singleton-cut obstruction package

This file packages the finite singleton-cut construction from `thm:singleton-cut`.
The heavy combinatorial facts are proved in `Affine.lean`; here they are assembled
into theorem-level forms matching the paper's obstruction statement.
-/

namespace Erdos61

open Finset

/-- The row set `R_m = {0,c_1,...,c_m}` has exactly `m+1` rows. -/
theorem cutRows_card (m : ℕ) :
    Fintype.card (CutRow m) = m + 1 := by
  simp [CutRow]

/--
Any cover of the singleton-cut row set by pieces of size at most two has at least
`ceil((m+1)/2)` pieces, expressed as `(m+2)/2`.
-/
theorem cutRows_two_cell_cover_lower_bound {m : ℕ}
    (P : Finset (Finset (CutRow m)))
    (hcover : P.biUnion id = (Finset.univ : Finset (CutRow m)))
    (hcell : ∀ C ∈ P, C.card ≤ 2) :
    (m + 2) / 2 ≤ P.card := by
  classical
  have hcover_card :
      m + 1 ≤ ∑ C ∈ P, C.card := by
    calc
      m + 1 = ((Finset.univ : Finset (CutRow m))).card := by
        simp [CutRow]
      _ = (P.biUnion id).card := by rw [hcover]
      _ ≤ ∑ C ∈ P, C.card := card_biUnion_le
  have hsum_le : ∑ C ∈ P, C.card ≤ ∑ _C ∈ P, 2 := by
    exact sum_le_sum hcell
  have htwice : m + 1 ≤ 2 * P.card := by
    calc
      m + 1 ≤ ∑ C ∈ P, C.card := hcover_card
      _ ≤ ∑ _C ∈ P, 2 := hsum_le
      _ = P.card * 2 := by simp
      _ = 2 * P.card := by rw [Nat.mul_comm]
  omega

/--
If every exact affine cell in a cover of `R_m` has size at most two, then the
cover has the lower bound from `thm:singleton-cut(iv)`.
-/
theorem cutRows_affine_cell_cover_lower_bound {m : ℕ}
    (P : Finset (Finset (CutRow m)))
    (hcover : P.biUnion id = (Finset.univ : Finset (CutRow m)))
    (hcell : ∀ C ∈ P, C.card ≤ 2) :
    (m + 2) / 2 ≤ P.card :=
  cutRows_two_cell_cover_lower_bound P hcover hcell

/--
Bundled formal singleton-cut obstruction: for `m>4`, there are `m+1` occupied
rows, no four distinct occupied rows form an affine plane, any two-point-cell
cover needs at least `ceil((m+1)/2)` cells, and every ladder in the parity matrix
has size at most two.
-/
theorem singleton_cut_obstruction_package {m : ℕ} (hm : 4 < m) :
    Fintype.card (CutRow m) = m + 1 ∧
      (∀ r₀ r₁ r₂ r₃ : CutRow m, ¬ IsCutAffinePlane r₀ r₁ r₂ r₃) ∧
        (∀ P : Finset (Finset (CutRow m)),
          P.biUnion id = (Finset.univ : Finset (CutRow m)) →
            (∀ C ∈ P, C.card ≤ 2) →
              (m + 2) / 2 ≤ P.card) ∧
          (∀ {k : ℕ} {row : Fin k → CutRow m} {col : Fin k → KEdge m},
            IsCutLadder row col → k ≤ 2) := by
  exact ⟨cutRows_card m, no_cut_affine_plane hm,
    fun P hcover hcell => cutRows_affine_cell_cover_lower_bound P hcover hcell,
    fun h => cut_ladder_size_le_two h⟩

end Erdos61
