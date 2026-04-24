import FormalConjectures.Problems.Erdos.E61.Alternation
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# A local `C5` semantic obstruction

This file formalizes the finite construction in `prop:C5-semantic`.
The graph has a distinguished vertex `x`, an independent side `P`, and a clique
side `Q`; `x` sees exactly `P`, and the cross matrix from `P` to `Q` is
complete.  The neighborhood word of `x` alternates along the displayed order,
but the graph has no induced `C5`.
-/

open Finset

namespace Erdos61

/-- Vertex type for the `C5` semantic obstruction: `none` is `x`, left is `P`,
and right is `Q`. -/
abbrev C5SemanticVertex (m : ℕ) := Option (Sum (Fin m) (Fin m))

/-- The distinguished vertex `x`. -/
def c5x {m : ℕ} : C5SemanticVertex m := none

/-- The independent side `P`. -/
def c5p {m : ℕ} (i : Fin m) : C5SemanticVertex m := some (Sum.inl i)

/-- The clique side `Q`. -/
def c5q {m : ℕ} (i : Fin m) : C5SemanticVertex m := some (Sum.inr i)

/-- Raw symmetric adjacency relation for `c5SemanticGraph`. -/
def c5SemanticAdj {m : ℕ} : C5SemanticVertex m → C5SemanticVertex m → Prop
  | none, some (Sum.inl _) => True
  | some (Sum.inl _), none => True
  | some (Sum.inl _), some (Sum.inr _) => True
  | some (Sum.inr _), some (Sum.inl _) => True
  | some (Sum.inr i), some (Sum.inr j) => i ≠ j
  | _, _ => False

theorem c5SemanticAdj_symm {m : ℕ} : Symmetric (c5SemanticAdj (m := m)) := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => simp [c5SemanticAdj] at h
      | some s => cases s <;> simp [c5SemanticAdj] at h ⊢
  | some s =>
      cases s with
      | inl _ =>
          cases b with
          | none => simp [c5SemanticAdj]
          | some t => cases t <;> simp [c5SemanticAdj] at h ⊢
      | inr _ =>
          cases b with
          | none => simp [c5SemanticAdj] at h
          | some t =>
              cases t with
              | inl _ => simp [c5SemanticAdj]
              | inr _ =>
                  change _ ≠ _
                  intro hji
                  exact h hji.symm

theorem c5SemanticAdj_loopless {m : ℕ} : Std.Irrefl (c5SemanticAdj (m := m)) := by
  constructor
  intro a h
  cases a with
  | none => simp [c5SemanticAdj] at h
  | some s => cases s <;> simp [c5SemanticAdj] at h

/--
The split-like graph from the `C5` semantic obstruction: `P` is independent,
`Q` is a clique, `P` is complete to `Q`, and `x` sees exactly `P`.
-/
def c5SemanticGraph (m : ℕ) : SimpleGraph (C5SemanticVertex m) where
  Adj := c5SemanticAdj
  symm := c5SemanticAdj_symm
  loopless := c5SemanticAdj_loopless

@[simp] theorem c5Semantic_adj_x_p {m : ℕ} (i : Fin m) :
    (c5SemanticGraph m).Adj c5x (c5p i) := by
  simp [c5SemanticGraph, c5SemanticAdj, c5x, c5p]

@[simp] theorem c5Semantic_not_adj_x_q {m : ℕ} (i : Fin m) :
    ¬ (c5SemanticGraph m).Adj c5x (c5q i) := by
  simp [c5SemanticGraph, c5SemanticAdj, c5x, c5q]

@[simp] theorem c5Semantic_not_adj_p_p {m : ℕ} (i j : Fin m) :
    ¬ (c5SemanticGraph m).Adj (c5p i) (c5p j) := by
  simp [c5SemanticGraph, c5SemanticAdj, c5p]

@[simp] theorem c5Semantic_adj_p_q {m : ℕ} (i j : Fin m) :
    (c5SemanticGraph m).Adj (c5p i) (c5q j) := by
  simp [c5SemanticGraph, c5SemanticAdj, c5p, c5q]

@[simp] theorem c5Semantic_adj_q_q {m : ℕ} (i j : Fin m) :
    (c5SemanticGraph m).Adj (c5q i) (c5q j) ↔ i ≠ j := by
  simp [c5SemanticGraph, c5SemanticAdj, c5q]

@[simp] theorem c5Semantic_adj_x_iff {m : ℕ} (v : C5SemanticVertex m) :
    (c5SemanticGraph m).Adj c5x v ↔ ∃ i, v = c5p i := by
  cases v with
  | none => simp [c5SemanticGraph, c5x, c5p]
  | some s => cases s <;> simp [c5SemanticGraph, c5SemanticAdj, c5x, c5p]

@[simp] theorem c5Semantic_nonadj_x_iff {m : ℕ} (v : C5SemanticVertex m) :
    ¬ (c5SemanticGraph m).Adj c5x v ↔ v = c5x ∨ ∃ i, v = c5q i := by
  cases v with
  | none => simp [c5SemanticGraph, c5x, c5q]
  | some s => cases s <;> simp [c5SemanticGraph, c5SemanticAdj, c5x, c5q]

@[simp] theorem c5Semantic_adj_p_iff {m : ℕ} (i : Fin m) (v : C5SemanticVertex m) :
    (c5SemanticGraph m).Adj (c5p i) v ↔ v = c5x ∨ ∃ j, v = c5q j := by
  cases v with
  | none => simp [c5SemanticGraph, c5SemanticAdj, c5x, c5p, c5q]
  | some s => cases s <;> simp [c5SemanticGraph, c5SemanticAdj, c5x, c5p, c5q]

@[simp] theorem c5Semantic_nonadj_p_iff {m : ℕ} (i : Fin m) (v : C5SemanticVertex m) :
    ¬ (c5SemanticGraph m).Adj (c5p i) v ↔ ∃ j, v = c5p j := by
  cases v with
  | none => simp [c5SemanticGraph, c5SemanticAdj, c5p]
  | some s => cases s <;> simp [c5SemanticGraph, c5SemanticAdj, c5p]

@[simp] theorem c5Semantic_nonadj_q_iff {m : ℕ} (i : Fin m) (v : C5SemanticVertex m) :
    ¬ (c5SemanticGraph m).Adj (c5q i) v ↔ v = c5x ∨ v = c5q i := by
  cases v with
  | none => simp [c5SemanticGraph, c5SemanticAdj, c5x, c5q]
  | some s =>
      cases s with
      | inl _ => simp [c5SemanticGraph, c5SemanticAdj, c5x, c5q]
      | inr _ => simp [c5SemanticGraph, c5SemanticAdj, c5x, c5q, eq_comm]

/-- The `P` side as a finite set. -/
def c5PSet (m : ℕ) : Finset (C5SemanticVertex m) :=
  univ.image fun i : Fin m => c5p i

/-- The `Q` side as a finite set. -/
def c5QSet (m : ℕ) : Finset (C5SemanticVertex m) :=
  univ.image fun i : Fin m => c5q i

theorem c5Semantic_x_complete_to_P (m : ℕ) :
    CompleteTo (fun u v => (c5SemanticGraph m).Adj u v) {c5x} (c5PSet m) := by
  intro u hu v hv
  rw [mem_singleton] at hu
  rcases mem_image.mp hv with ⟨i, _hi, rfl⟩
  subst u
  exact c5Semantic_adj_x_p i

theorem c5Semantic_x_anticomplete_to_Q (m : ℕ) :
    Anticomplete (fun u v => (c5SemanticGraph m).Adj u v) {c5x} (c5QSet m) := by
  intro u hu v hv
  rw [mem_singleton] at hu
  rcases mem_image.mp hv with ⟨i, _hi, rfl⟩
  subst u
  exact c5Semantic_not_adj_x_q i

theorem c5Semantic_P_complete_to_Q (m : ℕ) :
    CompleteTo (fun u v => (c5SemanticGraph m).Adj u v) (c5PSet m) (c5QSet m) := by
  intro u hu v hv
  rcases mem_image.mp hu with ⟨i, _hi, rfl⟩
  rcases mem_image.mp hv with ⟨j, _hj, rfl⟩
  exact c5Semantic_adj_p_q i j

/-- The alternating neighborhood word of `x` in the order
`p₁,q₁,p₂,q₂,...`. -/
def c5SemanticOrderWord : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: false :: c5SemanticOrderWord m

@[simp] theorem c5SemanticOrderWord_zero : c5SemanticOrderWord 0 = [] := rfl

@[simp] theorem c5SemanticOrderWord_succ (m : ℕ) :
    c5SemanticOrderWord (m + 1) = true :: false :: c5SemanticOrderWord m := rfl

theorem c5SemanticOrderWord_change_count (m : ℕ) :
    boolChangeCount (c5SemanticOrderWord m) = 2 * m - 1 := by
  induction m with
  | zero => simp [boolChangeCount, boolChangeFlags]
  | succ m ih =>
      cases m with
      | zero => simp [boolChangeCount, boolChangeFlags]
      | succ m =>
          have hflags : boolChangeFlags (c5SemanticOrderWord (m + 2)) =
              true :: true :: boolChangeFlags (c5SemanticOrderWord (m + 1)) := by
            simp [c5SemanticOrderWord, boolChangeFlags]
          rw [boolChangeCount, hflags]
          simp [boolChangeCount] at ih ⊢
          omega

theorem c5Semantic_side_patterns {m : ℕ} (hm : 2 ≤ m) :
    (∃ u ∈ c5PSet m, ∃ v ∈ c5PSet m,
        u ≠ v ∧ ¬ (c5SemanticGraph m).Adj u v) ∧
      ∃ u ∈ c5QSet m, ∃ v ∈ c5QSet m,
        u ≠ v ∧ (c5SemanticGraph m).Adj u v := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  constructor
  · refine ⟨c5p i0, ?_, c5p i1, ?_, ?_, ?_⟩
    · exact mem_image.mpr ⟨i0, mem_univ i0, rfl⟩
    · exact mem_image.mpr ⟨i1, mem_univ i1, rfl⟩
    · intro h
      exact h01 (by simpa [c5p] using h)
    · exact c5Semantic_not_adj_p_p i0 i1
  · refine ⟨c5q i0, ?_, c5q i1, ?_, ?_, ?_⟩
    · exact mem_image.mpr ⟨i0, mem_univ i0, rfl⟩
    · exact mem_image.mpr ⟨i1, mem_univ i1, rfl⟩
    · intro h
      exact h01 (by simpa [c5q] using h)
    · simpa using (c5Semantic_adj_q_q (m := m) i0 i1).mpr h01

private theorem c5_edge_01 :
    (SimpleGraph.cycleGraph 5).Adj (0 : Fin 5) (1 : Fin 5) := by decide

private theorem c5_edge_23 :
    (SimpleGraph.cycleGraph 5).Adj (2 : Fin 5) (3 : Fin 5) := by decide

private theorem c5_nonedge_02 :
    ¬ (SimpleGraph.cycleGraph 5).Adj (0 : Fin 5) (2 : Fin 5) := by decide

private theorem c5_nonedge_03 :
    ¬ (SimpleGraph.cycleGraph 5).Adj (0 : Fin 5) (3 : Fin 5) := by decide

private theorem c5_nonedge_13 :
    ¬ (SimpleGraph.cycleGraph 5).Adj (1 : Fin 5) (3 : Fin 5) := by decide

/-- The obstruction graph contains no induced `C5`. -/
theorem c5SemanticGraph_no_induced_c5 (m : ℕ) :
    ¬ SimpleGraph.IsIndContained (SimpleGraph.cycleGraph 5) (c5SemanticGraph m) := by
  rintro ⟨φ⟩
  have h01 : (c5SemanticGraph m).Adj (φ (0 : Fin 5)) (φ (1 : Fin 5)) :=
    (φ.map_adj_iff).mpr c5_edge_01
  have h23 : (c5SemanticGraph m).Adj (φ (2 : Fin 5)) (φ (3 : Fin 5)) :=
    (φ.map_adj_iff).mpr c5_edge_23
  have hn02 : ¬ (c5SemanticGraph m).Adj (φ (0 : Fin 5)) (φ (2 : Fin 5)) := by
    intro h
    exact c5_nonedge_02 ((φ.map_adj_iff).mp h)
  have hn03 : ¬ (c5SemanticGraph m).Adj (φ (0 : Fin 5)) (φ (3 : Fin 5)) := by
    intro h
    exact c5_nonedge_03 ((φ.map_adj_iff).mp h)
  have hn13 : ¬ (c5SemanticGraph m).Adj (φ (1 : Fin 5)) (φ (3 : Fin 5)) := by
    intro h
    exact c5_nonedge_13 ((φ.map_adj_iff).mp h)
  cases hφ0 : φ (0 : Fin 5) with
  | none =>
      have h1p : ∃ i, φ (1 : Fin 5) = c5p i := by
        exact (c5Semantic_adj_x_iff (m := m) (φ (1 : Fin 5))).mp
          (by simpa [c5x, hφ0] using h01)
      have h3q : ∃ i, φ (3 : Fin 5) = c5q i := by
        have hnon : ¬ (c5SemanticGraph m).Adj c5x (φ (3 : Fin 5)) := by
          intro h
          exact hn03 (by simpa [c5x, hφ0] using h)
        rcases (c5Semantic_nonadj_x_iff (m := m) (φ (3 : Fin 5))).mp hnon with
          h3x | h3q
        · exfalso
          have h30 : φ (3 : Fin 5) = φ (0 : Fin 5) := by
            simpa [c5x, hφ0] using h3x
          have hneq : (3 : Fin 5) ≠ (0 : Fin 5) := by decide
          exact hneq ((RelEmbedding.inj φ).mp h30)
        · exact h3q
      rcases h1p with ⟨p1, hp1⟩
      rcases h3q with ⟨q3, hq3⟩
      exact hn13 (by simp [hp1, hq3])
  | some s =>
      cases s with
      | inl p0 =>
          have h2p : ∃ i, φ (2 : Fin 5) = c5p i := by
            have hnon : ¬ (c5SemanticGraph m).Adj (c5p p0) (φ (2 : Fin 5)) := by
              intro h
              exact hn02 (by simpa [c5p, hφ0] using h)
            exact (c5Semantic_nonadj_p_iff (m := m) p0 (φ (2 : Fin 5))).mp hnon
          have h3p : ∃ i, φ (3 : Fin 5) = c5p i := by
            have hnon : ¬ (c5SemanticGraph m).Adj (c5p p0) (φ (3 : Fin 5)) := by
              intro h
              exact hn03 (by simpa [c5p, hφ0] using h)
            exact (c5Semantic_nonadj_p_iff (m := m) p0 (φ (3 : Fin 5))).mp hnon
          rcases h2p with ⟨p2, hp2⟩
          rcases h3p with ⟨p3, hp3⟩
          have hnot23 : ¬ (c5SemanticGraph m).Adj (φ (2 : Fin 5)) (φ (3 : Fin 5)) := by
            simpa [hp2, hp3] using c5Semantic_not_adj_p_p (m := m) p2 p3
          exact hnot23 h23
      | inr q0 =>
          have h2x : φ (2 : Fin 5) = c5x := by
            have hnon : ¬ (c5SemanticGraph m).Adj (c5q q0) (φ (2 : Fin 5)) := by
              intro h
              exact hn02 (by simpa [c5q, hφ0] using h)
            rcases (c5Semantic_nonadj_q_iff (m := m) q0 (φ (2 : Fin 5))).mp hnon with
              h2x | h2q
            · exact h2x
            · exfalso
              have h20 : φ (2 : Fin 5) = φ (0 : Fin 5) := by
                simpa [c5q, hφ0] using h2q
              have hneq : (2 : Fin 5) ≠ (0 : Fin 5) := by decide
              exact hneq ((RelEmbedding.inj φ).mp h20)
          have h3x : φ (3 : Fin 5) = c5x := by
            have hnon : ¬ (c5SemanticGraph m).Adj (c5q q0) (φ (3 : Fin 5)) := by
              intro h
              exact hn03 (by simpa [c5q, hφ0] using h)
            rcases (c5Semantic_nonadj_q_iff (m := m) q0 (φ (3 : Fin 5))).mp hnon with
              h3x | h3q
            · exact h3x
            · exfalso
              have h30 : φ (3 : Fin 5) = φ (0 : Fin 5) := by
                simpa [c5q, hφ0] using h3q
              have hneq : (3 : Fin 5) ≠ (0 : Fin 5) := by decide
              exact hneq ((RelEmbedding.inj φ).mp h30)
          have h23eq : φ (2 : Fin 5) = φ (3 : Fin 5) := h2x.trans h3x.symm
          have hneq23 : (2 : Fin 5) ≠ (3 : Fin 5) := by decide
          exact hneq23 ((RelEmbedding.inj φ).mp h23eq)

/--
Bundled finite form of `prop:C5-semantic`: for `m ≥ 2`, the construction is
induced-`C5`-free, the neighborhood word of `x` has `2m-1` adjacent changes,
both same-side patterns exist, and the cross matrix from `P` to `Q` is complete.
-/
theorem c5_semantic_obstruction (m : ℕ) (hm : 2 ≤ m) :
    ¬ SimpleGraph.IsIndContained (SimpleGraph.cycleGraph 5) (c5SemanticGraph m) ∧
      boolChangeCount (c5SemanticOrderWord m) = 2 * m - 1 ∧
      ((∃ u ∈ c5PSet m, ∃ v ∈ c5PSet m,
          u ≠ v ∧ ¬ (c5SemanticGraph m).Adj u v) ∧
        ∃ u ∈ c5QSet m, ∃ v ∈ c5QSet m,
          u ≠ v ∧ (c5SemanticGraph m).Adj u v) ∧
      CompleteTo (fun u v => (c5SemanticGraph m).Adj u v) (c5PSet m) (c5QSet m) := by
  exact ⟨c5SemanticGraph_no_induced_c5 m, c5SemanticOrderWord_change_count m,
    c5Semantic_side_patterns hm, c5Semantic_P_complete_to_Q m⟩

end Erdos61
