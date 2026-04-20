import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Correlation

open Finset BigOperators
open scoped Classical

namespace FormalConjectures
namespace Problems
namespace Erdos
namespace E20

variable {α : Type*} [DecidableEq α]

/-- A finite family of finite sets is pairwise disjoint when distinct members are disjoint.

This is the formal matching predicate used in the bounded-overlap kernel lemmas that correspond
to the informal statements about matching number and kernels. -/
def PairwiseDisjointFamily (M : Finset (Finset α)) : Prop :=
  ∀ ⦃e f : Finset α⦄, e ∈ M → f ∈ M → e ≠ f → Disjoint e f

/-- `M` is a maximal matching inside `J`: it is a pairwise-disjoint subfamily of `J`, and every
edge of `J` meets some edge of `M`.

This is the finite witness version of the informal matching-number language used in the kernel
bounds. -/
structure IsMaximalMatchingIn (J M : Finset (Finset α)) : Prop where
  subset : M ⊆ J
  pairwiseDisjoint : PairwiseDisjointFamily M
  meets_every_edge : ∀ ⦃e : Finset α⦄, e ∈ J → ∃ m ∈ M, ¬ Disjoint e m

/-- The set of edges of `J` other than `e` that meet `e`.

This formalizes the "other petals met by a petal" quantity from the informal bounded-overlap
kernel theorem. -/
def edgeOverlapSet (J : Finset (Finset α)) (e : Finset α) : Finset (Finset α) :=
  (J.erase e).filter fun f => ¬ Disjoint e f

/-- Every edge of `J` meets at most `D` other edges.

This is the formal bounded-overlap hypothesis from the informal theorem
`|J| ≤ (D + 1) ν(J)`. -/
def MaxEdgeOverlapAtMost (J : Finset (Finset α)) (D : Nat) : Prop :=
  ∀ ⦃e : Finset α⦄, e ∈ J → (edgeOverlapSet J e).card ≤ D

/-- Every ground vertex lies in at most `Δ` edges of `J`.

This is the formal bounded-vertex-degree hypothesis from the informal theorem
`|J| ≤ ((Δ - 1) s + 1) ν(J)` for `s`-uniform kernels. -/
def MaxVertexDegreeAtMost (J : Finset (Finset α)) (Δ : Nat) : Prop :=
  ∀ x : α, vertexDegree' J x ≤ Δ

lemma mem_edgeOverlapSet_iff {J : Finset (Finset α)} {e f : Finset α} :
    f ∈ edgeOverlapSet J e ↔ f ∈ J ∧ f ≠ e ∧ ¬ Disjoint e f := by
  unfold edgeOverlapSet
  simp [and_left_comm, and_assoc]

lemma self_not_mem_edgeOverlapSet {J : Finset (Finset α)} {e : Finset α} :
    e ∉ edgeOverlapSet J e := by
  simp [mem_edgeOverlapSet_iff]

lemma meetingFilter_subset_insert_overlap
    {J : Finset (Finset α)} {m : Finset α} (hmJ : m ∈ J) :
    (J.filter fun e => ¬ Disjoint e m) ⊆ insert m (edgeOverlapSet J m) := by
  intro e he
  rcases mem_filter.mp he with ⟨heJ, hmeet⟩
  by_cases hem : e = m
  · exact mem_insert.mpr (Or.inl hem)
  · have hmeet' : ¬ Disjoint m e := by
      intro h
      exact hmeet h.symm
    exact mem_insert.mpr <| Or.inr <| by
      exact (mem_edgeOverlapSet_iff).2 ⟨heJ, hem, hmeet'⟩

lemma card_meetingFilter_le_overlap_succ
    {J : Finset (Finset α)} {m : Finset α} (hmJ : m ∈ J) :
    (J.filter fun e => ¬ Disjoint e m).card ≤ (edgeOverlapSet J m).card + 1 := by
  calc
    (J.filter fun e => ¬ Disjoint e m).card ≤ (insert m (edgeOverlapSet J m)).card := by
      exact card_le_card (meetingFilter_subset_insert_overlap hmJ)
    _ = (edgeOverlapSet J m).card + 1 := by
      simp [self_not_mem_edgeOverlapSet]

/-- If `M` is a maximal matching in `J` and every edge of `J` meets at most `D` other edges, then
`|J| ≤ (D + 1) |M|`.

This is the formal maximal-matching version of the informal bounded-overlap kernel inequality
`|J| ≤ (D + 1) ν(J)`. -/
theorem card_le_overlap_bound_of_maximalMatching
    {J M : Finset (Finset α)} {D : Nat}
    (hM : IsMaximalMatchingIn J M) (hD : MaxEdgeOverlapAtMost J D) :
    J.card ≤ (D + 1) * M.card := by
  classical
  have hcover :
      J ⊆ M.biUnion (fun m => J.filter fun e => ¬ Disjoint e m) := by
    intro e heJ
    rcases hM.meets_every_edge heJ with ⟨m, hmM, hmeet⟩
    exact mem_biUnion.mpr ⟨m, hmM, mem_filter.mpr ⟨heJ, hmeet⟩⟩
  calc
    J.card ≤ (M.biUnion fun m => J.filter fun e => ¬ Disjoint e m).card := by
      exact card_le_card hcover
    _ ≤ ∑ m ∈ M, (J.filter fun e => ¬ Disjoint e m).card := by
      exact card_biUnion_le
    _ ≤ ∑ m ∈ M, (D + 1) := by
      refine sum_le_sum ?_
      intro m hmM
      calc
        (J.filter fun e => ¬ Disjoint e m).card ≤ (edgeOverlapSet J m).card + 1 :=
          card_meetingFilter_le_overlap_succ (hM.subset hmM)
        _ ≤ D + 1 := by
          exact Nat.add_le_add_right (hD (hM.subset hmM)) 1
    _ = (D + 1) * M.card := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

lemma filter_eq_insert_eraseFilter_of_mem
    {J : Finset (Finset α)} {e : Finset α} {x : α}
    (heJ : e ∈ J) (hx : x ∈ e) :
    J.filter (fun f => x ∈ f) = insert e ((J.erase e).filter fun f => x ∈ f) := by
  ext f
  by_cases hfe : f = e
  · subst hfe
    simp [heJ, hx]
  · simp [hfe, heJ, hx]

lemma card_eraseFilter_mem_le_degree_pred
    {J : Finset (Finset α)} {e : Finset α} {x : α} {Δ : Nat}
    (heJ : e ∈ J) (hx : x ∈ e) (hΔ : MaxVertexDegreeAtMost J Δ) :
    ((J.erase e).filter fun f => x ∈ f).card ≤ Δ - 1 := by
  have hdegree_eq :
      vertexDegree' J x = ((J.erase e).filter fun f => x ∈ f).card + 1 := by
    unfold vertexDegree'
    rw [filter_eq_insert_eraseFilter_of_mem heJ hx]
    simp
  have hbound := hΔ x
  omega

lemma edgeOverlapSet_subset_vertexWitnessUnion
    {J : Finset (Finset α)} {e : Finset α} :
    edgeOverlapSet J e ⊆ e.biUnion (fun x => (J.erase e).filter fun f => x ∈ f) := by
  intro f hf
  rcases (mem_edgeOverlapSet_iff).1 hf with ⟨hfJ, hfe, hmeet⟩
  rcases not_disjoint_iff.mp hmeet with ⟨x, hxE, hxF⟩
  exact mem_biUnion.mpr ⟨x, hxE, by simp [hfJ, hfe, hxF]⟩

/-- In an `s`-uniform family of maximum vertex degree `Δ`, each edge meets at most
`s (Δ - 1)` other edges.

This is the formal local counting lemma behind the informal bounded-degree kernel inequality. -/
theorem edgeOverlapSet_card_le_uniform_degree
    {J : Finset (Finset α)} {s Δ : Nat}
    (huniform : IsRUniform J s) (hΔ : MaxVertexDegreeAtMost J Δ)
    {e : Finset α} (heJ : e ∈ J) :
    (edgeOverlapSet J e).card ≤ s * (Δ - 1) := by
  classical
  calc
    (edgeOverlapSet J e).card
        ≤ (e.biUnion fun x => (J.erase e).filter fun f => x ∈ f).card := by
          exact card_le_card edgeOverlapSet_subset_vertexWitnessUnion
    _ ≤ ∑ x ∈ e, ((J.erase e).filter fun f => x ∈ f).card := by
      exact card_biUnion_le
    _ ≤ ∑ _x ∈ e, (Δ - 1) := by
      refine sum_le_sum ?_
      intro x hx
      exact card_eraseFilter_mem_le_degree_pred heJ hx hΔ
    _ = e.card * (Δ - 1) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ = s * (Δ - 1) := by
      rw [huniform e heJ]

/-- If `M` is a maximal matching in an `s`-uniform family `J` of maximum vertex degree `Δ`, then
`|J| ≤ ((Δ - 1) s + 1) |M|`.

This is the formal maximal-matching version of the informal bounded-degree kernel inequality
`|J| ≤ ((Δ - 1) s + 1) ν(J)`. -/
theorem card_le_vertexDegree_bound_of_maximalMatching
    {J M : Finset (Finset α)} {s Δ : Nat}
    (huniform : IsRUniform J s) (hΔ : MaxVertexDegreeAtMost J Δ)
    (hM : IsMaximalMatchingIn J M) :
    J.card ≤ (s * (Δ - 1) + 1) * M.card := by
  refine card_le_overlap_bound_of_maximalMatching hM ?_
  intro e heJ
  simpa [Nat.mul_comm] using edgeOverlapSet_card_le_uniform_degree huniform hΔ heJ

/-- If `M` is a maximal matching in an `s`-uniform kernel `J`, has size at most `k - 1`, and `J`
has maximum vertex degree at most `Δ`, then `|J| ≤ (k - 1) ((Δ - 1) s + 1)`.

This is the formal finite-witness version of the informal kernel corollary for sunflower-free
families: in applications, one supplies `M` as a maximal matching and proves `M.card ≤ k - 1`
from `k`-sunflower-freeness of the kernel. -/
theorem card_le_vertexDegree_bound_of_small_maximalMatching
    {J M : Finset (Finset α)} {s Δ k : Nat}
    (huniform : IsRUniform J s) (hΔ : MaxVertexDegreeAtMost J Δ)
    (hM : IsMaximalMatchingIn J M) (hMk : M.card ≤ k - 1) :
    J.card ≤ (k - 1) * (s * (Δ - 1) + 1) := by
  calc
    J.card ≤ (s * (Δ - 1) + 1) * M.card :=
      card_le_vertexDegree_bound_of_maximalMatching huniform hΔ hM
    _ ≤ (s * (Δ - 1) + 1) * (k - 1) := by
      exact Nat.mul_le_mul_left _ hMk
    _ = (k - 1) * (s * (Δ - 1) + 1) := by
      ring

end E20
end Erdos
end Problems
end FormalConjectures
