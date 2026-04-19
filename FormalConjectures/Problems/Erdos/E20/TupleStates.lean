import Mathlib
import FormalConjectures.Problems.Erdos.E20.Counterexample

open Finset
open scoped Classical

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Tuple States and Exact Trace Branching

This file formalizes the exact branching mechanism from the user's support-piece note.

For a fixed support piece `P`, each coordinate family is cut into trace fibers by the value of
`A ∩ P`, and the remainder `A \ P` defines the child state.  The main theorem is an exact
decomposition: a tuple state has a cross-sunflower tuple iff, for some local sunflower trace tuple
on `P`, the corresponding child state has a cross-sunflower tuple.

To make the equivalence literally true, the tuple-level notion here does **not** require the chosen
sets to be distinct.  That matches the exact recursive decomposition statement: equality can arise
in a child state even when the original tuple was distinguished entirely by the trace on `P`.
-/

variable {α : Type*} [DecidableEq α]

/-- A `k`-tuple state: one family for each coordinate. -/
abbrev TupleState (α : Type*) (k : ℕ) := Fin k → Finset (Finset α)

/-- A tuple state has a cross-sunflower tuple if one may choose one set from each coordinate family
and the resulting `k`-tuple is a sunflower. -/
def HasCrossSunflowerTuple {k : ℕ} (G : TupleState α k) : Prop :=
  ∃ A : Fin k → Finset α, (∀ i, A i ∈ G i) ∧ IsSunflowerTuple A

/-- Restrict a family to the trace cell `A ∩ P = T` and delete the support piece `P`. -/
def traceRestrictedFamily (H : Finset (Finset α)) (P T : Finset α) : Finset (Finset α) :=
  (H.filter fun A => A ∩ P = T).image fun A => A \ P

/-- The child tuple state obtained from a trace tuple on a fixed support piece `P`. -/
def childState {k : ℕ} (G : TupleState α k) (P : Finset α) (T : Fin k → Finset α) :
    TupleState α k :=
  fun i => traceRestrictedFamily (G i) P (T i)

theorem mem_traceRestrictedFamily_iff {H : Finset (Finset α)} {P T R : Finset α} :
    R ∈ traceRestrictedFamily H P T ↔ ∃ A ∈ H, A ∩ P = T ∧ R = A \ P := by
  constructor
  · intro hR
    rcases Finset.mem_image.mp hR with ⟨A, hA, rfl⟩
    exact ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2, rfl⟩
  · rintro ⟨A, hA, htrace, rfl⟩
    exact Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, htrace⟩, rfl⟩

lemma inter_trace_normal_form (A B P : Finset α) :
    (A ∩ P) ∩ (B ∩ P) = (A ∩ B) ∩ P := by
  ext x
  simp [and_assoc, and_left_comm, and_comm]

lemma inter_sdiff_normal_form (A B P : Finset α) :
    (A \ P) ∩ (B \ P) = (A ∩ B) \ P := by
  ext x
  simp [and_assoc, and_left_comm, and_comm]

/-- Taking traces on a fixed support piece preserves the sunflower property. -/
theorem IsSunflowerTuple.trace {k : ℕ} {A : Fin k → Finset α}
    (hA : IsSunflowerTuple A) (P : Finset α) :
    IsSunflowerTuple (fun i => A i ∩ P) := by
  intro i j i' j' hij hi'j'
  calc
    (A i ∩ P) ∩ (A j ∩ P) = (A i ∩ A j) ∩ P := inter_trace_normal_form _ _ _
    _ = (A i' ∩ A j') ∩ P := by rw [hA hij hi'j']
    _ = (A i' ∩ P) ∩ (A j' ∩ P) := (inter_trace_normal_form _ _ _).symm

/-- Deleting a fixed support piece preserves the sunflower property. -/
theorem IsSunflowerTuple.residual {k : ℕ} {A : Fin k → Finset α}
    (hA : IsSunflowerTuple A) (P : Finset α) :
    IsSunflowerTuple (fun i => A i \ P) := by
  intro i j i' j' hij hi'j'
  calc
    (A i \ P) ∩ (A j \ P) = (A i ∩ A j) \ P := inter_sdiff_normal_form _ _ _
    _ = (A i' ∩ A j') \ P := by rw [hA hij hi'j']
    _ = (A i' \ P) ∩ (A j' \ P) := (inter_sdiff_normal_form _ _ _).symm

/-- If the local trace tuple on `P` is a sunflower and the residual tuple outside `P` is a
sunflower, then the lifted parent tuple is also a sunflower. -/
theorem IsSunflowerTuple.of_trace_and_residual
    {k : ℕ} {A T R : Fin k → Finset α} {P : Finset α}
    (hT : IsSunflowerTuple T) (hR : IsSunflowerTuple R)
    (htrace : ∀ i, A i ∩ P = T i)
    (hres : ∀ i, A i \ P = R i) :
    IsSunflowerTuple A := by
  intro i j i' j' hij hi'j'
  ext x
  by_cases hxP : x ∈ P
  · have hiT : x ∈ A i ↔ x ∈ T i := by
      have h := congrArg (fun S : Finset α => x ∈ S) (htrace i)
      simpa [Finset.mem_inter, hxP] using h
    have hjT : x ∈ A j ↔ x ∈ T j := by
      have h := congrArg (fun S : Finset α => x ∈ S) (htrace j)
      simpa [Finset.mem_inter, hxP] using h
    have hi'T : x ∈ A i' ↔ x ∈ T i' := by
      have h := congrArg (fun S : Finset α => x ∈ S) (htrace i')
      simpa [Finset.mem_inter, hxP] using h
    have hj'T : x ∈ A j' ↔ x ∈ T j' := by
      have h := congrArg (fun S : Finset α => x ∈ S) (htrace j')
      simpa [Finset.mem_inter, hxP] using h
    have hEq := congrArg (fun S : Finset α => x ∈ S) (hT hij hi'j')
    simpa [Finset.mem_inter, hiT, hjT, hi'T, hj'T] using hEq
  · have hiR : x ∈ A i ↔ x ∈ R i := by
      have h := congrArg (fun S : Finset α => x ∈ S) (hres i)
      simpa [Finset.mem_sdiff, hxP] using h
    have hjR : x ∈ A j ↔ x ∈ R j := by
      have h := congrArg (fun S : Finset α => x ∈ S) (hres j)
      simpa [Finset.mem_sdiff, hxP] using h
    have hi'R : x ∈ A i' ↔ x ∈ R i' := by
      have h := congrArg (fun S : Finset α => x ∈ S) (hres i')
      simpa [Finset.mem_sdiff, hxP] using h
    have hj'R : x ∈ A j' ↔ x ∈ R j' := by
      have h := congrArg (fun S : Finset α => x ∈ S) (hres j')
      simpa [Finset.mem_sdiff, hxP] using h
    have hEq := congrArg (fun S : Finset α => x ∈ S) (hR hij hi'j')
    simpa [Finset.mem_inter, hiR, hjR, hi'R, hj'R] using hEq

/-- A global cross-sunflower tuple induces a local sunflower trace tuple on `P` and a
cross-sunflower tuple in the corresponding child state. -/
theorem exists_trace_child_of_crossSunflowerTuple
    {k : ℕ} {G : TupleState α k} (P : Finset α)
    (hG : HasCrossSunflowerTuple G) :
    ∃ T : Fin k → Finset α,
      IsSunflowerTuple T ∧ HasCrossSunflowerTuple (childState G P T) := by
  rcases hG with ⟨A, hA, hSun⟩
  refine ⟨fun i => A i ∩ P, hSun.trace P, ?_⟩
  refine ⟨fun i => A i \ P, ?_, hSun.residual P⟩
  intro i
  exact (mem_traceRestrictedFamily_iff).2 ⟨A i, hA i, rfl, rfl⟩

/-- A sunflower trace tuple on `P` together with a cross-sunflower tuple in the child state lifts
to a cross-sunflower tuple in the parent state. -/
theorem lift_crossSunflowerTuple_of_child
    {k : ℕ} {G : TupleState α k} {P : Finset α} {T : Fin k → Finset α}
    (hT : IsSunflowerTuple T)
    (hChild : HasCrossSunflowerTuple (childState G P T)) :
    HasCrossSunflowerTuple G := by
  rcases hChild with ⟨R, hRmem, hR⟩
  choose A hA_mem hA_trace hA_res using
    fun i => (mem_traceRestrictedFamily_iff).1 (hRmem i)
  refine ⟨A, hA_mem, ?_⟩
  exact IsSunflowerTuple.of_trace_and_residual hT hR hA_trace (fun i => (hA_res i).symm)

/-- Exact trace/branch decomposition on a fixed support piece `P`.

This is the precise formal version of the user's support-piece branching statement: for each fixed
piece `P`, a cross-sunflower tuple exists in the parent state iff there is some local sunflower
trace tuple on `P` whose child state contains a cross-sunflower tuple. -/
theorem hasCrossSunflowerTuple_iff_exists_child
    {k : ℕ} {G : TupleState α k} (P : Finset α) :
    HasCrossSunflowerTuple G ↔
      ∃ T : Fin k → Finset α,
        IsSunflowerTuple T ∧ HasCrossSunflowerTuple (childState G P T) := by
  constructor
  · exact exists_trace_child_of_crossSunflowerTuple P
  · rintro ⟨T, hT, hChild⟩
    exact lift_crossSunflowerTuple_of_child hT hChild

end FormalConjectures.Problems.Erdos.E20
