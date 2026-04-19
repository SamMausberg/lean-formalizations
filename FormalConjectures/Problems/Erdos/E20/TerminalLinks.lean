import Mathlib
import FormalConjectures.Problems.Erdos.E20.BetaChain

open Finset
open scoped Classical

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Terminal-Link Witness Reductions

This file packages the terminal-link notions from the user's E20 follow-up note in a form that
is precise in Lean and stable under later refinements.

The point is to separate:

* the abstract local notions (`minimalSurvivingWitnesses`, `effectiveOverlapDegree`);
* the exact bounded-alphabet conclusion that follows once one already has a disjoint
  root/petal witness pattern.

We do **not** formalize an Erdős--Rado sunflower extraction here.  Instead, the extraction step is
isolated as explicit input data (`WitnessSunflowerData`), and the bounded-alphabet skeleton is
proved exactly from that data.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

section MinimalWitnesses

variable (Survives : Finset (Finset α) → Prop)

/-- The abstract predicate saying that a nonempty set `W` is a minimal surviving witness for the
terminal-link scheme `Survives`.  It survives as a link, and no nonempty proper sublink survives.

This formalizes the user's `𝓜(𝓚)` definition. -/
def IsMinimalSurvivingWitness (H : Finset (Finset α)) (W : Finset α) : Prop :=
  W.Nonempty ∧
    Survives (linkFamily H W) ∧
    ∀ W' : Finset α, W' ⊂ W → W'.Nonempty → ¬ Survives (linkFamily H W')

/-- The finite family of minimal surviving witnesses.  Since the ambient vertex type is finite,
we realize it as a filtered powerset. -/
noncomputable def minimalSurvivingWitnesses (H : Finset (Finset α)) : Finset (Finset α) :=
  (Finset.univ : Finset α).powerset.filter fun W => IsMinimalSurvivingWitness Survives H W

/-- The effective overlap degree: the number of minimal surviving witnesses. -/
noncomputable def effectiveOverlapDegree (H : Finset (Finset α)) : ℕ :=
  (minimalSurvivingWitnesses Survives H).card

/-- The bounded-witness-size hypothesis from the user's note. -/
def BoundedWitnessSize (H : Finset (Finset α)) (s : ℕ) : Prop :=
  ∀ W ∈ minimalSurvivingWitnesses Survives H, W.card ≤ s

theorem mem_minimalSurvivingWitnesses_iff {H : Finset (Finset α)} {W : Finset α} :
    W ∈ minimalSurvivingWitnesses Survives H ↔ IsMinimalSurvivingWitness Survives H W := by
  simp [minimalSurvivingWitnesses, IsMinimalSurvivingWitness]

theorem effectiveOverlapDegree_eq_card (H : Finset (Finset α)) :
    effectiveOverlapDegree Survives H = (minimalSurvivingWitnesses Survives H).card := rfl

theorem minimalSurvivingWitness_nonempty {H : Finset (Finset α)} {W : Finset α}
    (hW : W ∈ minimalSurvivingWitnesses Survives H) :
    W.Nonempty := by
  exact (mem_minimalSurvivingWitnesses_iff (Survives := Survives)).mp hW |>.1

theorem minimalSurvivingWitness_survives {H : Finset (Finset α)} {W : Finset α}
    (hW : W ∈ minimalSurvivingWitnesses Survives H) :
    Survives (linkFamily H W) := by
  exact (mem_minimalSurvivingWitnesses_iff (Survives := Survives)).mp hW |>.2.1

end MinimalWitnesses

section WitnessSunflower

variable (Survives : Finset (Finset α) → Prop)

/-- Explicit root/petal witness data for the terminal-link reduction.

This is the precise finite combinatorial object extracted informally from a large family of
minimal surviving witnesses after applying a sunflower lemma.  Once such data is given, the
bounded-alphabet code skeleton can be built directly. -/
structure WitnessSunflowerData (H : Finset (Finset α)) (m : ℕ) where
  root : Finset α
  petals : Fin m → Finset α
  petals_nonempty : ∀ i, (petals i).Nonempty
  petals_pairwiseDisjoint : (Set.univ : Set (Fin m)).PairwiseDisjoint petals
  root_disjoint_petals : ∀ i, Disjoint root (petals i)
  survives_each : ∀ i, Survives (linkFamily H (root ∪ petals i))

namespace WitnessSunflowerData

variable {Survives} {H : Finset (Finset α)} {m s : ℕ}

/-- The residual family after conditioning on the common root. -/
noncomputable def residualFamily (D : WitnessSunflowerData Survives H m) :
    Finset (Finset α) :=
  linkFamily H D.root

/-- The `i`-th local alphabet: all intersections of residual edges with the `i`-th petal. -/
noncomputable def localAlphabet (D : WitnessSunflowerData Survives H m) (i : Fin m) :
    Finset (Finset α) :=
  (D.residualFamily).image fun A => A ∩ D.petals i

/-- The block trace of the residual family on the petal coordinates. -/
noncomputable def blockTrace (D : WitnessSunflowerData Survives H m) :
    Finset (Fin m → Finset α) :=
  (D.residualFamily).image fun A => fun i => A ∩ D.petals i

theorem survives_petals_after_root (D : WitnessSunflowerData Survives H m) (i : Fin m) :
    Survives (linkFamily H (D.root ∪ D.petals i)) :=
  D.survives_each i

theorem mem_localAlphabet_iff {D : WitnessSunflowerData Survives H m} {i : Fin m}
    {B : Finset α} :
    B ∈ D.localAlphabet i ↔ ∃ A ∈ D.residualFamily, B = A ∩ D.petals i := by
  constructor
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨A, hA, hAB⟩
    exact ⟨A, hA, hAB.symm⟩
  · rintro ⟨A, hA, rfl⟩
    exact Finset.mem_image.mpr ⟨A, hA, rfl⟩

theorem mem_blockTrace_iff {D : WitnessSunflowerData Survives H m} {w : Fin m → Finset α} :
    w ∈ D.blockTrace ↔ ∃ A ∈ D.residualFamily, w = fun i => A ∩ D.petals i := by
  constructor
  · intro hw
    rcases Finset.mem_image.mp hw with ⟨A, hA, hAw⟩
    exact ⟨A, hA, hAw.symm⟩
  · rintro ⟨A, hA, rfl⟩
    exact Finset.mem_image.mpr ⟨A, hA, rfl⟩

theorem blockTrace_coordinate_mem_localAlphabet
    {D : WitnessSunflowerData Survives H m} {w : Fin m → Finset α}
    (hw : w ∈ D.blockTrace) (i : Fin m) :
    w i ∈ D.localAlphabet i := by
  rcases (mem_blockTrace_iff (D := D)).mp hw with ⟨A, hA, rfl⟩
  exact (mem_localAlphabet_iff (D := D)).2 ⟨A, hA, rfl⟩

theorem localAlphabet_subset_powerset
    {D : WitnessSunflowerData Survives H m} (i : Fin m) :
    D.localAlphabet i ⊆ (D.petals i).powerset := by
  intro B hB
  rcases (mem_localAlphabet_iff (D := D)).mp hB with ⟨A, hA, rfl⟩
  exact Finset.mem_powerset.mpr Finset.inter_subset_right

theorem localAlphabet_card_le_pow
    {D : WitnessSunflowerData Survives H m} (i : Fin m) :
    (D.localAlphabet i).card ≤ 2 ^ (D.petals i).card := by
  calc
    (D.localAlphabet i).card ≤ ((D.petals i).powerset).card := by
      exact Finset.card_le_card (D.localAlphabet_subset_powerset i)
    _ = 2 ^ (D.petals i).card := by simp

theorem localAlphabet_card_le_pow_of_card_le
    {D : WitnessSunflowerData Survives H m} (i : Fin m)
    (hsize : (D.petals i).card ≤ s) :
    (D.localAlphabet i).card ≤ 2 ^ s := by
  calc
    (D.localAlphabet i).card ≤ 2 ^ (D.petals i).card := D.localAlphabet_card_le_pow i
    _ ≤ 2 ^ s := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hsize

/-- Exact bounded-alphabet conclusion from a root/petal witness pattern.

This is the formal core of the user's terminal-link theorem: once one has conditioned on a common
root and exposed pairwise disjoint surviving petal blocks of uniformly bounded size, the residual
family yields a block trace living inside bounded local alphabets. -/
theorem exists_boundedAlphabetSkeleton
    {D : WitnessSunflowerData Survives H m}
    (hsize : ∀ i, (D.petals i).card ≤ s) :
    ∃ A : Fin m → Finset (Finset α),
      (∀ i, (A i).card ≤ 2 ^ s) ∧
      ∀ w ∈ D.blockTrace, ∀ i, w i ∈ A i := by
  refine ⟨D.localAlphabet, ?_, ?_⟩
  · intro i
    exact D.localAlphabet_card_le_pow_of_card_le i (hsize i)
  · intro w hw i
    exact D.blockTrace_coordinate_mem_localAlphabet hw i

end WitnessSunflowerData

end WitnessSunflower

end FormalConjectures.Problems.Erdos.E20
