import FormalConjectures.Problems.Erdos.E20.ExplicitKernels

open Finset

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Bounded-Local-Coordinate Branch Bridge Counterexample

This file packages an explicit finite obstruction to a "bounded-local-coordinate branch bridge."
The hypergraph family is the `K_k` tensor-product family already formalized in
`ExplicitKernels.lean`.  Its local alphabet is the finite set of `2`-subsets of `Fin k`, so the
global family on `n + 1` coordinates has size `choose k 2 ^ (n + 1)`.

We record the exact structural facts needed for the obstruction:

* exact cardinality;
* exact uniformity;
* `k`-sunflower-freeness for `k ≥ 3`;
* terminal / no-degree-`1` behavior via "no one-out set" and leaf-stripping invariance;
* a precise local branch model: after any conditioning on coordinates, every branch that leaves
  only `b` coordinates free has size at most `choose k 2 ^ b`, hence `O_k(1)` when `b = O_k(1)`.
-/

section Family

/-- The fixed local alphabet: one coordinate chooses an edge of `K_k`, i.e. a `2`-subset of
`Fin k`. -/
abbrev BranchBridgeLocalAlphabet (k : ℕ) := ↥(twoSubsets k)

/-- The coordinate-word model underlying the tensor-product counterexample. -/
abbrev BranchBridgeWord (n k : ℕ) := Fin (n + 1) → BranchBridgeLocalAlphabet k

/-- The hypergraph family `F_n`: one row for each `i : Fin (n + 1)`, each row carrying one
local `2`-subset of `Fin k`. -/
abbrev branchBridgeFamily (n k : ℕ) : Finset (Finset (Fin (n + 1) × Fin k)) :=
  pairTensorFamily (n + 1) k

/-- The tagged-edge map from the coordinate-word model to the actual hypergraph edge. -/
def branchBridgeWordToEdge {n k : ℕ} (x : BranchBridgeWord n k) :
    Finset (Fin (n + 1) × Fin k) :=
  taggedEdge fun i => (((x i : BranchBridgeLocalAlphabet k) : Finset (Fin k)))

@[simp] theorem card_BranchBridgeLocalAlphabet (k : ℕ) :
    Fintype.card (BranchBridgeLocalAlphabet k) = Nat.choose k 2 := by
  simp [BranchBridgeLocalAlphabet]

theorem branchBridgeWordToEdge_injective {n k : ℕ} :
    Function.Injective (branchBridgeWordToEdge (n := n) (k := k)) := by
  intro x y hxy
  apply funext
  intro i
  apply Subtype.ext
  have hset :
      (fun j : Fin (n + 1) => (((x j : BranchBridgeLocalAlphabet k) : Finset (Fin k)))) i =
        (fun j : Fin (n + 1) => (((y j : BranchBridgeLocalAlphabet k) : Finset (Fin k)))) i := by
    exact congrArg (fun f => f i) (taggedEdge_injective hxy)
  simpa using hset

theorem branchBridgeWordToEdge_mem_family {n k : ℕ} (x : BranchBridgeWord n k) :
    branchBridgeWordToEdge x ∈ branchBridgeFamily n k := by
  unfold branchBridgeFamily pairTensorFamily branchBridgeWordToEdge taggedProductFamily
  exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

@[simp] theorem card_branchBridgeFamily (n k : ℕ) :
    (branchBridgeFamily n k).card = Nat.choose k 2 ^ (n + 1) := by
  simp [branchBridgeFamily]

/-- Every edge of `F_n` has exactly `2` vertices in each of the `n + 1` rows. -/
theorem branchBridgeFamily_uniform (n k : ℕ) :
    IsRUniform (branchBridgeFamily n k) (2 * (n + 1)) := by
  intro e he
  unfold branchBridgeFamily pairTensorFamily taggedProductFamily at he
  rcases Finset.mem_image.mp he with ⟨x, -, rfl⟩
  rw [card_taggedEdge]
  have hcard :
      ∀ i : Fin (n + 1),
        ((((x i : ↥(twoSubsets k)) : Finset (Fin k))).card) = 2 := by
    intro i
    simpa using (mem_twoSubsets_iff.mp (x i).2)
  calc
    ∑ i : Fin (n + 1), (((x i : ↥(twoSubsets k)) : Finset (Fin k))).card
        = ∑ _ : Fin (n + 1), 2 := by simp [hcard]
    _ = (n + 1) * 2 := by simp
    _ = 2 * (n + 1) := by omega

theorem branchBridgeFamily_sunflowerFree (n k : ℕ) (hk : 3 ≤ k) :
    SunflowerFree (branchBridgeFamily n k) k := by
  simpa [branchBridgeFamily] using pairTensorFamily_sunflowerFree (n + 1) k hk

/-- In the one-out / terminal sense from `ExplicitKernels.lean`, the family already has no
genuine one-out coordinate block. -/
theorem branchBridgeFamily_noOneOutSet (n k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ Q, IsOneOutSet (branchBridgeFamily n k) Q := by
  simpa [branchBridgeFamily] using pairTensorFamily_no_oneOutSet n k hk

/-- Every vertex survives leaf stripping, so there are no degree-`1` vertices. -/
theorem nonLeafVertices_branchBridgeFamily_eq_univ (n k : ℕ) (hk : 3 ≤ k) :
    nonLeafVertices (branchBridgeFamily n k) = Finset.univ := by
  simpa [branchBridgeFamily] using nonLeafVertices_pairTensorFamily_eq_univ n k hk

/-- One leaf-stripping round fixes the family. -/
theorem strippedSupport_branchBridgeFamily_eq (n k : ℕ) (hk : 3 ≤ k) :
    strippedSupportFamily (branchBridgeFamily n k) = branchBridgeFamily n k := by
  simpa [branchBridgeFamily] using strippedSupport_pairTensorFamily_eq n k hk

end Family

section LocalBranches

/-- A finite coordinate conditioning for the word model of `F_n`. -/
structure BranchBridgeConditioning (n k : ℕ) where
  coords : Finset (Fin (n + 1))
  values : ∀ i, i ∈ coords → BranchBridgeLocalAlphabet k

/-- The words that survive a given coordinate conditioning. -/
def conditionedBranchBridgeWords {n k : ℕ} (C : BranchBridgeConditioning n k) :
    Finset (BranchBridgeWord n k) :=
  (Finset.univ : Finset (BranchBridgeWord n k)).filter
    fun x => ∀ i hi, x i = C.values i hi

/-- A bounded-local-coordinate branch inside a conditioned family: outside the free coordinate set,
the word is frozen to a single background word.  Only coordinates in `free` may vary. -/
def boundedLocalCoordinateBranchWords {n k : ℕ} (C : BranchBridgeConditioning n k)
    (free : Finset (Fin (n + 1))) (base : BranchBridgeWord n k) :
    Finset (BranchBridgeWord n k) :=
  (conditionedBranchBridgeWords C).filter fun x => ∀ i, i ∉ free → x i = base i

/-- The corresponding edge branch inside the hypergraph family `F_n`. -/
def boundedLocalCoordinateBranch {n k : ℕ} (C : BranchBridgeConditioning n k)
    (free : Finset (Fin (n + 1))) (base : BranchBridgeWord n k) :
    Finset (Finset (Fin (n + 1) × Fin k)) :=
  (boundedLocalCoordinateBranchWords C free base).image
    (branchBridgeWordToEdge (n := n) (k := k))

theorem boundedLocalCoordinateBranch_subset_family {n k : ℕ}
    (C : BranchBridgeConditioning n k) (free : Finset (Fin (n + 1)))
    (base : BranchBridgeWord n k) :
    boundedLocalCoordinateBranch C free base ⊆ branchBridgeFamily n k := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
  exact branchBridgeWordToEdge_mem_family x

@[simp] theorem card_boundedLocalCoordinateBranch {n k : ℕ}
    (C : BranchBridgeConditioning n k) (free : Finset (Fin (n + 1)))
    (base : BranchBridgeWord n k) :
    (boundedLocalCoordinateBranch C free base).card =
      (boundedLocalCoordinateBranchWords C free base).card := by
  exact Finset.card_image_of_injective _ (branchBridgeWordToEdge_injective (n := n) (k := k))

theorem card_boundedLocalCoordinateBranchWords_le {n k : ℕ}
    (C : BranchBridgeConditioning n k) (free : Finset (Fin (n + 1)))
    (base : BranchBridgeWord n k) :
    (boundedLocalCoordinateBranchWords C free base).card ≤ Nat.choose k 2 ^ free.card := by
  classical
  let restrict :
      ↥(boundedLocalCoordinateBranchWords C free base) →
        (free → BranchBridgeLocalAlphabet k) :=
    fun x i => x.1 i
  have hrestrict :
      Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ free
    · have := congrArg (fun f => f ⟨i, hi⟩) hxy
      simpa [restrict] using this
    · have hxbase : x.1 i = base i := by
        exact (Finset.mem_filter.mp x.2).2 i hi
      have hybase : y.1 i = base i := by
        exact (Finset.mem_filter.mp y.2).2 i hi
      exact hxbase.trans hybase.symm
  have hcard := Fintype.card_le_of_injective restrict hrestrict
  simpa [restrict, Fintype.card_fun, card_BranchBridgeLocalAlphabet] using hcard

theorem card_boundedLocalCoordinateBranch_le {n k : ℕ}
    (C : BranchBridgeConditioning n k) (free : Finset (Fin (n + 1)))
    (base : BranchBridgeWord n k) :
    (boundedLocalCoordinateBranch C free base).card ≤ Nat.choose k 2 ^ free.card := by
  rw [card_boundedLocalCoordinateBranch]
  exact card_boundedLocalCoordinateBranchWords_le C free base

/-- The bound depends only on the number of free coordinates, not on how much conditioning was
performed beforehand.  In particular, after any `O_k(1)` conditioning, every branch with
`O_k(1)` free coordinates has `O_k(1)` size. -/
theorem boundedLocalCoordinateBranch_card_le_of_free_card_le {n k b : ℕ}
    (C : BranchBridgeConditioning n k) (free : Finset (Fin (n + 1)))
    (base : BranchBridgeWord n k) (hk : 3 ≤ k) (hfree : free.card ≤ b) :
    (boundedLocalCoordinateBranch C free base).card ≤ Nat.choose k 2 ^ b := by
  have hchoose : 1 ≤ Nat.choose k 2 := by
    exact Nat.succ_le_of_lt (Nat.choose_pos (by omega))
  exact le_trans (card_boundedLocalCoordinateBranch_le C free base)
    (pow_le_pow_right' hchoose hfree)

end LocalBranches

end FormalConjectures.Problems.Erdos.E20
