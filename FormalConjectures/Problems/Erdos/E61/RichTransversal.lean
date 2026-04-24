import FormalConjectures.Problems.Erdos.E61.Blockade

/-!
# Rich blockade transversal selection

This file formalizes the finite selection core behind `prop:rich-transversal`.
The analytic size bookkeeping from the paper is abstracted into the hypothesis
that, for every active candidate family, the current block contains a vertex
that leaves nonempty correct candidate sets in every earlier block.  The
conclusion is a transversal satisfying all required earlier relations.
-/

namespace Erdos61

open Finset

/--
Abstract finite backward-selection core behind rich blockades.

`Good i j v w` means that the choice `v` in block `i` has the correct relation
to the earlier choice `w` in block `j`.  The hypothesis `hstep` says that from
any nonempty candidate family in blocks `0, ..., i`, one can choose a vertex in
block `i` and keep a nonempty refined candidate set in every earlier block on
which the relation to that vertex is already correct.
-/
theorem rich_transversal_selection_finite {V : Type*} [Inhabited V]
    (Good : ℕ → ℕ → V → V → Prop) (n : ℕ) (C : ℕ → Finset V)
    (hC : ∀ i, i < n → (C i).Nonempty)
    (hstep : ∀ i, i < n → ∀ D : ℕ → Finset V,
      (∀ j, j ≤ i → (D j).Nonempty) →
        ∃ v ∈ D i, ∀ j, j < i →
          ∃ D' : Finset V, D' ⊆ D j ∧ D'.Nonempty ∧
            ∀ y ∈ D', Good i j v y) :
    ∃ f : ℕ → V,
      (∀ i, i < n → f i ∈ C i) ∧
        ∀ i j, j < i → i < n → Good i j (f i) (f j) := by
  induction n generalizing C with
  | zero =>
      refine ⟨fun _ => default, ?_, ?_⟩
      · intro i hi
        omega
      · intro i _j _hji hi
        omega
  | succ n ih =>
      have hCn : ∀ j, j ≤ n → (C j).Nonempty := by
        intro j hj
        exact hC j (Nat.lt_succ_of_le hj)
      rcases hstep n (Nat.lt_succ_self n) C hCn with ⟨v, hvC, hrefine⟩
      let Cprev : ℕ → Finset V := fun j =>
        if hj : j < n then Classical.choose (hrefine j hj) else C j
      have hCprev : ∀ i, i < n → (Cprev i).Nonempty := by
        intro i hi
        dsimp [Cprev]
        simp [hi, (Classical.choose_spec (hrefine i hi)).2.1]
      have hstep_prev : ∀ i, i < n → ∀ D : ℕ → Finset V,
          (∀ j, j ≤ i → (D j).Nonempty) →
            ∃ v ∈ D i, ∀ j, j < i →
              ∃ D' : Finset V, D' ⊆ D j ∧ D'.Nonempty ∧
                ∀ y ∈ D', Good i j v y := by
        intro i hi D hD
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)) D hD
      rcases ih Cprev hCprev hstep_prev with ⟨f, hfCprev, hgoodprev⟩
      let F : ℕ → V := fun i =>
        if h : i < n then f i else if i = n then v else default
      refine ⟨F, ?_, ?_⟩
      · intro i hi
        by_cases hin : i < n
        · have hfi : f i ∈ Cprev i := hfCprev i hin
          have hsub : Classical.choose (hrefine i hin) ⊆ C i :=
            (Classical.choose_spec (hrefine i hin)).1
          have hfi_refined : f i ∈ Classical.choose (hrefine i hin) := by
            simpa [Cprev, hin] using hfi
          dsimp [F]
          rw [if_pos hin]
          exact hsub hfi_refined
        · have hin_eq : i = n := by omega
          dsimp [F]
          simp [hin_eq, hvC]
      · intro i j hji hi
        by_cases hin : i < n
        · have hjn : j < n := Nat.lt_trans hji hin
          dsimp [F]
          rw [if_pos hin, if_pos hjn]
          exact hgoodprev i j hji hin
        · have hi_eq : i = n := by omega
          subst i
          have hjn : j < n := hji
          have hfj : f j ∈ Cprev j := hfCprev j hjn
          have hspec := Classical.choose_spec (hrefine j hjn)
          have hgood : ∀ y ∈ Classical.choose (hrefine j hjn), Good n j v y :=
            hspec.2.2
          have hfj_refined : f j ∈ Classical.choose (hrefine j hjn) := by
            dsimp [Cprev] at hfj
            simpa [hjn] using hfj
          dsimp [F]
          rw [if_neg (Nat.lt_irrefl n), if_pos rfl, if_pos hjn]
          exact hgood (f j) hfj_refined

end Erdos61
