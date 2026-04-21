import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium

def CodeModelFree (q k m : ℕ) (C : Finset (Fin m → Fin q)) : Prop :=
  ∀ (f : Fin k → Fin m → Fin q),
    Function.Injective f →
    (∀ i, f i ∈ C) →
    ∃ j : Fin m, ¬(∀ a b : Fin k, f a j = f b j) ∧
                  ¬(Function.Injective (fun a => f a j))

theorem codeModelNumber_bddAbove (q k m : ℕ) :
    BddAbove {c : ℕ | ∃ (C : Finset (Fin m → Fin q)),
      C.card = c ∧ CodeModelFree q k m C} := by
  refine ⟨Fintype.card (Fin m → Fin q), ?_⟩
  rintro c ⟨C, rfl, -⟩
  exact Finset.card_le_univ C

theorem card_le_codeModelNumber {q k m : ℕ} {C : Finset (Fin m → Fin q)}
    (hfree : CodeModelFree q k m C) :
    C.card ≤ codeModelNumber q k m := by
  unfold codeModelNumber
  exact le_csSup (codeModelNumber_bddAbove q k m) ⟨C, rfl, hfree⟩


/-!
# Section 10: Fixed-Alphabet Code Models

This file packages the results from Section 10 of the sunflower compendium
(sunflower_compendium.pdf): "Fixed-alphabet code models: rigorous recurrences
and provisional local tensors." The recurrence statements below are kept
honest: when the current local definitions do not yet support a full proof, the file
only records the checked extremalization step from an explicit per-code bound.
-/

/-- If every admissible code has size at most `B`, then the extremal code-model number is at
most `B`.  This is the `csSup` packaging step used by the conditional recurrence reductions
below. -/
theorem codeModelNumber_le_of_code_bound
    {q k m B : ℕ}
    (hbound : ∀ (C : Finset (Fin m → Fin q)), CodeModelFree q k m C → C.card ≤ B) :
    codeModelNumber q k m ≤ B := by
  unfold codeModelNumber
  apply csSup_le'
  intro c hc
  rcases hc with ⟨C, rfl, hfree⟩
  exact hbound C hfree

/-- **Theorem 10.1 (one extra symbol), extremalization step.**
If the missing support-class decomposition has already been proved for every concrete
`CodeModelFree (q + 1) k m` code, then the extremal recurrence follows. -/
theorem one_extra_symbol_recurrence_of_support_class_bound
    (q k m : ℕ)
    (hbound : ∀ (C : Finset (Fin m → Fin (q + 1))),
      CodeModelFree (q + 1) k m C →
      C.card ≤ ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r) :
    codeModelNumber (q + 1) k m ≤
      ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r :=
  codeModelNumber_le_of_code_bound hbound

/-- **Theorem 10.1, iterated form, extremalization step.**
If the iterated deletion/convolution estimate has already been proved for every concrete
`CodeModelFree (q + t) k m` code, then the stated extremal recurrence follows. -/
theorem iterated_extra_symbol_recurrence_of_code_bound
    (q k m t : ℕ)
    (hbound : ∀ (C : Finset (Fin m → Fin (q + t))),
      CodeModelFree (q + t) k m C →
      C.card ≤
        ∑ r ∈ Finset.range (m + 1), m.choose r * t ^ (m - r) * codeModelNumber q k r) :
    codeModelNumber (q + t) k m ≤
      ∑ r ∈ Finset.range (m + 1), m.choose r * t ^ (m - r) * codeModelNumber q k r :=
  codeModelNumber_le_of_code_bound hbound

/- **Theorem 10.2 (sharper randomized deletion lift).**
The probabilistic proof in the compendium reduces to a counting lemma for
coordinatewise `q`-subset selections.  That scaled averaging step is not proved in this file,
so no theorem for the final randomized inequality is asserted here. -/
end FormalConjectures.Problems.Erdos.E20.Compendium
