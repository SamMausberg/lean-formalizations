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

This file formalizes the results from Section 10 of the sunflower compendium
(sunflower_compendium.pdf): "Fixed-alphabet code models: rigorous recurrences
and provisional local tensors." Only the exact off-diagonal recurrences
(Section 10.1) are formalized here, as the local tensor program (Section 10.2)
is explicitly labeled exploratory/provisional in the paper.
-/

/-- **Theorem 10.1 (One extra symbol), first recurrence.**
For all integers `q, k, m ≥ 1`:
  `F_{q+1,k}(m) ≤ ∑_{r=0}^{m} C(m,r) · F_{q,k}(r)`.

The proof partitions a code `C ⊆ [q+1]^m` by the support of the extra symbol `q+1`.
Deleting the extra-symbol coordinates from a fixed support class gives an injective
map into `[q]^{m-r}`, and sunflower-freeness is preserved. -/
theorem one_extra_symbol_recurrence (q k m : ℕ) (hq : 1 ≤ q) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    codeModelNumber (q + 1) k m ≤ ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r := by
  sorry

/-- **Theorem 10.1, general iterated form.**
For every integer `t ≥ 0`:
  `F_{q+t,k}(m) ≤ ∑_{r=0}^{m} C(m,r) · t^{m-r} · F_{q,k}(r)`.

The iterated formula follows by induction on `t`. -/
theorem iterated_extra_symbol_recurrence
    (q k m t : ℕ) (hq : 1 ≤ q) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    codeModelNumber (q + t) k m ≤
      ∑ r ∈ Finset.range (m + 1), m.choose r * t ^ (m - r) * codeModelNumber q k r := by
  sorry

/-- **Theorem 10.2 (Sharper randomized deletion lift).**
For all integers `q, t, k, m ≥ 1`:
  `F_{q+t,k}(m) ≤ ((q+t)/q)^m · F_{q,k}(m)`.

The proof uses a probabilistic argument: choose independently in each coordinate
a uniformly random `q`-subset of `[q+t]`. Any codeword survives with probability
`(q/(q+t))^m`. The surviving code remains `k`-sunflower-free.

We formalize this as a natural number inequality (multiplied through by `q^m`):
  `q^m · F_{q+t,k}(m) ≤ (q+t)^m · F_{q,k}(m)`. -/
theorem randomized_deletion_lift
    (q t k m : ℕ) (hq : 1 ≤ q) (hk : 2 ≤ k) :
    q ^ m * codeModelNumber (q + t) k m ≤ (q + t) ^ m * codeModelNumber q k m := by
  sorry
end FormalConjectures.Problems.Erdos.E20.Compendium
