import FormalConjectures.Problems.Erdos.E20.Families.TransversalCounterexample

namespace FormalConjectures.Problems.Erdos.E20

open Finset

/-!
# Balanced Multislice Obstruction

This file records the formal core of the balanced-multislice obstruction from
`sunflower_selected_results.tex`.

The analytic estimates in the TeX note, such as Stirling asymptotics and the
positive-density box upper bound, are not formalized here.  The exact finite
object and its immediate sunflower-free consequence are.
-/

/-- Number of coordinates of a word carrying the symbol `a`. -/
def symbolCount {n q : ℕ} (x : Fin n → Fin q) (a : Fin q) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card

/-- A word is balanced if every symbol appears exactly `n / q` times. -/
def IsBalancedWord {n q : ℕ} (x : Fin n → Fin q) : Prop :=
  ∀ a : Fin q, symbolCount x a = n / q

instance instDecidableIsBalancedWord {n q : ℕ} (x : Fin n → Fin q) :
    Decidable (IsBalancedWord x) := by
  unfold IsBalancedWord
  infer_instance

/-- The balanced multislice in `[q]^n`. -/
def balancedWords (n q : ℕ) : Finset (Fin n → Fin q) :=
  Finset.univ.filter IsBalancedWord

@[simp] theorem mem_balancedWords {n q : ℕ} {x : Fin n → Fin q} :
    x ∈ balancedWords n q ↔ IsBalancedWord x := by
  simp [balancedWords]

/-- The transversal set family associated to the balanced multislice. -/
def balancedMultisliceFamily (n q : ℕ) : Finset (Finset (Fin n × Fin q)) :=
  transversalFamily (G := Fin q) (balancedWords n q)

@[simp] theorem card_balancedMultisliceFamily (n q : ℕ) :
    (balancedMultisliceFamily n q).card = (balancedWords n q).card := by
  simp [balancedMultisliceFamily]

/-- The balanced multislice is a subfamily of the full `q`-ary transversal code. -/
theorem balancedWords_subset_univ (n q : ℕ) :
    balancedWords n q ⊆ (Finset.univ : Finset (Fin n → Fin q)) := by
  intro x hx
  simp

/-- Core sunflower-free fact for the balanced multislice obstruction.

If the alphabet has fewer than `k` symbols, every transversal family over that
alphabet is `k`-sunflower-free.  The balanced multislice is one such family,
with the intended specialization `q = k - 1`.
-/
theorem balancedMultislice_sunflowerFree_of_q_lt_k
    (n q k : ℕ) (hk : 2 ≤ k) (hqk : q < k) :
    SunflowerFree (balancedMultisliceFamily n q) k := by
  simpa [balancedMultisliceFamily] using
    (transversalFamily_sunflowerFree_of_card_lt
      (G := Fin q) (C := balancedWords n q) hk (by simpa using hqk))

/-- Specialization to the TeX notation `q = k - 1`. -/
theorem balancedMultislice_sunflowerFree
    (n k : ℕ) (hk : 2 ≤ k) :
    SunflowerFree (balancedMultisliceFamily n (k - 1)) k := by
  apply balancedMultislice_sunflowerFree_of_q_lt_k
  · exact hk
  · omega

end FormalConjectures.Problems.Erdos.E20
