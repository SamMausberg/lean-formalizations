import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Bounded alternation as finite cutpoint data

This file formalizes the finite Boolean-word core of `lem:bounded-alt`.
For a fixed ordered vertex set and one outside vertex, the neighborhood pattern
is a Boolean word.  Such a word is determined by its first bit and the finite
list of adjacent transition flags; the number of true transition flags is the
number of adjacent alternations.
-/

namespace Erdos61

/-- Adjacent transition flags of a Boolean word. -/
def boolChangeFlags : List Bool → List Bool
  | [] => []
  | [_] => []
  | a :: b :: rest => (a != b) :: boolChangeFlags (b :: rest)

/-- Number of adjacent alternations in a Boolean word. -/
def boolChangeCount (w : List Bool) : ℕ :=
  (boolChangeFlags w).count true

/-- Advance one Boolean step according to a transition flag. -/
def boolNextFromChange (b change : Bool) : Bool :=
  if change then !b else b

/-- Reconstruct a nonempty Boolean word from its first bit and transition flags. -/
def boolReconstruct : Bool → List Bool → List Bool
  | b, [] => [b]
  | b, change :: rest => b :: boolReconstruct (boolNextFromChange b change) rest

/-- Empty-aware reconstruction from an optional first bit. -/
def boolReconstruct? : Option Bool → List Bool → List Bool
  | none, _ => []
  | some b, flags => boolReconstruct b flags

@[simp] theorem boolNextFromChange_change (a b : Bool) :
    boolNextFromChange a (a != b) = b := by
  cases a <;> cases b <;> rfl

@[simp] theorem bool_change_of_nextFromChange (a change : Bool) :
    (a != boolNextFromChange a change) = change := by
  cases a <;> cases change <;> rfl

@[simp] theorem boolChangeFlags_cons_reconstruct (a b : Bool) (flags : List Bool) :
    boolChangeFlags (a :: boolReconstruct b flags) = (a != b) :: flags := by
  induction flags generalizing a b with
  | nil =>
      simp [boolReconstruct, boolChangeFlags]
  | cons change rest ih =>
      simp [boolReconstruct, boolChangeFlags, ih]

@[simp] theorem boolChangeFlags_reconstruct (b : Bool) (flags : List Bool) :
    boolChangeFlags (boolReconstruct b flags) = flags := by
  induction flags generalizing b with
  | nil =>
      simp [boolReconstruct, boolChangeFlags]
  | cons change rest ih =>
      simp [boolReconstruct]

@[simp] theorem boolChangeCount_reconstruct (b : Bool) (flags : List Bool) :
    boolChangeCount (boolReconstruct b flags) = flags.count true := by
  simp [boolChangeCount]

@[simp] theorem boolReconstruct_changeFlags_cons (b : Bool) (rest : List Bool) :
    boolReconstruct b (boolChangeFlags (b :: rest)) = b :: rest := by
  induction rest generalizing b with
  | nil =>
      simp [boolReconstruct, boolChangeFlags]
  | cons c rest ih =>
      simp [boolReconstruct, boolChangeFlags, ih]

theorem bool_word_determined_by_initial_and_changes (w₁ w₂ : List Bool)
    (hhead : w₁.head? = w₂.head?)
    (hchanges : boolChangeFlags w₁ = boolChangeFlags w₂) :
    w₁ = w₂ := by
  cases w₁ with
  | nil =>
      cases w₂ with
      | nil => rfl
      | cons b rest => simp at hhead
  | cons b rest =>
      cases w₂ with
      | nil => simp at hhead
      | cons c rest₂ =>
          injection hhead with hbc
          subst c
          rw [← boolReconstruct_changeFlags_cons b rest,
            ← boolReconstruct_changeFlags_cons b rest₂, hchanges]

/--
Finite cutpoint-control package for a Boolean word with bounded adjacent
alternation: the transition flags have at most `A` true entries and reconstruct
the word from its initial bit.
-/
theorem bounded_bool_alternation_has_finite_control (w : List Bool) {A : ℕ}
    (hA : boolChangeCount w ≤ A) :
    ∃ flags : List Bool,
      flags = boolChangeFlags w ∧ flags.count true ≤ A ∧
        boolReconstruct? w.head? flags = w := by
  refine ⟨boolChangeFlags w, rfl, hA, ?_⟩
  cases w with
  | nil =>
      simp [boolReconstruct?]
  | cons b rest =>
      simp [boolReconstruct?, boolReconstruct_changeFlags_cons]

/--
The transition count is forced by any reconstruction from transition flags:
there is no shorter transition-flag representation in this exact model.
-/
theorem bool_change_count_eq_flags_count_of_reconstruct
    {w flags : List Bool} {b : Bool} (h : boolReconstruct b flags = w) :
    boolChangeCount w = flags.count true := by
  rw [← h]
  simp

end Erdos61
