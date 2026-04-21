import FormalConjectures.Problems.Erdos.E20.Compendium.Models.CodeModels

open scoped BigOperators Pointwise
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-- The explicit `28`-point construction from the `(4,4)` code-model proposition. -/
def A0 : Finset (Fin 2 → Fin 4) :=
  {![0, 0], ![0, 1], ![0, 2], ![2, 2], ![2, 3], ![3, 0], ![3, 1], ![3, 2]}

def A1 : Finset (Fin 2 → Fin 4) :=
  {![0, 0], ![0, 1], ![0, 3], ![1, 0], ![2, 1], ![2, 3], ![3, 0], ![3, 1], ![3, 3]}

def A2 : Finset (Fin 2 → Fin 4) :=
  {![0, 0], ![0, 1], ![0, 2], ![2, 1], ![2, 2], ![2, 3], ![3, 0], ![3, 1], ![3, 2]}

def A3 : Finset (Fin 2 → Fin 4) :=
  {![2, 1], ![2, 2]}

def liftWord (i : Fin 4) (u : Fin 2 → Fin 4) : Fin 3 → Fin 4 := ![i, u 0, u 1]

def pairOf (x : Fin 3 → Fin 4) : Fin 2 → Fin 4 := ![x 1, x 2]

def codeModel444_28 : Finset (Fin 3 → Fin 4) :=
  (A0.image (liftWord 0)) ∪ (A1.image (liftWord 1)) ∪ (A2.image (liftWord 2)) ∪
    (A3.image (liftWord 3))

set_option linter.style.nativeDecide false in
lemma A0_row_card_lt_four : ∀ r : Fin 4, (A0.filter (fun u => u 0 = r)).card < 4 := by
  intro r
  fin_cases r <;> native_decide

set_option linter.style.nativeDecide false in
lemma A2_row_card_lt_four : ∀ r : Fin 4, (A2.filter (fun u => u 0 = r)).card < 4 := by
  intro r
  fin_cases r <;> native_decide

set_option linter.style.nativeDecide false in
lemma A1_col_card_lt_four : ∀ r : Fin 4, (A1.filter (fun u => u 1 = r)).card < 4 := by
  intro r
  fin_cases r <;> native_decide

set_option linter.style.nativeDecide false in
lemma A0_no_first_one : ∀ u ∈ A0, u 0 ≠ 1 := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A2_no_first_one : ∀ u ∈ A2, u 0 ≠ 1 := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A3_no_first_one : ∀ u ∈ A3, u 0 ≠ 1 := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A1_first_one_eq_zero : ∀ u ∈ A1, u 0 = 1 → u 1 = 0 := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A0_first_two_second_mem : ∀ u ∈ A0, u 0 = 2 → u 1 ∈ ({2, 3} : Finset (Fin 4)) := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A1_first_two_second_mem : ∀ u ∈ A1, u 0 = 2 → u 1 ∈ ({1, 3} : Finset (Fin 4)) := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A2_first_two_second_mem : ∀ u ∈ A2, u 0 = 2 → u 1 ∈ ({1, 2, 3} : Finset (Fin 4)) := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A3_first_two_second_mem : ∀ u ∈ A3, u 0 = 2 → u 1 ∈ ({1, 2} : Finset (Fin 4)) := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A0_first_zero_or_three_second_mem :
    ∀ u ∈ A0, (u 0 = 0 ∨ u 0 = 3) → u 1 ∈ ({0, 1, 2} : Finset (Fin 4)) := by
  native_decide

set_option linter.style.nativeDecide false in
lemma A2_first_zero_or_three_second_mem :
    ∀ u ∈ A2, (u 0 = 0 ∨ u 0 = 3) → u 1 ∈ ({0, 1, 2} : Finset (Fin 4)) := by
  native_decide

theorem codeModel444_28_card : codeModel444_28.card = 28 := by
  native_decide

theorem codeModel444_28_free : CodeModelFree 4 4 3 codeModel444_28 := by
  sorry

theorem codeModel444_28_lower_bound : 28 ≤ codeModelNumber 4 4 3 := by
  have hcard : codeModel444_28.card = 28 := codeModel444_28_card
  have hle := card_le_codeModelNumber (q := 4) (k := 4) (m := 3) (C := codeModel444_28)
    codeModel444_28_free
  simpa [hcard] using hle

end FormalConjectures.Problems.Erdos.E20.Compendium
