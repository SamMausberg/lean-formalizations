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
  fin_cases r <;> decide

set_option linter.style.nativeDecide false in
lemma A2_row_card_lt_four : ∀ r : Fin 4, (A2.filter (fun u => u 0 = r)).card < 4 := by
  intro r
  fin_cases r <;> decide

set_option linter.style.nativeDecide false in
lemma A1_col_card_lt_four : ∀ r : Fin 4, (A1.filter (fun u => u 1 = r)).card < 4 := by
  intro r
  fin_cases r <;> decide

set_option linter.style.nativeDecide false in
lemma A0_no_first_one : ∀ u ∈ A0, u 0 ≠ 1 := by
  decide

set_option linter.style.nativeDecide false in
lemma A2_no_first_one : ∀ u ∈ A2, u 0 ≠ 1 := by
  decide

set_option linter.style.nativeDecide false in
lemma A3_no_first_one : ∀ u ∈ A3, u 0 ≠ 1 := by
  decide

set_option linter.style.nativeDecide false in
lemma A1_first_one_eq_zero : ∀ u ∈ A1, u 0 = 1 → u 1 = 0 := by
  decide

set_option linter.style.nativeDecide false in
lemma A0_first_two_second_mem : ∀ u ∈ A0, u 0 = 2 → u 1 ∈ ({2, 3} : Finset (Fin 4)) := by
  decide

set_option linter.style.nativeDecide false in
lemma A1_first_two_second_mem : ∀ u ∈ A1, u 0 = 2 → u 1 ∈ ({1, 3} : Finset (Fin 4)) := by
  decide

set_option linter.style.nativeDecide false in
lemma A2_first_two_second_mem : ∀ u ∈ A2, u 0 = 2 → u 1 ∈ ({1, 2, 3} : Finset (Fin 4)) := by
  decide

set_option linter.style.nativeDecide false in
lemma A3_first_two_second_mem : ∀ u ∈ A3, u 0 = 2 → u 1 ∈ ({1, 2} : Finset (Fin 4)) := by
  decide

set_option linter.style.nativeDecide false in
lemma A0_first_zero_or_three_second_mem :
    ∀ u ∈ A0, (u 0 = 0 ∨ u 0 = 3) → u 1 ∈ ({0, 1, 2} : Finset (Fin 4)) := by
  decide

set_option linter.style.nativeDecide false in
lemma A2_first_zero_or_three_second_mem :
    ∀ u ∈ A2, (u 0 = 0 ∨ u 0 = 3) → u 1 ∈ ({0, 1, 2} : Finset (Fin 4)) := by
  decide

theorem codeModel444_28_card : codeModel444_28.card = 28 := by
  decide

set_option linter.style.nativeDecide false in
lemma pairOf_mem_A0_of_mem_codeModel444_28 :
    ∀ x ∈ codeModel444_28, x 0 = 0 → pairOf x ∈ A0 := by
  decide

set_option linter.style.nativeDecide false in
lemma pairOf_mem_A1_of_mem_codeModel444_28 :
    ∀ x ∈ codeModel444_28, x 0 = 1 → pairOf x ∈ A1 := by
  decide

set_option linter.style.nativeDecide false in
lemma pairOf_mem_A2_of_mem_codeModel444_28 :
    ∀ x ∈ codeModel444_28, x 0 = 2 → pairOf x ∈ A2 := by
  decide

set_option linter.style.nativeDecide false in
lemma pairOf_mem_A3_of_mem_codeModel444_28 :
    ∀ x ∈ codeModel444_28, x 0 = 3 → pairOf x ∈ A3 := by
  decide

set_option linter.style.nativeDecide false in
lemma A0_codeModelFree :
  ∀ f : Fin 4 → Fin 2 → Fin 4,
      Function.Injective f →
      (∀ i, f i ∈ A0) →
      ∃ j : Fin 2, ¬(∀ a b : Fin 4, f a j = f b j) ∧
        ¬ Function.Injective (fun a => f a j) := by
  unfold Function.Injective
  native_decide

set_option linter.style.nativeDecide false in
lemma A1_codeModelFree :
  ∀ f : Fin 4 → Fin 2 → Fin 4,
      Function.Injective f →
      (∀ i, f i ∈ A1) →
      ∃ j : Fin 2, ¬(∀ a b : Fin 4, f a j = f b j) ∧
        ¬ Function.Injective (fun a => f a j) := by
  unfold Function.Injective
  native_decide

set_option linter.style.nativeDecide false in
lemma A2_codeModelFree :
  ∀ f : Fin 4 → Fin 2 → Fin 4,
      Function.Injective f →
      (∀ i, f i ∈ A2) →
      ∃ j : Fin 2, ¬(∀ a b : Fin 4, f a j = f b j) ∧
        ¬ Function.Injective (fun a => f a j) := by
  unfold Function.Injective
  native_decide

set_option linter.style.nativeDecide false in
lemma A3_codeModelFree :
  ∀ f : Fin 4 → Fin 2 → Fin 4,
      Function.Injective f →
      (∀ i, f i ∈ A3) →
      ∃ j : Fin 2, ¬(∀ a b : Fin 4, f a j = f b j) ∧
        ¬ Function.Injective (fun a => f a j) := by
  unfold Function.Injective
  native_decide

set_option linter.style.nativeDecide false in
lemma crossFibers_codeModelFree :
    ∀ u0 ∈ A0, ∀ u1 ∈ A1, ∀ u2 ∈ A2, ∀ u3 ∈ A3,
      ∃ j : Fin 2,
        ¬(∀ a b : Fin 4, (![u0, u1, u2, u3] a) j = (![u0, u1, u2, u3] b) j) ∧
          ¬ Function.Injective (fun a : Fin 4 => (![u0, u1, u2, u3] a) j) := by
  unfold Function.Injective
  native_decide

theorem codeModel444_28_free : CodeModelFree 4 4 3 codeModel444_28 := by
  intro f hfInj hfMem
  by_contra hbad
  have hcoord :
      ∀ j : Fin 3,
        (∀ a b : Fin 4, f a j = f b j) ∨
          Function.Injective (fun a : Fin 4 => f a j) := by
    intro j
    by_cases hall : ∀ a b : Fin 4, f a j = f b j
    · exact Or.inl hall
    · by_cases hinj : Function.Injective (fun a : Fin 4 => f a j)
      · exact Or.inr hinj
      · exact False.elim (hbad ⟨j, hall, hinj⟩)
  let g : Fin 4 → Fin 2 → Fin 4 := fun i => pairOf (f i)
  have hgInj_of_first_constant
      (hall0 : ∀ a b : Fin 4, f a 0 = f b 0) :
      Function.Injective g := by
    intro a b hab
    apply hfInj
    funext j
    fin_cases j
    · exact hall0 a b
    · exact congrArg (fun x : Fin 2 → Fin 4 => x 0) hab
    · exact congrArg (fun x : Fin 2 → Fin 4 => x 1) hab
  have lift_fiber_bad
      (hfiber :
        ∃ j : Fin 2, ¬(∀ a b : Fin 4, g a j = g b j) ∧
          ¬ Function.Injective (fun a => g a j)) :
      ∃ j : Fin 3, ¬(∀ a b : Fin 4, f a j = f b j) ∧
        ¬ Function.Injective (fun a => f a j) := by
    rcases hfiber with ⟨j, hnotConst, hnotInj⟩
    refine ⟨j.succ, ?_, ?_⟩
    · intro hall
      apply hnotConst
      intro a b
      fin_cases j <;> simpa [g, pairOf] using hall a b
    · intro hinj
      apply hnotInj
      intro a b hab
      apply hinj
      fin_cases j <;> simpa [g, pairOf] using hab
  rcases hcoord 0 with hall0 | hinj0
  · have hgInj : Function.Injective g := hgInj_of_first_constant hall0
    cases h00 : f 0 0 with
    | mk v hv =>
      interval_cases v
      · have hmem : ∀ i, g i ∈ A0 := by
          intro i
          apply pairOf_mem_A0_of_mem_codeModel444_28
          · exact hfMem i
          · simpa [h00] using hall0 i 0
        exact hbad (lift_fiber_bad (A0_codeModelFree g hgInj hmem))
      · have hmem : ∀ i, g i ∈ A1 := by
          intro i
          apply pairOf_mem_A1_of_mem_codeModel444_28
          · exact hfMem i
          · simpa [h00] using hall0 i 0
        exact hbad (lift_fiber_bad (A1_codeModelFree g hgInj hmem))
      · have hmem : ∀ i, g i ∈ A2 := by
          intro i
          apply pairOf_mem_A2_of_mem_codeModel444_28
          · exact hfMem i
          · simpa [h00] using hall0 i 0
        exact hbad (lift_fiber_bad (A2_codeModelFree g hgInj hmem))
      · have hmem : ∀ i, g i ∈ A3 := by
          intro i
          apply pairOf_mem_A3_of_mem_codeModel444_28
          · exact hfMem i
          · simpa [h00] using hall0 i 0
        exact hbad (lift_fiber_bad (A3_codeModelFree g hgInj hmem))
  · have hsurj0 : Function.Surjective (fun a : Fin 4 => f a 0) :=
      Finite.surjective_of_injective hinj0
    let pre : Fin 4 → Fin 4 := fun i => Classical.choose (hsurj0 i)
    have hpre : ∀ i : Fin 4, f (pre i) 0 = i := fun i => Classical.choose_spec (hsurj0 i)
    let u : Fin 4 → Fin 2 → Fin 4 := fun i => pairOf (f (pre i))
    have hu0 : u 0 ∈ A0 := by
      apply pairOf_mem_A0_of_mem_codeModel444_28
      · exact hfMem (pre 0)
      · exact hpre 0
    have hu1 : u 1 ∈ A1 := by
      apply pairOf_mem_A1_of_mem_codeModel444_28
      · exact hfMem (pre 1)
      · exact hpre 1
    have hu2 : u 2 ∈ A2 := by
      apply pairOf_mem_A2_of_mem_codeModel444_28
      · exact hfMem (pre 2)
      · exact hpre 2
    have hu3 : u 3 ∈ A3 := by
      apply pairOf_mem_A3_of_mem_codeModel444_28
      · exact hfMem (pre 3)
      · exact hpre 3
    rcases crossFibers_codeModelFree (u 0) hu0 (u 1) hu1 (u 2) hu2 (u 3) hu3 with
      ⟨j, hnotConst, hnotInj⟩
    have htuple :
        (fun a : Fin 4 => (![u 0, u 1, u 2, u 3] a) j) = fun a => u a j := by
      funext a
      fin_cases a <;> simp
    have hfull_good := hcoord j.succ
    rcases hfull_good with hall | hinj
    · apply hnotConst
      intro a b
      have ha : (![u 0, u 1, u 2, u 3] a) = u a := by
        fin_cases a <;> simp
      have hb : (![u 0, u 1, u 2, u 3] b) = u b := by
        fin_cases b <;> simp
      have ha_j := congrArg (fun x : Fin 2 → Fin 4 => x j) ha
      have hb_j := congrArg (fun x : Fin 2 → Fin 4 => x j) hb
      calc
        (![u 0, u 1, u 2, u 3] a) j = (u a) j := ha_j
        _ = (u b) j := by
          fin_cases j <;> simpa [u, pairOf] using hall (pre a) (pre b)
        _ = (![u 0, u 1, u 2, u 3] b) j := hb_j.symm
    · apply hnotInj
      intro a b hab
      have ha : (![u 0, u 1, u 2, u 3] a) = u a := by
        fin_cases a <;> simp
      have hb : (![u 0, u 1, u 2, u 3] b) = u b := by
        fin_cases b <;> simp
      have habu : u a j = u b j := by
        have ha_j := congrArg (fun x : Fin 2 → Fin 4 => x j) ha
        have hb_j := congrArg (fun x : Fin 2 → Fin 4 => x j) hb
        calc
          (u a) j = (![u 0, u 1, u 2, u 3] a) j := ha_j.symm
          _ = (![u 0, u 1, u 2, u 3] b) j := hab
          _ = (u b) j := hb_j
      have hpre_eq : pre a = pre b := by
        apply hinj
        fin_cases j <;> simpa [u, pairOf] using habu
      have hcoord_eq := congrArg (fun x : Fin 4 => f x 0) hpre_eq
      simpa [hpre] using hcoord_eq

theorem codeModel444_28_lower_bound : 28 ≤ codeModelNumber 4 4 3 := by
  have hcard : codeModel444_28.card = 28 := codeModel444_28_card
  have hle := card_le_codeModelNumber (q := 4) (k := 4) (m := 3) (C := codeModel444_28)
    codeModel444_28_free
  simpa [hcard] using hle

end FormalConjectures.Problems.Erdos.E20.Compendium
