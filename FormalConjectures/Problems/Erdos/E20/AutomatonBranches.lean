import Mathlib
import FormalConjectures.Problems.Erdos.E20.ProjectionTransfer
import FormalConjectures.Problems.Erdos.E20.RecurrenceReduction

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace FormalConjectures.Problems.Erdos.E20

/-!
# DFA Branch Prefixes

This file formalizes the deterministic finite-automaton branch counting from the user's
profitable-prefix note.

For a finite partial DFA:

* a length-`t + s` admissible word has a length-`t` prefix lying in one of at most `N_*(t)` branch
  cells;
* one prefix cell therefore carries at least a `1 / N_*(t)` fraction of the total;
* the maximal branch count `h_A(m,k)` satisfies `h_A(m,k) ≤ N_*(t) * h_A(m - t,k)`.

The heavy-prefix step is obtained from the generic fiber theorem in
`ProjectionTransfer.lean`, and the recurrence is packaged as a
`HasProfitableDropRecurrence` from `RecurrenceReduction.lean`.
-/

section Core

variable {Q : Type*} {σ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [DecidableEq σ]

/-- A finite deterministic branch model with partial transition function. -/
structure PartialDFA (Q : Type*) (σ : Type*) where
  step : Q → σ → Option Q

namespace PartialDFA

/-- Words of fixed length over the alphabet `σ`. -/
abbrev Word (σ : Type*) (n : ℕ) := Fin n → σ

/-- Running a DFA on a list of symbols. -/
def runList (A : PartialDFA Q σ) : Q → List σ → Option Q
  | q, [] => some q
  | q, a :: w =>
      match A.step q a with
      | none => none
      | some q' => A.runList q' w

/-- Running a DFA on a fixed-length word. -/
def run (A : PartialDFA Q σ) {n : ℕ} (q : Q) (w : Word σ n) : Option Q :=
  A.runList q (List.ofFn w)

@[simp] theorem runList_nil (A : PartialDFA Q σ) (q : Q) :
    A.runList q [] = some q := rfl

@[simp] theorem runList_cons (A : PartialDFA Q σ) (q : Q) (a : σ) (w : List σ) :
    A.runList q (a :: w) =
      match A.step q a with
      | none => none
      | some q' => A.runList q' w := rfl

theorem runList_append (A : PartialDFA Q σ) (q : Q) (u v : List σ) :
    A.runList q (u ++ v) = Option.bind (A.runList q u) (fun r => A.runList r v) := by
  induction u generalizing q with
  | nil =>
      simp [runList]
  | cons a u ihu =>
      simp [runList, ihu]
      split <;> simp

theorem run_append (A : PartialDFA Q σ) (q : Q) {t s : ℕ}
    (u : Word σ t) (v : Word σ s) :
    A.run q (Fin.append u v) = Option.bind (A.run q u) (fun r => A.run r v) := by
  simp [run, runList_append, List.ofFn_fin_append]

/-- The admissible length-`n` words from a state `q`. -/
def admissibleWords (A : PartialDFA Q σ) (q : Q) (n : ℕ) : Finset (Word σ n) :=
  Finset.univ.filter fun w => (A.run q w).isSome

/-- The number of admissible length-`n` branches from state `q`. -/
def continuationCount (A : PartialDFA Q σ) (n : ℕ) (q : Q) : ℕ :=
  (A.admissibleWords q n).card

theorem mem_admissibleWords_iff (A : PartialDFA Q σ) {q : Q} {n : ℕ} {w : Word σ n} :
    w ∈ A.admissibleWords q n ↔ ∃ r, A.run q w = some r := by
  by_cases h : A.run q w = none
  · simp [admissibleWords, h]
  · cases hrun : A.run q w with
    | none =>
        contradiction
    | some r =>
        simp [admissibleWords, hrun]

@[simp] theorem continuationCount_zero (A : PartialDFA Q σ) (q : Q) :
    A.continuationCount 0 q = 1 := by
  simp [continuationCount, admissibleWords, run]

/-- The first `t` symbols of a length-`t + s` word. -/
def prefixWord {t s : ℕ} (w : Word σ (t + s)) : Word σ t :=
  fun i => w (Fin.castAdd s i)

/-- The last `s` symbols of a length-`t + s` word. -/
def suffixWord {t s : ℕ} (w : Word σ (t + s)) : Word σ s :=
  fun i => w (Fin.natAdd t i)

theorem append_prefix_suffix {t s : ℕ} (w : Word σ (t + s)) :
    Fin.append (α := σ) (prefixWord w) (suffixWord w) = w := by
  simpa [prefixWord, suffixWord] using (Fin.append_castAdd_natAdd (f := w))

theorem prefixWord_append {t s : ℕ} (u : Word σ t) (v : Word σ s) :
    prefixWord (Fin.append u v) = u := by
  ext i
  simp [prefixWord]

theorem suffixWord_append {t s : ℕ} (u : Word σ t) (v : Word σ s) :
    suffixWord (Fin.append u v) = v := by
  ext i
  simp [suffixWord]

/-- Prefix fibers inside the admissible length-`t + s` words. -/
def prefixFiber (A : PartialDFA Q σ) (q : Q) (t s : ℕ) (u : Word σ t) :
    Finset (Word σ (t + s)) :=
  fiberOver (A.admissibleWords q (t + s)) prefixWord u

@[simp] theorem mem_prefixFiber_iff (A : PartialDFA Q σ)
    {q : Q} {t s : ℕ} {u : Word σ t} {w : Word σ (t + s)} :
    w ∈ A.prefixFiber q t s u ↔
      w ∈ A.admissibleWords q (t + s) ∧ prefixWord w = u := by
  simp [prefixFiber, fiberOver]

theorem prefix_admissible_of_full_admissible (A : PartialDFA Q σ)
    {q : Q} {t s : ℕ} {w : Word σ (t + s)}
    (hw : w ∈ A.admissibleWords q (t + s)) :
    prefixWord w ∈ A.admissibleWords q t := by
  rcases (mem_admissibleWords_iff (A := A)).1 hw with ⟨r, hr⟩
  have happend :
      A.run q (Fin.append (prefixWord w) (suffixWord w)) = some r := by
    simpa [append_prefix_suffix] using hr
  cases hprefix : A.run q (prefixWord w) with
  | none =>
      simp [run_append, hprefix] at happend
  | some r0 =>
      exact (mem_admissibleWords_iff (A := A)).2 ⟨r0, hprefix⟩

theorem projectedCode_subset_admissibleWords (A : PartialDFA Q σ) (q : Q) (t s : ℕ) :
    projectedCode (A.admissibleWords q (t + s)) (Fin.castAdd s) ⊆ A.admissibleWords q t := by
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
  simpa [projectedCode, selectCoords, prefixWord] using
    A.prefix_admissible_of_full_admissible hw

theorem projectedCode_card_le_continuationCount (A : PartialDFA Q σ) (q : Q) (t s : ℕ) :
    (projectedCode (A.admissibleWords q (t + s)) (Fin.castAdd s)).card ≤
      A.continuationCount t q := by
  calc
    (projectedCode (A.admissibleWords q (t + s)) (Fin.castAdd s)).card
        ≤ (A.admissibleWords q t).card := by
          exact Finset.card_le_card (A.projectedCode_subset_admissibleWords q t s)
    _ = A.continuationCount t q := rfl

noncomputable def prefixFiberEquiv (A : PartialDFA Q σ)
    {q r : Q} {t s : ℕ} {u : Word σ t} (hru : A.run q u = some r) :
    ↥(A.admissibleWords r s) ≃ ↥(A.prefixFiber q t s u) where
  toFun v :=
    ⟨Fin.append u v.1, by
      refine (mem_prefixFiber_iff (A := A) (q := q) (t := t) (s := s) (u := u)).2 ?_
      constructor
      · rcases (mem_admissibleWords_iff (A := A)).1 v.2 with ⟨r', hr'⟩
        exact (mem_admissibleWords_iff (A := A)).2 ⟨r', by simpa [run_append, hru, hr']⟩
      · exact prefixWord_append u v.1⟩
  invFun w :=
    ⟨suffixWord w.1, by
      rcases (mem_prefixFiber_iff (A := A) (q := q) (t := t) (s := s) (u := u)).1 w.2 with
        ⟨hw, hprefix⟩
      rcases (mem_admissibleWords_iff (A := A)).1 hw with ⟨r', hr'⟩
      have happend :
          A.run q (Fin.append (prefixWord w.1) (suffixWord w.1)) = some r' := by
        simpa [append_prefix_suffix] using hr'
      cases hsuf : A.run r (suffixWord w.1) with
      | none =>
          simp [run_append, hru, hprefix, hsuf] at happend
      | some r0 =>
          exact (mem_admissibleWords_iff (A := A)).2 ⟨r0, hsuf⟩⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    simp [suffixWord_append]
  right_inv w := by
    apply Subtype.ext
    calc
      Fin.append u (suffixWord w.1) = Fin.append (prefixWord w.1) (suffixWord w.1) := by
        simp [(mem_prefixFiber_iff (A := A) (q := q) (t := t) (s := s) (u := u)).1 w.2 |>.2]
      _ = w.1 := append_prefix_suffix _

@[simp] theorem card_prefixFiber (A : PartialDFA Q σ)
    {q r : Q} {t s : ℕ} {u : Word σ t} (hru : A.run q u = some r) :
    (A.prefixFiber q t s u).card = A.continuationCount s r := by
  rw [continuationCount]
  rw [← Fintype.card_coe (A.admissibleWords r s)]
  rw [← Fintype.card_coe (A.prefixFiber q t s u)]
  exact Fintype.card_congr
    ((prefixFiberEquiv (A := A) (q := q) (r := r) (t := t) (s := s) hru).symm)

/-- The maximum number of admissible length-`t` branches from a single state. -/
def NStar (A : PartialDFA Q σ) (t : ℕ) : ℕ :=
  Finset.univ.sup fun q => A.continuationCount t q

theorem continuationCount_le_NStar (A : PartialDFA Q σ) (t : ℕ) (q : Q) :
    A.continuationCount t q ≤ A.NStar t := by
  exact Finset.le_sup (by simp)

theorem admissibleWords_nonempty_of_count_pos (A : PartialDFA Q σ)
    {q : Q} {n : ℕ} (hcount : 0 < A.continuationCount n q) :
    (A.admissibleWords q n).Nonempty := by
  exact Finset.card_pos.mp hcount

/-- Exact heavy-prefix theorem with the local bound `1 / continuationCount t q`. -/
theorem exists_heavy_prefix_local (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    ∃ u ∈ A.admissibleWords q t, ∃ r,
      A.run q u = some r ∧
      A.continuationCount (t + s) q ≤
        A.continuationCount t q * A.continuationCount s r := by
  let C := A.admissibleWords q (t + s)
  let ι : Fin t → Fin (t + s) := Fin.castAdd s
  have hC : C.Nonempty := A.admissibleWords_nonempty_of_count_pos hcount
  have hB : (projectedCode C ι).card ≤ A.continuationCount t q := by
    simpa [C, ι] using A.projectedCode_card_le_continuationCount q t s
  obtain ⟨u, huCode, hlarge⟩ :=
    exists_large_projectedFiber_of_card_bound C ι hC hB
  have huAdm : u ∈ A.admissibleWords q t := A.projectedCode_subset_admissibleWords q t s huCode
  rcases (mem_admissibleWords_iff (A := A)).1 huAdm with ⟨r, hru⟩
  refine ⟨u, huAdm, r, hru, ?_⟩
  calc
    A.continuationCount (t + s) q = C.card := rfl
    _ ≤ A.continuationCount t q * (projectedFiber C ι u).card := hlarge
    _ = A.continuationCount t q * A.continuationCount s r := by
          congr 1
          change (A.prefixFiber q t s u).card = A.continuationCount s r
          simpa [C, ι, projectedFiber, prefixFiber, fiberOver, selectCoords, prefixWord] using
            (card_prefixFiber (A := A) (q := q) (r := r) (t := t) (s := s) hru)

/-- Global heavy-prefix theorem, using the uniform branch bound `N_*(t)`. -/
theorem exists_heavy_prefix (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    ∃ u ∈ A.admissibleWords q t, ∃ r,
      A.run q u = some r ∧
      A.continuationCount (t + s) q ≤ A.NStar t * A.continuationCount s r := by
  obtain ⟨u, hu, r, hru, hineq⟩ := A.exists_heavy_prefix_local hcount
  refine ⟨u, hu, r, hru, ?_⟩
  calc
    A.continuationCount (t + s) q ≤ A.continuationCount t q * A.continuationCount s r := hineq
    _ ≤ A.NStar t * A.continuationCount s r := by
          exact Nat.mul_le_mul_right _ (A.continuationCount_le_NStar t q)

theorem NStar_pos_of_count_pos (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    0 < A.NStar t := by
  obtain ⟨u, hu, _r, _hru, _⟩ := A.exists_heavy_prefix_local hcount
  have hlocal : 0 < A.continuationCount t q := Finset.card_pos.mpr ⟨u, hu⟩
  exact lt_of_lt_of_le hlocal (A.continuationCount_le_NStar t q)

/-- Ratio form of the heavy-prefix theorem: some length-`t` branch captures at least a
`1 / N_*(t)` fraction of the admissible length-`t + s` branches. -/
theorem exists_heavy_prefix_ratio (A : PartialDFA Q σ) {q : Q} {t s : ℕ}
    (hcount : 0 < A.continuationCount (t + s) q) :
    ∃ u ∈ A.admissibleWords q t,
      (1 : ℚ) / (A.NStar t : ℚ) ≤
        ((A.prefixFiber q t s u).card : ℚ) / (A.continuationCount (t + s) q : ℚ) := by
  obtain ⟨u, hu, r, hru, hineq⟩ := A.exists_heavy_prefix hcount
  refine ⟨u, hu, ?_⟩
  have hNpos : 0 < (A.NStar t : ℚ) := by
    exact_mod_cast A.NStar_pos_of_count_pos hcount
  have hTpos : 0 < (A.continuationCount (t + s) q : ℚ) := by
    exact_mod_cast hcount
  have hineqQ :
      (A.continuationCount (t + s) q : ℚ) ≤
        (A.NStar t : ℚ) * (A.continuationCount s r : ℚ) := by
    exact_mod_cast hineq
  have hdiv :
      (1 : ℚ) / (A.NStar t : ℚ) ≤
        (A.continuationCount s r : ℚ) / (A.continuationCount (t + s) q : ℚ) := by
    rw [_root_.le_div_iff₀ hTpos]
    have hscaled :
        ((1 : ℚ) / (A.NStar t : ℚ)) * (A.continuationCount (t + s) q : ℚ) ≤
          ((1 : ℚ) / (A.NStar t : ℚ)) * ((A.NStar t : ℚ) * (A.continuationCount s r : ℚ)) := by
      exact mul_le_mul_of_nonneg_left hineqQ (by positivity)
    have hNne : (A.NStar t : ℚ) ≠ 0 := by positivity
    simpa [div_eq_mul_inv, hNne, mul_assoc, mul_left_comm, mul_comm] using hscaled
  simpa [card_prefixFiber (A := A) (q := q) (r := r) (t := t) (s := s) hru] using hdiv

theorem continuationCount_le_NStar_mul_NStar (A : PartialDFA Q σ)
    {m t : ℕ} (ht : t ≤ m) (q : Q) :
    A.continuationCount m q ≤ A.NStar t * A.NStar (m - t) := by
  by_cases hzero : A.continuationCount m q = 0
  · simp [hzero]
  · have hpos : 0 < A.continuationCount m q := Nat.pos_of_ne_zero hzero
    let s := m - t
    have hm : m = t + s := by
      simp [s, Nat.add_sub_of_le ht]
    obtain ⟨u, hu, r, hru, hineq⟩ :=
      A.exists_heavy_prefix (q := q) (t := t) (s := s) (by simpa [hm] using hpos)
    calc
      A.continuationCount m q = A.continuationCount (t + s) q := by simp [hm]
      _ ≤ A.NStar t * A.continuationCount s r := hineq
      _ ≤ A.NStar t * A.NStar s := by
            exact Nat.mul_le_mul_left _ (A.continuationCount_le_NStar s r)
      _ = A.NStar t * A.NStar (m - t) := by simp [s]

theorem NStar_recurrence (A : PartialDFA Q σ) {m t : ℕ} (ht : t ≤ m) :
    A.NStar m ≤ A.NStar t * A.NStar (m - t) := by
  refine Finset.sup_le ?_
  intro q hq
  exact A.continuationCount_le_NStar_mul_NStar ht q

/-- `h_A(m,k)`: the maximal length-`m` branch count among automata states, provided the automaton
has at most `k` states.  If the state bound fails, we record `0`. -/
def hA (A : PartialDFA Q σ) (m k : ℕ) : ℕ :=
  if Fintype.card Q ≤ k then A.NStar m else 0

theorem hA_eq_NStar (A : PartialDFA Q σ) {m k : ℕ} (hk : Fintype.card Q ≤ k) :
    A.hA m k = A.NStar m := by
  simp [hA, hk]

theorem hA_recurrence (A : PartialDFA Q σ) {m t k : ℕ} (ht : t ≤ m) :
    A.hA m k ≤ A.NStar t * A.hA (m - t) k := by
  by_cases hk : Fintype.card Q ≤ k
  · simpa only [hA, hk] using A.NStar_recurrence ht
  · simp [hA, hk]

theorem hA_nonneg (A : PartialDFA Q σ) (m k : ℕ) :
    0 ≤ (A.hA m k : ℝ) := by
  positivity

/-- The exact DFA recurrence packaged in the `RecurrenceReduction` interface. -/
theorem hasProfitableDropRecurrence_hA (A : PartialDFA Q σ) (k t : ℕ) (ht : 0 < t) :
    HasProfitableDropRecurrence (fun m => (A.hA m k : ℝ)) (A.NStar t) 1 (t - 1) := by
  intro m hm
  refine ⟨1, by omega, by omega, ?_⟩
  have htm : t ≤ m := by omega
  have hrec := A.hA_recurrence (m := m) (t := t) (k := k) htm
  have hsub : m - (t - 1) - 1 = m - t := by omega
  calc
    (A.hA m k : ℝ) ≤ (A.NStar t : ℝ) * (A.hA (m - t) k : ℝ) := by
      exact_mod_cast hrec
    _ = (A.NStar t : ℝ) * (1 : ℝ) ^ (1 : ℕ) * (A.hA (m - (t - 1) - 1) k : ℝ) := by
          simp [hsub, mul_assoc]

end PartialDFA

end Core

end FormalConjectures.Problems.Erdos.E20
