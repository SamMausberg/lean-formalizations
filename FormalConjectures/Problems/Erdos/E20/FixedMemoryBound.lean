import Mathlib
import FormalConjectures.Problems.Erdos.E20.ProjectionTransfer

open Finset

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Fixed-Memory Forbidden-Block Bounds

This file formalizes the exact counting step behind the user's fixed-memory note.

Rather than encode a full sliding-window automaton, we package only the data needed for the
counting argument:

* a length-graded `q`-ary language;
* closure under deleting the last `r` symbols;
* one globally forbidden block of length `r`.

Every proper `q`-ary `r`-step sliding-window branch yields such a package after choosing any
missing length-`r` block.  The core consequence is the exact recursion

`|L_{n + r}| ≤ (q^r - 1) |L_n|`,

and hence the closed-form block bound

`|L_n| ≤ q^(n % r) (q^r - 1)^(n / r)`.
-/

/-- Length-`n` words over an alphabet of size `q`. -/
abbrev QWord (q n : ℕ) := Fin n → Fin q

/-- The first `n` symbols of a word of length `n + r`. -/
def prefixWord {q n r : ℕ} (w : QWord q (n + r)) : QWord q n :=
  fun i => w (Fin.castAdd r i)

/-- The last `r` symbols of a word of length `n + r`. -/
def suffixWord {q n r : ℕ} (w : QWord q (n + r)) : QWord q r :=
  fun i => w (Fin.natAdd n i)

theorem append_prefix_suffix {q n r : ℕ} (w : QWord q (n + r)) :
    Fin.append (prefixWord w) (suffixWord w) = w := by
  simpa [prefixWord, suffixWord] using (Fin.append_castAdd_natAdd (f := w))

/-- Abstract data extracted from a proper fixed-memory branch after choosing one forbidden
length-`r` block. -/
structure FixedMemoryBranch (q r : ℕ) where
  language : ∀ n, Finset (QWord q n)
  prefix_closed :
    ∀ {n : ℕ} {w : QWord q (n + r)}, w ∈ language (n + r) → prefixWord w ∈ language n
  forbiddenBlock : QWord q r
  forbidden_suffix :
    ∀ {n : ℕ} (u : QWord q n), Fin.append u forbiddenBlock ∉ language (n + r)

namespace FixedMemoryBranch

variable {q r : ℕ} (X : FixedMemoryBranch q r)

/-- Prefix fibers inside the length-`n + r` language. -/
def prefixFiber (n : ℕ) (u : QWord q n) : Finset (QWord q (n + r)) :=
  fiberOver (X.language (n + r)) prefixWord u

theorem image_prefix_subset (n : ℕ) :
    (X.language (n + r)).image prefixWord ⊆ X.language n := by
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
  exact X.prefix_closed hw

theorem suffixWord_injOn_prefixFiber (n : ℕ) (u : QWord q n) :
    Set.InjOn suffixWord (↑(X.prefixFiber n u) : Set (QWord q (n + r))) := by
  intro x hx y hy hxy
  have hpx : prefixWord x = u := (mem_fiberOver_iff.mp hx).2
  have hpy : prefixWord y = u := (mem_fiberOver_iff.mp hy).2
  calc
    x = Fin.append (prefixWord x) (suffixWord x) := by
      symm
      exact append_prefix_suffix x
    _ = Fin.append (prefixWord y) (suffixWord y) := by
      simp [hpx, hpy, hxy]
    _ = y := append_prefix_suffix y

theorem card_prefixFiber_le (n : ℕ) (u : QWord q n) :
    (X.prefixFiber n u).card ≤ q ^ r - 1 := by
  let S : Finset (QWord q r) := (X.prefixFiber n u).image suffixWord
  have hcard :
      (X.prefixFiber n u).card = S.card := by
    dsimp [S]
    symm
    exact Finset.card_image_of_injOn (X.suffixWord_injOn_prefixFiber n u)
  have hforbidden :
      X.forbiddenBlock ∉ S := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨w, hw, hsuf⟩
    have hwLang : w ∈ X.language (n + r) := (mem_fiberOver_iff.mp hw).1
    have hpref : prefixWord w = u := (mem_fiberOver_iff.mp hw).2
    have hwEq : w = Fin.append u X.forbiddenBlock := by
      calc
        w = Fin.append (prefixWord w) (suffixWord w) := by
          symm
          exact append_prefix_suffix w
        _ = Fin.append u X.forbiddenBlock := by
          simp [hpref, hsuf]
    exact X.forbidden_suffix (n := n) u (by simpa [hwEq] using hwLang)
  have hsubset : S ⊆ (Finset.univ : Finset (QWord q r)).erase X.forbiddenBlock := by
    intro v hv
    have hvne : v ≠ X.forbiddenBlock := by
      intro hEq
      exact hforbidden (by simpa [S, hEq] using hv)
    simp [hvne]
  calc
    (X.prefixFiber n u).card = S.card := hcard
    _ ≤ ((Finset.univ : Finset (QWord q r)).erase X.forbiddenBlock).card :=
      Finset.card_le_card hsubset
    _ = q ^ r - 1 := by
      rw [Finset.card_erase_of_mem (by simp)]
      simp [QWord]

/-- Exact `r`-step recursion: once one forbidden block is fixed, every prefix loses at least one
length-`r` continuation. -/
theorem card_language_add_le (n : ℕ) :
    (X.language (n + r)).card ≤ (q ^ r - 1) * (X.language n).card := by
  calc
    (X.language (n + r)).card =
        ∑ u ∈ (X.language (n + r)).image prefixWord, (X.prefixFiber n u).card := by
          simpa [prefixFiber] using card_eq_sum_card_fiberOver_image (X.language (n + r)) prefixWord
    _ ≤ ∑ _u ∈ (X.language (n + r)).image prefixWord, (q ^ r - 1) := by
          exact Finset.sum_le_sum (fun u hu => X.card_prefixFiber_le n u)
    _ = ((X.language (n + r)).image prefixWord).card * (q ^ r - 1) := by
          rw [Finset.sum_const_nat]
          intro u hu
          rfl
    _ ≤ (X.language n).card * (q ^ r - 1) := by
          exact Nat.mul_le_mul_right (q ^ r - 1) (Finset.card_le_card (X.image_prefix_subset n))
    _ = (q ^ r - 1) * (X.language n).card := by
          rw [Nat.mul_comm]

theorem card_language_le_alphabet_pow (n : ℕ) :
    (X.language n).card ≤ q ^ n := by
  simpa [QWord] using (Finset.card_le_univ (s := X.language n))

/-- Closed-form block bound obtained by iterating the exact `n ↦ n + r` recursion. -/
theorem card_language_block_bound (s m : ℕ) :
    (X.language (s + r * m)).card ≤ q ^ s * (q ^ r - 1) ^ m := by
  induction m with
  | zero =>
      simpa using X.card_language_le_alphabet_pow s
  | succ m ih =>
      have hlen : s + r * (m + 1) = (s + r * m) + r := by
        simp [Nat.mul_succ, Nat.add_left_comm, Nat.add_comm]
      have hstep :
          (X.language ((s + r * m) + r)).card ≤
            (q ^ r - 1) * (X.language (s + r * m)).card := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          X.card_language_add_le (s + r * m)
      calc
        (X.language (s + r * (m + 1))).card
            = (X.language ((s + r * m) + r)).card := by
                rw [hlen]
        _ ≤ (q ^ r - 1) * (X.language (s + r * m)).card := hstep
        _ ≤ (q ^ r - 1) * (q ^ s * (q ^ r - 1) ^ m) := by
              exact Nat.mul_le_mul_left _ ih
        _ = q ^ s * (q ^ r - 1) ^ (m + 1) := by
              rw [pow_succ]
              ac_rfl

/-- Closed form for arbitrary `n`, split into its remainder modulo `r` and its quotient. -/
theorem card_language_bound (n : ℕ) :
    (X.language n).card ≤ q ^ (n % r) * (q ^ r - 1) ^ (n / r) := by
  by_cases hr : 0 < r
  · have hcard :
        (X.language (n % r + r * (n / r))).card = (X.language n).card := by
      simpa using congrArg (fun t => (X.language t).card) (Nat.mod_add_div n r)
    calc
      (X.language n).card = (X.language (n % r + r * (n / r))).card := by
        simpa using hcard.symm
      _ ≤ q ^ (n % r) * (q ^ r - 1) ^ (n / r) :=
        X.card_language_block_bound (s := n % r) (m := n / r)
  · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    simpa [hr0] using X.card_language_le_alphabet_pow n

end FixedMemoryBranch

end FormalConjectures.Problems.Erdos.E20
