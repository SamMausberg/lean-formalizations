import FormalConjectures.Problems.Erdos.E20.ProjectionTransfer

open Finset

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Hereditary Bounded-Alphabet Projection Growth

This file gives a clean finite model of the hereditary projection-growth recursion from the user's
note.

We work with finite `Q`-ary codes of length `n`, i.e. finite subsets of `Fin n → Fin Q`.
The two main hypotheses are:

* an adaptive one-step projection bound: every code in the class has some coordinate whose
  deletion loses at most a factor `lam`;
* a fixed-order bound: along the distinguished "delete the last coordinate" order, the step from
  length `n + 1` to length `n` is either `lam`-good or only bounded by the trivial alphabet factor
  `Q`.

The outputs are honest maximal-size recurrences:

* `maxSize_succ_le_of_adaptiveProjectionBound`:
  `M(n + 1) ≤ lam M(n)`, hence `M(n) ≤ lam^n`;
* `maxSize_succ_le_of_fixedOrderProjectionBound`:
  `M(n + 1) ≤ (if good n then lam else Q) M(n)`;
* `maxSize_block_le_basePow_of_fixedOrderDensity`:
  for a rational density `δ = a / b`, if at least `a m` of the first `b m` fixed-order steps are
  `lam`-good, then `M(b m) ≤ (Q^(b-a) * lam^a)^m`.
-/

/-- Length-`n` words over an alphabet of size `Q`. -/
abbrev Word (Q n : ℕ) := Fin n → Fin Q

/-- Finite `Q`-ary codes of length `n`. -/
abbrev Code (Q n : ℕ) := Finset (Word Q n)

/-- Delete the coordinate `i` from a word of length `n + 1`. -/
def deleteCoordWord {Q n : ℕ} (i : Fin (n + 1)) (w : Word Q (n + 1)) : Word Q n :=
  Fin.removeNth i w

/-- Delete the coordinate `i` from every word in a code. -/
def deleteCoordCode {Q n : ℕ} (i : Fin (n + 1)) (C : Code Q (n + 1)) : Code Q n :=
  C.image (deleteCoordWord (Q := Q) i)

/-- The fixed-order projection: delete the last coordinate. -/
def dropLastWord {Q n : ℕ} : Word Q (n + 1) → Word Q n :=
  deleteCoordWord (Q := Q) (Fin.last n)

/-- The corresponding fixed-order projection on codes. -/
def dropLastCode {Q n : ℕ} (C : Code Q (n + 1)) : Code Q n :=
  deleteCoordCode (Q := Q) (Fin.last n) C

/-- A length-graded class of finite `Q`-ary codes. -/
abbrev CodeClass (Q : ℕ) := ∀ n, Set (Code Q n)

/-- The class is hereditary under one-coordinate deletions. -/
def Hereditary {Q : ℕ} (K : CodeClass Q) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃C : Code Q (n + 1)⦄, K (n + 1) C →
    ∀ i : Fin (n + 1), K n (deleteCoordCode (Q := Q) i C)

/-- Adaptive projection growth: every descendant admits some coordinate deletion with loss at most
`lam`. -/
def HasAdaptiveProjectionBound {Q L : ℕ} (K : CodeClass Q) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃C : Code Q (n + 1)⦄, K (n + 1) C →
    ∃ i : Fin (n + 1), C.card ≤ L * (deleteCoordCode (Q := Q) i C).card

/-- Fixed-order projection growth: if the step `n ↦ n + 1` is declared good, then deleting the last
coordinate loses at most a factor `lam`. -/
def HasFixedOrderProjectionBound {Q L : ℕ} (K : CodeClass Q) (good : ℕ → Prop) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃C : Code Q (n + 1)⦄, K (n + 1) C → good n →
    C.card ≤ L * (dropLastCode (Q := Q) C).card

/-- The finite search space of all length-`n` codes. -/
def allCodes (Q n : ℕ) : Finset (Code Q n) :=
  (Finset.univ : Finset (Word Q n)).powerset

/-- The maximal cardinality of a code in the class at length `n`. -/
noncomputable def maxSize {Q : ℕ} (K : CodeClass Q) (n : ℕ) : ℕ :=
  by
    classical
    exact (allCodes Q n).sup fun C => if K n C then C.card else 0

@[simp] theorem mem_allCodes {Q n : ℕ} (C : Code Q n) : C ∈ allCodes Q n := by
  refine Finset.mem_powerset.mpr ?_
  intro x hx
  simp

theorem card_le_maxSize {Q : ℕ} {K : CodeClass Q} {n : ℕ} {C : Code Q n}
    (hC : K n C) : C.card ≤ maxSize K n := by
  classical
  unfold maxSize
  refine Finset.le_sup_of_le (mem_allCodes C) ?_
  simp [hC]

theorem maxSize_le_of_forall {Q : ℕ} {K : CodeClass Q} {n B : ℕ}
    (hB : ∀ C : Code Q n, K n C → C.card ≤ B) : maxSize K n ≤ B := by
  classical
  unfold maxSize
  refine Finset.sup_le ?_
  intro C hC
  by_cases hKC : K n C
  · simpa [hKC] using hB C hKC
  · simp only [hKC, if_false, zero_le]

theorem card_le_one_of_zeroLength {Q : ℕ} (C : Code Q 0) : C.card ≤ 1 := by
  simpa [Code, Word] using (Finset.card_le_univ C)

theorem maxSize_zero_le_one {Q : ℕ} {K : CodeClass Q} : maxSize K 0 ≤ 1 := by
  apply maxSize_le_of_forall
  intro C hC
  exact card_le_one_of_zeroLength C

theorem eq_of_dropLastWord_eq_and_last_eq {Q n : ℕ} {u v : Word Q (n + 1)}
    (hdrop : dropLastWord (Q := Q) u = dropLastWord (Q := Q) v)
    (hlast : u (Fin.last n) = v (Fin.last n)) : u = v := by
  calc
    u = Fin.insertNth (Fin.last n) (u (Fin.last n)) (dropLastWord (Q := Q) u) := by
      symm
      exact Fin.insertNth_self_removeNth (Fin.last n) u
    _ = Fin.insertNth (Fin.last n) (v (Fin.last n)) (dropLastWord (Q := Q) v) := by
      simp [hdrop, hlast]
    _ = v := by
      exact Fin.insertNth_self_removeNth (Fin.last n) v

theorem card_fiberOver_dropLast_le_alphabet {Q n : ℕ} (C : Code Q (n + 1)) (u : Word Q n) :
    (fiberOver C (dropLastWord (Q := Q)) u).card ≤ Q := by
  let S : Code Q (n + 1) := fiberOver C (dropLastWord (Q := Q)) u
  have hinj : Set.InjOn (fun w : Word Q (n + 1) => w (Fin.last n)) S := by
    intro x hx y hy hxy
    apply eq_of_dropLastWord_eq_and_last_eq (Q := Q)
    · exact (mem_fiberOver_iff.mp hx).2.trans (mem_fiberOver_iff.mp hy).2.symm
    · exact hxy
  calc
    S.card = (S.image fun w : Word Q (n + 1) => w (Fin.last n)).card := by
      symm
      exact Finset.card_image_of_injOn hinj
    _ ≤ (Finset.univ : Finset (Fin Q)).card := by
      exact Finset.card_le_card (by intro a ha; simp)
    _ = Q := by simp

theorem card_le_alphabet_mul_card_dropLast {Q n : ℕ} (C : Code Q (n + 1)) :
    C.card ≤ Q * (dropLastCode (Q := Q) C).card := by
  calc
    C.card =
        ∑ u ∈ C.image (dropLastWord (Q := Q)),
          (fiberOver C (dropLastWord (Q := Q)) u).card := by
      simpa [dropLastCode] using
        card_eq_sum_card_fiberOver_image C (dropLastWord (Q := Q))
    _ ≤ ∑ _u ∈ C.image (dropLastWord (Q := Q)), Q := by
      refine Finset.sum_le_sum ?_
      intro u hu
      exact card_fiberOver_dropLast_le_alphabet (Q := Q) C u
    _ = (C.image (dropLastWord (Q := Q))).card * Q := by
      simp [Nat.mul_comm]
    _ = Q * (dropLastCode (Q := Q) C).card := by
      rw [Nat.mul_comm]
      rfl

/-- Exact one-step recurrence for the adaptive, descendant-wise reordered variant. -/
theorem maxSize_succ_le_of_adaptiveProjectionBound {Q L : ℕ} {K : CodeClass Q}
    (hHered : Hereditary K) (hGrow : HasAdaptiveProjectionBound (Q := Q) (L := L) K) (n : ℕ) :
    maxSize K (n + 1) ≤ L * maxSize K n := by
  apply maxSize_le_of_forall
  intro C hC
  rcases hGrow (C := C) hC with ⟨i, hstep⟩
  have hChild : K n (deleteCoordCode (Q := Q) i C) := hHered (C := C) hC i
  calc
    C.card ≤ L * (deleteCoordCode (Q := Q) i C).card := hstep
    _ ≤ L * maxSize K n := by
      exact Nat.mul_le_mul_left _ (card_le_maxSize (K := K) hChild)

/-- The adaptive recurrence iterates to the base `lam`. -/
theorem maxSize_le_lambda_pow_of_adaptiveProjectionBound {Q L : ℕ} {K : CodeClass Q}
    (hHered : Hereditary K) (hGrow : HasAdaptiveProjectionBound (Q := Q) (L := L) K) :
    ∀ n, maxSize K n ≤ L ^ n := by
  intro n
  induction n with
  | zero =>
      simpa using maxSize_zero_le_one (K := K)
  | succ n ih =>
      calc
        maxSize K (n + 1) ≤ L * maxSize K n :=
          maxSize_succ_le_of_adaptiveProjectionBound (Q := Q) (L := L) hHered hGrow n
        _ ≤ L * L ^ n := Nat.mul_le_mul_left _ ih
        _ = L ^ (n + 1) := by
          rw [pow_succ]
          ac_rfl

/-- Number of `lam`-good fixed-order steps among the first `n` deletions. -/
def goodStepCount (good : ℕ → Prop) [DecidablePred good] (n : ℕ) : ℕ :=
  ((Finset.range n).filter good).card

theorem goodStepCount_le (good : ℕ → Prop) [DecidablePred good] (n : ℕ) :
    goodStepCount good n ≤ n := by
  simpa [goodStepCount] using (Finset.card_filter_le (s := Finset.range n) (p := good))

@[simp] theorem goodStepCount_zero (good : ℕ → Prop) [DecidablePred good] :
    goodStepCount good 0 = 0 := by
  simp [goodStepCount]

@[simp] theorem goodStepCount_succ (good : ℕ → Prop) [DecidablePred good] (n : ℕ) :
    goodStepCount good (n + 1) = goodStepCount good n + if good n then 1 else 0 := by
  by_cases hg : good n
  · simp [goodStepCount, Finset.range_add_one, Finset.filter_insert, hg]
  · simp [goodStepCount, Finset.range_add_one, Finset.filter_insert, hg]

/-- Exact one-step recurrence for a fixed coordinate order. The good steps contribute `lam`; the
others only use the trivial bounded-alphabet factor `Q`. -/
theorem maxSize_succ_le_of_fixedOrderProjectionBound
    {Q L : ℕ} {K : CodeClass Q} {good : ℕ → Prop} [DecidablePred good]
    (hHered : Hereditary K) (hGood : HasFixedOrderProjectionBound (Q := Q) (L := L) K good)
    (n : ℕ) :
    maxSize K (n + 1) ≤ (if good n then L else Q) * maxSize K n := by
  by_cases hg : good n
  · apply maxSize_le_of_forall
    intro C hC
    have hstep : C.card ≤ L * (dropLastCode (Q := Q) C).card := hGood (C := C) hC hg
    have hChild : K n (dropLastCode (Q := Q) C) := hHered (C := C) hC (Fin.last n)
    calc
      C.card ≤ L * (dropLastCode (Q := Q) C).card := hstep
      _ ≤ L * maxSize K n := by
        exact Nat.mul_le_mul_left _ (card_le_maxSize (K := K) hChild)
      _ = (if good n then L else Q) * maxSize K n := by simp [hg]
  · apply maxSize_le_of_forall
    intro C hC
    have hChild : K n (dropLastCode (Q := Q) C) := hHered (C := C) hC (Fin.last n)
    calc
      C.card ≤ Q * (dropLastCode (Q := Q) C).card :=
        card_le_alphabet_mul_card_dropLast (Q := Q) C
      _ ≤ Q * maxSize K n := by
        exact Nat.mul_le_mul_left _ (card_le_maxSize (K := K) hChild)
      _ = (if good n then L else Q) * maxSize K n := by simp [hg]

/-- Closed-form bound obtained by iterating the fixed-order recurrence. -/
theorem maxSize_le_of_fixedOrderProjectionBound
    {Q L : ℕ} {K : CodeClass Q} {good : ℕ → Prop} [DecidablePred good]
    (hHered : Hereditary K) (hGood : HasFixedOrderProjectionBound (Q := Q) (L := L) K good) :
    ∀ n, maxSize K n ≤ Q ^ (n - goodStepCount good n) * L ^ goodStepCount good n := by
  intro n
  induction n with
  | zero =>
      simpa using maxSize_zero_le_one (K := K)
  | succ n ih =>
      by_cases hg : good n
      · set t := goodStepCount good n
        have ht : t ≤ n := by simpa [t] using goodStepCount_le good n
        have hstep :
            maxSize K (n + 1) ≤ L * maxSize K n := by
          simpa [hg] using
            maxSize_succ_le_of_fixedOrderProjectionBound
              (Q := Q) (L := L) (K := K) (good := good) hHered hGood n
        have hcount : goodStepCount good (n + 1) = t + 1 := by
          simp [goodStepCount_succ, hg, t]
        calc
          maxSize K (n + 1) ≤ L * maxSize K n := hstep
          _ ≤ L * (Q ^ (n - t) * L ^ t) := by
            simpa [t] using Nat.mul_le_mul_left L ih
          _ = Q ^ ((n + 1) - goodStepCount good (n + 1)) * L ^ goodStepCount good (n + 1) := by
            calc
              L * (Q ^ (n - t) * L ^ t) = Q ^ (n - t) * L ^ (t + 1) := by
                rw [pow_succ]
                ac_rfl
              _ = Q ^ ((n + 1) - (t + 1)) * L ^ (t + 1) := by
                have hexp : n - t = (n + 1) - (t + 1) := by omega
                rw [hexp]
              _ = Q ^ ((n + 1) - goodStepCount good (n + 1)) * L ^ goodStepCount good (n + 1) := by
                rw [hcount]
      · set t := goodStepCount good n
        have ht : t ≤ n := by simpa [t] using goodStepCount_le good n
        have hstep :
            maxSize K (n + 1) ≤ Q * maxSize K n := by
          simpa [hg] using
            maxSize_succ_le_of_fixedOrderProjectionBound
              (Q := Q) (L := L) (K := K) (good := good) hHered hGood n
        have hcount : goodStepCount good (n + 1) = t := by
          simp [goodStepCount_succ, hg, t]
        calc
          maxSize K (n + 1) ≤ Q * maxSize K n := hstep
          _ ≤ Q * (Q ^ (n - t) * L ^ t) := by
            simpa [t] using Nat.mul_le_mul_left Q ih
          _ = Q ^ ((n + 1) - goodStepCount good (n + 1)) * L ^ goodStepCount good (n + 1) := by
            calc
              Q * (Q ^ (n - t) * L ^ t) = Q ^ (n - t + 1) * L ^ t := by
                rw [pow_succ]
                ac_rfl
              _ = Q ^ ((n + 1) - t) * L ^ t := by
                have hexp : n - t + 1 = (n + 1) - t := by omega
                simp [hexp]
              _ = Q ^ ((n + 1) - goodStepCount good (n + 1)) * L ^ goodStepCount good (n + 1) := by
                rw [hcount]

lemma mixedBase_mono {Q L N m t : ℕ} (hLQ : L ≤ Q) (hm : m ≤ t) (ht : t ≤ N) :
    Q ^ (N - t) * L ^ t ≤ Q ^ (N - m) * L ^ m := by
  rcases Nat.exists_eq_add_of_le hm with ⟨d, rfl⟩
  have hpow : L ^ d ≤ Q ^ d := Nat.pow_le_pow_left hLQ d
  calc
    Q ^ (N - (m + d)) * L ^ (m + d) = (Q ^ (N - (m + d)) * L ^ m) * L ^ d := by
      rw [pow_add]
      ac_rfl
    _ ≤ (Q ^ (N - (m + d)) * L ^ m) * Q ^ d := by
      exact Nat.mul_le_mul_left _ hpow
    _ = (Q ^ (N - (m + d)) * Q ^ d) * L ^ m := by
      ac_rfl
    _ = Q ^ (N - (m + d) + d) * L ^ m := by
      rw [← pow_add]
    _ = Q ^ (N - m) * L ^ m := by
      have hexp : N - (m + d) + d = N - m := by omega
      rw [hexp]

/-- Fixed-order density corollary.

If `δ = a / b` and among the first `b m` fixed-order deletions at least `a m` are `lam`-good, then
the maximal size at length `b m` is bounded by `(Q^(b-a) * lam^a)^m`. This is the exact natural
form of the base `Q^(1-δ) * lam^δ`. -/
theorem maxSize_block_le_basePow_of_fixedOrderDensity
    {Q L : ℕ} {K : CodeClass Q} {good : ℕ → Prop} [DecidablePred good]
    (hHered : Hereditary K) (hGood : HasFixedOrderProjectionBound (Q := Q) (L := L) K good)
    (hLQ : L ≤ Q) {a b : ℕ} (_hab : a ≤ b)
    (hdense : ∀ m, a * m ≤ goodStepCount good (b * m)) :
    ∀ m, maxSize K (b * m) ≤ (Q ^ (b - a) * L ^ a) ^ m := by
  intro m
  have hclosed :=
    maxSize_le_of_fixedOrderProjectionBound
      (Q := Q) (L := L) (K := K) (good := good) hHered hGood (b * m)
  have hmono :
      Q ^ (b * m - goodStepCount good (b * m)) * L ^ goodStepCount good (b * m) ≤
        Q ^ (b * m - a * m) * L ^ (a * m) := by
    exact mixedBase_mono (Q := Q) (L := L) (N := b * m) (m := a * m)
      (t := goodStepCount good (b * m)) hLQ (hdense m) (goodStepCount_le good (b * m))
  calc
    maxSize K (b * m) ≤ Q ^ (b * m - goodStepCount good (b * m)) * L ^ goodStepCount good (b * m) :=
      hclosed
    _ ≤ Q ^ (b * m - a * m) * L ^ (a * m) := hmono
    _ = (Q ^ (b - a) * L ^ a) ^ m := by
      have hsub : b * m - a * m = (b - a) * m := by
        simpa [Nat.mul_comm] using (Nat.sub_mul b a m).symm
      rw [hsub, Nat.pow_mul, Nat.pow_mul]
      symm
      exact Nat.mul_pow (Q ^ (b - a)) (L ^ a) m

end FormalConjectures.Problems.Erdos.E20
