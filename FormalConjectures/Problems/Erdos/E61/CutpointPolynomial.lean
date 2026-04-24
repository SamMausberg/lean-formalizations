import FormalConjectures.Problems.Erdos.E61.CutpointFull
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Explicit polynomial one-switch extraction

This file adds the concrete square-root extraction bound used as the polynomial
step in `thm:cutpoint-canonization`, and its iterated `m^(2^k) -> m`
form for the `d^2` cutpoint-comparison relations.
-/

namespace Erdos61

open Finset

def OrderedPairHomogeneous (R : ℕ → ℕ → Prop) (I : Finset ℕ) : Prop :=
  (∀ x ∈ I, ∀ y ∈ I, x < y → R x y) ∨
    ∀ x ∈ I, ∀ y ∈ I, x < y → ¬ R x y

/-- The exponent appearing in the paper's polynomial cutpoint-canonization bound. -/
def cutpointCanonizationExponent (d : ℕ) : ℕ :=
  2 ^ (d * d + d - 1)

theorem cutpointCanonizationExponent_decomposition {d : ℕ} (hd : 1 ≤ d) :
    cutpointCanonizationExponent d = 2 ^ (d - 1) * 2 ^ (d * d) := by
  rw [cutpointCanonizationExponent]
  have hsum : d * d + d - 1 = (d - 1) + d * d := by omega
  rw [hsum, pow_add]

/-- The `r`-th consecutive block of length `m` in `{0, ..., m*m-1}`. -/
def oneSwitchBlock (m : ℕ) (r : Fin m) : Finset ℕ :=
  Finset.Ico (r.val * m) ((r.val + 1) * m)

@[simp] theorem oneSwitchBlock_card (m : ℕ) (r : Fin m) :
    (oneSwitchBlock m r).card = m := by
  dsimp [oneSwitchBlock]
  rw [Nat.card_Ico]
  have hle : r.val * m ≤ (r.val + 1) * m :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  rw [Nat.sub_eq_iff_eq_add hle]
  ring

theorem oneSwitchBlock_ordered (m : ℕ) :
    ∀ ⦃r s : Fin m⦄, r < s →
      ∀ x ∈ oneSwitchBlock m r, ∀ y ∈ oneSwitchBlock m s, x < y := by
  intro r s hrs x hx y hy
  dsimp [oneSwitchBlock] at hx hy
  rw [mem_Ico] at hx hy
  have hrsnat : r.val + 1 ≤ s.val := by omega
  calc
    x < (r.val + 1) * m := hx.2
    _ ≤ s.val * m := Nat.mul_le_mul_right m hrsnat
    _ ≤ y := hy.1

/--
Concrete square-root form of `lem:one-switch`: a suffix-row relation on the first
`m*m` natural-number positions has a homogeneous ordered subset of size at least
`m`.
-/
theorem one_switch_extraction_square_bound
    {R : ℕ → ℕ → Prop} (hR : HasSuffixRows R) (m : ℕ) :
    ∃ I : Finset ℕ, I ⊆ Finset.Iio (m * m) ∧ m ≤ I.card ∧
      OrderedPairHomogeneous R I := by
  classical
  rcases one_switch_extraction_from_ordered_blocks hR (oneSwitchBlock m)
      (by intro r; rw [oneSwitchBlock_card])
      (oneSwitchBlock_ordered m) with ⟨I, hpack⟩
  rcases hpack with ⟨hIsub_blocks, hIlarge, hhom⟩
  refine ⟨I, ?_, hIlarge, hhom⟩
  intro x hx
  rcases mem_biUnion.mp (hIsub_blocks hx) with ⟨r, _hr, hxr⟩
  rw [mem_Iio]
  dsimp [oneSwitchBlock] at hxr
  rw [mem_Ico] at hxr
  calc
    x < (r.val + 1) * m := hxr.2
    _ ≤ m * m := by
      have hr : r.val + 1 ≤ m := r.isLt
      exact Nat.mul_le_mul_right m hr

theorem one_switch_extraction_square_bound_finset
    {R : ℕ → ℕ → Prop} (hR : HasSuffixRows R)
    (S : Finset ℕ) (m : ℕ) (hS : m * m ≤ S.card) :
    ∃ I : Finset ℕ, I ⊆ S ∧ m ≤ I.card ∧ OrderedPairHomogeneous R I := by
  classical
  by_cases hm0 : m = 0
  · refine ⟨∅, by simp, by omega, Or.inl ?_⟩
    simp
  · let e := S.orderEmbOfCardLe hS
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    let idx : Fin m → Fin m → Fin (m * m) := fun r c =>
      ⟨r.val * m + c.val, by
        calc
          r.val * m + c.val < r.val * m + m := Nat.add_lt_add_left c.isLt _
          _ = (r.val + 1) * m := by ring
          _ ≤ m * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt r.isLt)⟩
    let block : Fin m → Finset ℕ := fun r =>
      Finset.univ.image fun c : Fin m => e (idx r c)
    have hlarge : ∀ r, m ≤ (block r).card := by
      intro r
      have hinj : Set.InjOn (fun c : Fin m => e (idx r c))
          ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
        intro c _hc d _hd hcd
        have hidx : idx r c = idx r d := e.injective hcd
        apply Fin.ext
        have hval := congrArg Fin.val hidx
        dsimp [idx] at hval
        omega
      change m ≤ (Finset.univ.image (fun c : Fin m => e (idx r c))).card
      rw [Finset.card_image_of_injOn hinj]
      simp
    have hordered : ∀ ⦃r s : Fin m⦄, r < s →
        ∀ x ∈ block r, ∀ y ∈ block s, x < y := by
      intro r s hrs x hx y hy
      rcases Finset.mem_image.mp hx with ⟨c, _hc, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨d, _hd, rfl⟩
      apply e.strictMono
      have hrsnat : r.val + 1 ≤ s.val := by omega
      change (idx r c).val < (idx s d).val
      dsimp [idx]
      calc
        r.val * m + c.val < (r.val + 1) * m := by
          calc
            r.val * m + c.val < r.val * m + m := Nat.add_lt_add_left c.isLt _
            _ = (r.val + 1) * m := by ring
        _ ≤ s.val * m := Nat.mul_le_mul_right m hrsnat
        _ ≤ s.val * m + d.val := Nat.le_add_right _ _
    rcases one_switch_extraction_from_ordered_blocks hR block hlarge hordered with
      ⟨I, hIsub, hIcard, hIhom⟩
    refine ⟨I, ?_, hIcard, hIhom⟩
    intro x hx
    rcases mem_biUnion.mp (hIsub hx) with ⟨r, _hr, hxr⟩
    rcases Finset.mem_image.mp hxr with ⟨c, _hc, rfl⟩
    exact S.orderEmbOfCardLe_mem hS (idx r c)

theorem iterated_one_switch_extraction :
    ∀ (k m : ℕ) (rels : Fin k → ℕ → ℕ → Prop),
      (∀ r, HasSuffixRows (rels r)) →
      ∀ S : Finset ℕ, m ^ (2 ^ k) ≤ S.card →
        ∃ I : Finset ℕ, I ⊆ S ∧ m ≤ I.card ∧
          ∀ r : Fin k, OrderedPairHomogeneous (rels r) I
  | 0, m, rels, _hrels, S, hS => by
      classical
      have hmle : m ≤ S.card := by simpa using hS
      rcases exists_subset_card_eq hmle with ⟨I, hIS, hIcard⟩
      refine ⟨I, hIS, by omega, ?_⟩
      intro r
      exact Fin.elim0 r
  | k + 1, m, rels, hrels, S, hS => by
      classical
      let relsInit : Fin k → ℕ → ℕ → Prop := fun r => rels r.castSucc
      have hrelsInit : ∀ r, HasSuffixRows (relsInit r) := by
        intro r
        exact hrels r.castSucc
      have hpow : (m * m) ^ (2 ^ k) = m ^ (2 ^ (k + 1)) := by
        rw [mul_pow, ← pow_add]
        congr 1
        rw [pow_succ]
        ring
      have hSinit : (m * m) ^ (2 ^ k) ≤ S.card := by
        simpa [hpow] using hS
      rcases iterated_one_switch_extraction k (m * m) relsInit hrelsInit S hSinit with
        ⟨J, hJS, hJcard, hJhom⟩
      let last : Fin (k + 1) := ⟨k, by omega⟩
      rcases one_switch_extraction_square_bound_finset (hrels last) J m hJcard with
        ⟨I, hIJ, hIcard, hIhomLast⟩
      refine ⟨I, fun x hx => hJS (hIJ hx), hIcard, ?_⟩
      intro r
      by_cases hr : r.val < k
      · let r0 : Fin k := ⟨r.val, hr⟩
        have hr0 : r0.castSucc = r := by
          apply Fin.ext
          rfl
        rcases hJhom r0 with htrue | hfalse
        · exact Or.inl (by
            intro x hx y hy hxy
            simpa [relsInit, hr0] using htrue x (hIJ hx) y (hIJ hy) hxy)
        · exact Or.inr (by
            intro x hx y hy hxy
            simpa [relsInit, hr0] using hfalse x (hIJ hx) y (hIJ hy) hxy)
      · have hlast : r = last := by
          apply Fin.ext
          simp [last]
          omega
        simpa [hlast] using hIhomLast

theorem suffix_rows_cutpoint_relation
    {d : ℕ} (cut : Fin d → ℕ → ℕ)
    {p q : Fin d} (hqmono : Monotone (cut q)) :
    HasSuffixRows (fun x y => cut p x ≤ cut q y) := by
  intro i j k _hij hjk h
  exact h.trans (hqmono hjk)

theorem suffix_rows_cutpoint_relation_compl
    {d : ℕ} (cut : Fin d → ℕ → ℕ)
    {p q : Fin d} (hqanti : Antitone (cut q)) :
    HasSuffixRows (fun x y => ¬ cut p x ≤ cut q y) := by
  intro i j k _hij hjk h hle
  exact h (hle.trans (hqanti hjk))

/--
The iterated one-switch part of `thm:cutpoint-canonization`, with the explicit
polynomial bound.  Once the cutpoint coordinates are monotone or antitone on an
ordered core, `d^2` successive square-root extractions turn a block of size
`m^(2^(d*d))` into a block of size at least `m` on which every comparison bit
`cut p x ≤ cut q y` is independent of the ordered pair `x<y`.
-/
theorem cutpoint_comparison_bits_polynomial_extraction
    {d m : ℕ} (cut : Fin d → ℕ → ℕ)
    (orientation : Fin d → Bool)
    (hmono : ∀ q : Fin d,
      if orientation q then Monotone (cut q) else Antitone (cut q))
    (S : Finset ℕ) (hS : m ^ (2 ^ (d * d)) ≤ S.card) :
    ∃ I : Finset ℕ, I ⊆ S ∧ m ≤ I.card ∧
      ∀ p q : Fin d, ∃ b : Bool,
        ∀ x ∈ I, ∀ y ∈ I, x < y →
          decide (cut p x ≤ cut q y) = b := by
  classical
  let pairOf : Fin (d * d) → Fin d × Fin d :=
    (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm
  let rels : Fin (d * d) → ℕ → ℕ → Prop := fun r x y =>
    if orientation (pairOf r).2 then
      cut (pairOf r).1 x ≤ cut (pairOf r).2 y
    else
      ¬ cut (pairOf r).1 x ≤ cut (pairOf r).2 y
  have hrels : ∀ r, HasSuffixRows (rels r) := by
    intro r
    dsimp [rels]
    by_cases hor : orientation (pairOf r).2
    · have hq : Monotone (cut (pairOf r).2) := by
        simpa [hor] using hmono (pairOf r).2
      simpa [hor] using
        suffix_rows_cutpoint_relation cut (p := (pairOf r).1) (q := (pairOf r).2) hq
    · have hq : Antitone (cut (pairOf r).2) := by
        simpa [hor] using hmono (pairOf r).2
      simpa [hor] using
        suffix_rows_cutpoint_relation_compl cut (p := (pairOf r).1) (q := (pairOf r).2) hq
  rcases iterated_one_switch_extraction (d * d) m rels hrels S hS with
    ⟨I, hIS, hIcard, hIhom⟩
  refine ⟨I, hIS, hIcard, ?_⟩
  intro p q
  let r : Fin (d * d) := (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)) (p, q)
  have hpair : pairOf r = (p, q) := by
    simp [pairOf, r]
  by_cases hor : orientation q
  · rcases hIhom r with htrue | hfalse
    · refine ⟨true, ?_⟩
      intro x hx y hy hxy
      have hxyR : cut p x ≤ cut q y := by
        simpa [rels, hpair, hor] using htrue x hx y hy hxy
      simp [hxyR]
    · refine ⟨false, ?_⟩
      intro x hx y hy hxy
      have hxyR : ¬ cut p x ≤ cut q y := by
        simpa [rels, hpair, hor] using hfalse x hx y hy hxy
      simp [hxyR]
  · rcases hIhom r with htrue | hfalse
    · refine ⟨false, ?_⟩
      intro x hx y hy hxy
      have hxyR : ¬ cut p x ≤ cut q y := by
        simpa [rels, hpair, hor] using htrue x hx y hy hxy
      simp [hxyR]
    · refine ⟨true, ?_⟩
      intro x hx y hy hxy
      have hxyR : cut p x ≤ cut q y := by
        by_contra hnot
        exact (hfalse x hx y hy hxy) (by
          simpa [rels, hpair, hor] using hnot)
      simp [hxyR]

end Erdos61
