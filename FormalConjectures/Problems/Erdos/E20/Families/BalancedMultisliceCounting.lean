import FormalConjectures.Problems.Erdos.E20.Families.BalancedMultislice

namespace FormalConjectures.Problems.Erdos.E20

open Finset BigOperators

/-!
# Balanced Multislice Counting

This file isolates finite counting facts for the balanced multislice from
`BalancedMultislice.lean`.
-/

/-- Symbol count for words on an arbitrary finite coordinate type. -/
def symbolCountOn {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (x : ι → Fin q) (a : Fin q) : ℕ :=
  ((Finset.univ : Finset ι).filter fun i => x i = a).card

/-- Words on an arbitrary finite coordinate type with prescribed symbol counts. -/
def wordsWithCountsOn (ι : Type*) [Fintype ι] [DecidableEq ι]
    (q : ℕ) (m : Fin q → ℕ) : Finset (ι → Fin q) :=
  Finset.univ.filter fun x => ∀ a : Fin q, symbolCountOn x a = m a

@[simp] theorem mem_wordsWithCountsOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} {m : Fin q → ℕ} {x : ι → Fin q} :
    x ∈ wordsWithCountsOn ι q m ↔ ∀ a : Fin q, symbolCountOn x a = m a := by
  simp [wordsWithCountsOn]

/-- Words with a prescribed count for every symbol. -/
def wordsWithSymbolCounts (n q : ℕ) (m : Fin q → ℕ) : Finset (Fin n → Fin q) :=
  Finset.univ.filter fun x => ∀ a : Fin q, symbolCount x a = m a

@[simp] theorem mem_wordsWithSymbolCounts {n q : ℕ} {m : Fin q → ℕ}
    {x : Fin n → Fin q} :
    x ∈ wordsWithSymbolCounts n q m ↔ ∀ a : Fin q, symbolCount x a = m a := by
  simp [wordsWithSymbolCounts]

theorem balancedWords_eq_wordsWithSymbolCounts (n q : ℕ) :
    balancedWords n q = wordsWithSymbolCounts n q (fun _ => n / q) := by
  ext x
  simp [IsBalancedWord, wordsWithSymbolCounts]

theorem symbolCountOn_fin_eq_symbolCount {n q : ℕ} (x : Fin n → Fin q) (a : Fin q) :
    symbolCountOn x a = symbolCount x a := rfl

theorem wordsWithCountsOn_fin_eq_wordsWithSymbolCounts
    (n q : ℕ) (m : Fin q → ℕ) :
    wordsWithCountsOn (Fin n) q m = wordsWithSymbolCounts n q m := by
  rfl

theorem card_wordsWithCountsOn_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Fin 1 → ℕ) (hsum : ∑ a : Fin 1, m a = Fintype.card ι) :
    (wordsWithCountsOn ι 1 m).card = Nat.multinomial Finset.univ m := by
  classical
  have hm0 : m 0 = Fintype.card ι := by
    simpa using hsum
  have hpred : ∀ x : ι → Fin 1, ∀ a : Fin 1, symbolCountOn x a = m a := by
    intro x a
    have hfilter :
        ((Finset.univ : Finset ι).filter fun i => x i = a) = Finset.univ := by
      ext i
      simp [Subsingleton.elim (x i) a]
    have ha : a = 0 := Subsingleton.elim a 0
    rw [symbolCountOn, hfilter, Finset.card_univ, ha, hm0]
  have hwords : wordsWithCountsOn ι 1 m = Finset.univ := by
    ext x
    constructor
    · intro _
      exact Finset.mem_univ x
    · intro _
      exact mem_wordsWithCountsOn.mpr (hpred x)
  rw [hwords]
  simp

/-- The coordinates on which a word over `Fin (q + 2)` takes the zero symbol. -/
def zeroSymbolFiber {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (x : ι → Fin (q + 2)) : Finset ι :=
  (Finset.univ : Finset ι).filter fun i => x i = 0

@[simp] theorem mem_zeroSymbolFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} {x : ι → Fin (q + 2)} {i : ι} :
    i ∈ zeroSymbolFiber x ↔ x i = 0 := by
  simp [zeroSymbolFiber]

lemma symbolCountOn_tail_zeroSymbolFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (x : ι → Fin (q + 2)) (a : Fin (q + 1)) :
    symbolCountOn
        (fun i : {i : ι // i ∉ zeroSymbolFiber x} =>
          Fin.predAbove (0 : Fin (q + 1)) (x i.1)) a =
      symbolCountOn x a.succ := by
  classical
  rw [symbolCountOn, symbolCountOn,
    ← Fintype.card_subtype (fun i : {i : ι // i ∉ zeroSymbolFiber x} =>
      Fin.predAbove (0 : Fin (q + 1)) (x i.1) = a),
    ← Fintype.card_subtype (fun i : ι => x i = a.succ)]
  refine Fintype.card_congr ?_
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left
      right_inv := ?right }
  · intro i
    refine ⟨i.1.1, ?_⟩
    have hne : x i.1.1 ≠ 0 := by
      intro hzero
      exact i.1.2 (by simp [hzero])
    have hsucc : Fin.succ (Fin.predAbove (0 : Fin (q + 1)) (x i.1.1)) = x i.1.1 := by
      simpa using Fin.succ_predAbove_zero (j := x i.1.1) hne
    rw [← hsucc, i.2]
  · intro i
    refine ⟨⟨i.1, ?_⟩, ?_⟩
    · intro hi
      have hzero : x i.1 = 0 := (mem_zeroSymbolFiber (x := x) (i := i.1)).mp hi
      have hsucc_zero : a.succ = 0 := by
        rw [← i.2, hzero]
      exact Fin.succ_ne_zero a hsucc_zero
    · simp [i.2]
  · intro i
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro i
    apply Subtype.ext
    rfl

/-- Insert a zero-symbol fiber back into a word over the nonzero symbols. -/
def insertZeroFiberWord {ι : Type*} [DecidableEq ι] {q : ℕ}
    (S : Finset ι) (y : {i : ι // i ∉ S} → Fin (q + 1)) : ι → Fin (q + 2) :=
  fun i => if h : i ∈ S then 0 else (y ⟨i, h⟩).succ

lemma symbolCountOn_insertZeroFiberWord_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (S : Finset ι) (y : {i : ι // i ∉ S} → Fin (q + 1)) :
    symbolCountOn (insertZeroFiberWord S y) 0 = S.card := by
  classical
  have hfilter :
      ((Finset.univ : Finset ι).filter fun i => insertZeroFiberWord S y i = 0) = S := by
    ext i
    by_cases hi : i ∈ S
    · simp [insertZeroFiberWord, hi]
    · simp [insertZeroFiberWord, hi]
  rw [symbolCountOn, hfilter]

lemma symbolCountOn_insertZeroFiberWord_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (S : Finset ι) (y : {i : ι // i ∉ S} → Fin (q + 1)) (a : Fin (q + 1)) :
    symbolCountOn (insertZeroFiberWord S y) a.succ = symbolCountOn y a := by
  classical
  rw [symbolCountOn, symbolCountOn,
    ← Fintype.card_subtype (fun i : ι => insertZeroFiberWord S y i = a.succ),
    ← Fintype.card_subtype (fun i : {i : ι // i ∉ S} => y i = a)]
  refine Fintype.card_congr ?_
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left
      right_inv := ?right }
  · intro i
    have hiS : i.1 ∉ S := by
      intro hi
      have hzero : insertZeroFiberWord S y i.1 = 0 := by
        simp [insertZeroFiberWord, hi]
      have hsucc_zero : a.succ = 0 := by
        rw [← i.2, hzero]
      exact Fin.succ_ne_zero a hsucc_zero
    refine ⟨⟨i.1, hiS⟩, ?_⟩
    simpa [insertZeroFiberWord, hiS] using i.2
  · intro i
    refine ⟨i.1.1, ?_⟩
    simp [insertZeroFiberWord, i.1.2, i.2]
  · intro i
    apply Subtype.ext
    rfl
  · intro i
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem zeroSymbolFiber_insertZeroFiberWord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (S : Finset ι) (y : {i : ι // i ∉ S} → Fin (q + 1)) :
    zeroSymbolFiber (insertZeroFiberWord S y) = S := by
  ext i
  by_cases hi : i ∈ S
  · simp [insertZeroFiberWord, hi]
  · simp [insertZeroFiberWord, hi]

/-- The word obtained from an equivalence `Fin n ≃ Fin q × Fin r` by reading the
`Fin q` coordinate. -/
noncomputable def productWord {n q r : ℕ} (e : Fin n ≃ Fin q × Fin r) : Fin n → Fin q :=
  fun i => (e i).1

theorem symbolCount_productWord {n q r : ℕ} (e : Fin n ≃ Fin q × Fin r) (a : Fin q) :
    symbolCount (productWord e) a = r := by
  classical
  rw [symbolCount, ← Fintype.card_subtype (fun i : Fin n => productWord e i = a)]
  calc
    Fintype.card {i : Fin n // productWord e i = a} = Fintype.card (Fin r) := by
      apply Fintype.card_congr
      refine
        { toFun := fun i => (e i.1).2
          invFun := fun t => ⟨e.symm (a, t), by simp [productWord]⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro i
        apply Subtype.ext
        change e.symm (a, (e i.1).2) = i.1
        have hpair : (a, (e i.1).2) = e i.1 := by
          ext
          · exact congrArg Fin.val i.2.symm
          · rfl
        rw [hpair]
        simp
      · intro t
        simp
    _ = r := Fintype.card_fin r

theorem productWord_mem_balancedWords_of_mul_eq {n q r : ℕ}
    (hn : n = q * r) (e : Fin n ≃ Fin q × Fin r) :
    productWord e ∈ balancedWords n q := by
  rw [mem_balancedWords]
  intro a
  rw [symbolCount_productWord]
  by_cases hq : q = 0
  · subst hq
    exact Fin.elim0 a
  · rw [hn, Nat.mul_div_right _ (Nat.pos_of_ne_zero hq)]

/-- An arbitrary product equivalence adjusted so that one prescribed coordinate is sent
to one prescribed product point. -/
noncomputable def productEquivSending {n q r : ℕ} (hn : n = q * r)
    (i : Fin n) (p : Fin q × Fin r) : Fin n ≃ Fin q × Fin r :=
  let e : Fin n ≃ Fin q × Fin r := Fintype.equivOfCardEq (by
    simp [hn, Fintype.card_prod])
  e.trans (Equiv.swap (e i) p)

@[simp] theorem productEquivSending_apply {n q r : ℕ} (hn : n = q * r)
    (i : Fin n) (p : Fin q × Fin r) :
    productEquivSending hn i p i = p := by
  simp [productEquivSending]

theorem two_le_coordinateCount_balancedWords_of_mul_eq {n q r : ℕ}
    (hn : n = q * r) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    ∀ i : Fin n, ∀ a : Fin q,
      2 ≤ coordinateCount (G := Fin q) (balancedWords n q) i a := by
  classical
  intro i a
  obtain ⟨b, hba⟩ : ∃ b : Fin q, b ≠ a := by
    apply Fintype.exists_ne_of_one_lt_card
    simpa [Fintype.card_fin] using hq
  let t0 : Fin r := Fin.mk 0 (by omega)
  obtain ⟨t, htt0⟩ : ∃ t : Fin r, t ≠ t0 := by
    apply Fintype.exists_ne_of_one_lt_card
    simpa [Fintype.card_fin] using hr
  let e : Fin n ≃ Fin q × Fin r := productEquivSending hn i (a, t0)
  let e' : Fin n ≃ Fin q × Fin r := e.trans (Equiv.swap (a, t) (b, t))
  let x : Fin n → Fin q := productWord e
  let y : Fin n → Fin q := productWord e'
  have hxbal : x ∈ balancedWords n q := productWord_mem_balancedWords_of_mul_eq hn e
  have hybal : y ∈ balancedWords n q := productWord_mem_balancedWords_of_mul_eq hn e'
  have hxi : x i = a := by
    simp [x, productWord, e]
  have hyi : y i = a := by
    have hleft : (a, t0) ≠ (a, t) := by
      intro h
      have ht : t = t0 := by
        simpa using (congrArg Prod.snd h).symm
      exact htt0 ht
    have hright : (a, t0) ≠ (b, t) := by
      intro h
      have hab : a = b := by
        simpa using congrArg Prod.fst h
      exact hba hab.symm
    have hswap : Equiv.swap (a, t) (b, t) (a, t0) = (a, t0) :=
      Equiv.swap_apply_of_ne_of_ne hleft hright
    simp [y, productWord, e', e, hswap]
  have hxy : x ≠ y := by
    intro h
    let j : Fin n := e.symm (a, t)
    have hxj : x j = a := by
      simp [x, productWord, j]
    have hyj : y j = b := by
      simp [y, productWord, e', j]
    have hab : a = b := by
      have hxyj : x j = y j := congrFun h j
      rw [hxj, hyj] at hxyj
      exact hxyj
    exact hba hab.symm
  unfold coordinateCount
  have hlt : 1 < ((balancedWords n q).filter fun x => x i = a).card := by
    apply Finset.one_lt_card.mpr
    refine ⟨x, ?_, y, ?_, hxy⟩
    · exact Finset.mem_filter.mpr ⟨hxbal, hxi⟩
    · exact Finset.mem_filter.mpr ⟨hybal, hyi⟩
  omega

theorem two_le_vertexDegree_balancedMultisliceFamily_of_mul_eq {n q r : ℕ}
    (hn : n = q * r) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (i : Fin n) (a : Fin q) :
    2 ≤ vertexDegree' (balancedMultisliceFamily n q) (i, a) := by
  rw [vertexDegree_balancedMultisliceFamily_eq_coordinateCount]
  exact two_le_coordinateCount_balancedWords_of_mul_eq hn hq hr i a

theorem nonLeafVertices_balancedMultisliceFamily_eq_univ_of_mul_eq {n q r : ℕ}
    (hn : n = q * r) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    nonLeafVertices (balancedMultisliceFamily n q) = Finset.univ := by
  apply nonLeafVertices_balancedMultisliceFamily_eq_univ_of_two_le_coordinateCount
  exact two_le_coordinateCount_balancedWords_of_mul_eq hn hq hr

end FormalConjectures.Problems.Erdos.E20
