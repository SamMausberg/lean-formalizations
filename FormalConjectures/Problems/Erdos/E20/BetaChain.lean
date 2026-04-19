import Mathlib
import FormalConjectures.Problems.Erdos.E20.Counterexample

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- All `t`-subsets of the ambient ground set. -/
def levelSets (t : ℕ) : Finset (Finset α) :=
  (Finset.univ : Finset α).powersetCard t

@[simp] theorem mem_levelSets {t : ℕ} {B : Finset α} :
    B ∈ levelSets t ↔ B.card = t := by
  simp [levelSets]

/-- The first moment `Λ_t(F) = Σ_{|B|=t} d(B)`. -/
noncomputable def lambdaLevel (H : Finset (Finset α)) (t : ℕ) : ℕ :=
  Finset.sum (levelSets t) (setDegree H)

/-- The maximum `t`-degree `M_t(F) = max_{|S|=t} d(S)`. -/
noncomputable def maxDegreeLevel (H : Finset (Finset α)) (t : ℕ) : ℕ :=
  (levelSets t).sup (setDegree H)

/-- The moment ratio `A_t(F) = Γ_t(F) / Λ_t(F)`. -/
noncomputable def averageDegreeLevel (H : Finset (Finset α)) (t : ℕ) : ℚ :=
  (gammaLevel H t : ℚ) / (lambdaLevel H t : ℚ)

/-- The propagated ratio `β_t(F) = ((t+1)Γ_{t+1}) / ((n-t)Γ_t)`. -/
noncomputable def betaLevel (H : Finset (Finset α)) (n t : ℕ) : ℚ :=
  ((((t + 1 : ℕ) : ℚ) * (gammaLevel H (t + 1) : ℚ))) /
    ((((n - t : ℕ) : ℚ) * (gammaLevel H t : ℚ)))

/-- The prefix product `∏_{i < t} β_i(F)`. -/
noncomputable def betaPrefix (H : Finset (Finset α)) (n t : ℕ) : ℚ :=
  Finset.prod (Finset.range t) (fun i => betaLevel H n i)

theorem gammaLevel_eq_sum_levelSets (H : Finset (Finset α)) (t : ℕ) :
    gammaLevel H t = Finset.sum (levelSets t) (fun B => setDegree H B ^ 2) := by
  rw [gammaLevel, levelSets, Finset.powersetCard_eq_filter]

@[simp] theorem setDegree_empty (H : Finset (Finset α)) :
    setDegree H ∅ = H.card := by
  simp [setDegree]

@[simp] theorem lambdaLevel_zero (H : Finset (Finset α)) :
    lambdaLevel H 0 = H.card := by
  simp [lambdaLevel, levelSets, setDegree]

@[simp] theorem gammaLevel_zero (H : Finset (Finset α)) :
    gammaLevel H 0 = H.card ^ 2 := by
  rw [gammaLevel_eq_sum_levelSets, levelSets, Finset.powersetCard_zero]
  simp [setDegree]

@[simp] theorem averageDegreeLevel_zero (H : Finset (Finset α)) :
    averageDegreeLevel H 0 = H.card := by
  by_cases hH : H.card = 0
  · simp [averageDegreeLevel, gammaLevel_zero, lambdaLevel_zero, hH]
  · have hHq : (H.card : ℚ) ≠ 0 := by exact_mod_cast hH
    rw [averageDegreeLevel, gammaLevel_zero, lambdaLevel_zero, Nat.cast_pow]
    field_simp [hHq]

@[simp] theorem betaPrefix_zero (H : Finset (Finset α)) (n : ℕ) :
    betaPrefix H n 0 = 1 := by
  simp [betaPrefix]

@[simp] theorem betaPrefix_succ (H : Finset (Finset α)) (n t : ℕ) :
    betaPrefix H n (t + 1) = betaPrefix H n t * betaLevel H n t := by
  simp [betaPrefix, Finset.prod_range_succ, mul_comm, mul_assoc]

theorem lambdaLevel_eq_sum_powersetCard (H : Finset (Finset α)) (t : ℕ) :
    lambdaLevel H t = Finset.sum H (fun e => (e.powersetCard t).card) := by
  unfold lambdaLevel setDegree levelSets
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [Finset.sum_boole]
  congr
  ext B
  constructor
  · intro h
    have hmem : B ∈ {x ∈ (Finset.univ : Finset α).powersetCard t | x ⊆ e} := h
    have hpow : B ∈ (Finset.univ : Finset α).powersetCard t := (Finset.mem_filter.mp hmem).1
    have hsub : B ⊆ e := (Finset.mem_filter.mp hmem).2
    exact Finset.mem_powersetCard.mpr ⟨hsub, (Finset.mem_powersetCard.mp hpow).2⟩
  · intro h
    have hpow : B ∈ powersetCard t e := h
    have hsub : B ⊆ e := (Finset.mem_powersetCard.mp hpow).1
    have hcard : B.card = t := (Finset.mem_powersetCard.mp hpow).2
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, hsub⟩

theorem lambdaLevel_eq_choose_mul_card
    (H : Finset (Finset α)) {n t : ℕ} (hH : IsRUniform H n) :
    lambdaLevel H t = Nat.choose n t * H.card := by
  rw [lambdaLevel_eq_sum_powersetCard]
  calc
    Finset.sum H (fun e => (e.powersetCard t).card) = Finset.sum H (fun _ => Nat.choose n t) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      simp [hH e he]
    _ = Nat.choose n t * H.card := by
      rw [Finset.card_eq_sum_ones]
      symm
      rw [Finset.mul_sum]
      simp

theorem lambdaLevel_pos
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    0 < lambdaLevel H t := by
  rw [lambdaLevel_eq_choose_mul_card H hH]
  exact Nat.mul_pos (Nat.choose_pos ht) (Finset.card_pos.mpr hne)

theorem gammaLevel_pos
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    0 < gammaLevel H t := by
  obtain ⟨e, he⟩ := hne
  have hsub : (e.powersetCard t).Nonempty := Finset.powersetCard_nonempty.2 (by simpa [hH e he] using ht)
  rcases hsub with ⟨B, hB⟩
  have hdeg : 0 < setDegree H B := by
    unfold setDegree
    apply Finset.card_pos.mpr
    refine ⟨e, ?_⟩
    simp [he, (Finset.mem_powersetCard.mp hB).1]
  have hsingle : setDegree H B ^ 2 ≤ gammaLevel H t := by
    have hmem : B ∈ levelSets t := (mem_levelSets).2 (Finset.mem_powersetCard.mp hB).2
    have hsum : setDegree H B ^ 2 ≤ Finset.sum (levelSets t) (fun C => setDegree H C ^ 2) :=
      Finset.single_le_sum (f := fun C : Finset α => setDegree H C ^ 2)
        (fun C hC => Nat.zero_le _) hmem
    simpa [gammaLevel_eq_sum_levelSets] using hsum
  exact lt_of_lt_of_le (by positivity) hsingle

theorem choose_cast_ratio
    {n t : ℕ} (ht : t < n) :
    ((Nat.choose n t : ℚ) * (((n - t : ℕ) : ℚ))) =
      (Nat.choose n (t + 1) : ℚ) * ((t + 1 : ℕ) : ℚ) := by
  exact_mod_cast (Nat.choose_succ_right_eq n t).symm

theorem lambdaLevel_succ
    (H : Finset (Finset α)) {n t : ℕ} (hH : IsRUniform H n) (ht : t < n) :
    (lambdaLevel H (t + 1) : ℚ) =
      ((((n - t : ℕ) : ℚ)) / (((t + 1 : ℕ) : ℚ))) * lambdaLevel H t := by
  have hchoose :
      (Nat.choose n t : ℚ) * (((n - t : ℕ) : ℚ)) =
      (Nat.choose n (t + 1) : ℚ) * (((t + 1 : ℕ) : ℚ)) :=
    choose_cast_ratio ht
  have ht1 : (0 : ℚ) < (((t + 1 : ℕ) : ℚ)) := by positivity
  rw [lambdaLevel_eq_choose_mul_card H hH, lambdaLevel_eq_choose_mul_card H hH]
  field_simp [ht1.ne']
  have hchooseCard := congrArg (fun x : ℚ => x * (H.card : ℚ)) hchoose
  simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hchooseCard.symm

theorem averageDegreeLevel_succ
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t < n) :
    averageDegreeLevel H (t + 1) = betaLevel H n t * averageDegreeLevel H t := by
  have hΓ : (0 : ℚ) < gammaLevel H t := by
    exact_mod_cast gammaLevel_pos H hH hne ht.le
  have hΛ : (0 : ℚ) < lambdaLevel H t := by
    exact_mod_cast lambdaLevel_pos H hH hne ht.le
  have ht1 : (0 : ℚ) < (((t + 1 : ℕ) : ℚ)) := by positivity
  have hnt : (0 : ℚ) < (((n - t : ℕ) : ℚ)) := by
    exact_mod_cast Nat.sub_pos_of_lt ht
  have hΛsucc : (lambdaLevel H (t + 1) : ℚ) =
      ((((n - t : ℕ) : ℚ)) / (((t + 1 : ℕ) : ℚ))) * lambdaLevel H t :=
    lambdaLevel_succ H hH ht
  unfold averageDegreeLevel betaLevel
  rw [hΛsucc]
  field_simp [hΓ.ne', hΛ.ne', ht1.ne', hnt.ne']

theorem averageDegreeLevel_eq_card_mul_betaPrefix
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    averageDegreeLevel H t = (H.card : ℚ) * betaPrefix H n t := by
  induction' t with t ih
  · simp
  · have ht' : t < n := by omega
    rw [averageDegreeLevel_succ H hH hne ht', ih (by omega), betaPrefix_succ]
    ring

theorem setDegree_le_maxDegreeLevel
    (H : Finset (Finset α)) {t : ℕ} {B : Finset α} (hB : B.card = t) :
    setDegree H B ≤ maxDegreeLevel H t := by
  have hmem : B ∈ levelSets t := by simp [levelSets, hB]
  exact Finset.le_sup hmem

theorem gammaLevel_le_max_mul_lambda (H : Finset (Finset α)) (t : ℕ) :
    gammaLevel H t ≤ maxDegreeLevel H t * lambdaLevel H t := by
  rw [gammaLevel_eq_sum_levelSets, lambdaLevel]
  calc
    Finset.sum (levelSets t) (fun B => setDegree H B ^ 2)
      ≤ Finset.sum (levelSets t) (fun B => maxDegreeLevel H t * setDegree H B) := by
          refine Finset.sum_le_sum ?_
          intro B hB
          have hdeg : setDegree H B ≤ maxDegreeLevel H t :=
            setDegree_le_maxDegreeLevel H ((mem_levelSets).1 hB)
          simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_right (setDegree H B) hdeg
    _ = maxDegreeLevel H t * Finset.sum (levelSets t) (setDegree H) := by
          rw [Finset.mul_sum]

theorem averageDegreeLevel_le_maxDegreeLevel (H : Finset (Finset α)) (t : ℕ) :
    averageDegreeLevel H t ≤ maxDegreeLevel H t := by
  by_cases hΛ : lambdaLevel H t = 0
  · have hΓ : gammaLevel H t = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hΛ] using gammaLevel_le_max_mul_lambda H t
    simp [averageDegreeLevel, hΛ, hΓ]
  · have hΛq : (0 : ℚ) < lambdaLevel H t := by
      exact_mod_cast Nat.pos_of_ne_zero hΛ
    apply (div_le_iff₀ hΛq).2
    have h := gammaLevel_le_max_mul_lambda H t
    exact_mod_cast h

/-- Exact heavy-set lemma: `M_t(F) ≥ A_t(F)`. -/
theorem heavy_set_average_bound (H : Finset (Finset α)) (t : ℕ) :
    averageDegreeLevel H t ≤ maxDegreeLevel H t :=
  averageDegreeLevel_le_maxDegreeLevel H t

/-- Exact heavy-set lemma in prefix-product form. -/
theorem heavy_set_betaPrefix_bound
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    (H.card : ℚ) * betaPrefix H n t ≤ maxDegreeLevel H t := by
  rw [← averageDegreeLevel_eq_card_mul_betaPrefix H hH hne ht]
  exact heavy_set_average_bound H t

/-- The link of `H` at `S`: the members of `H` containing `S`, with `S` deleted. -/
noncomputable def linkFamily (H : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  (H.filter fun e => S ⊆ e).image fun e => e \ S

@[simp] theorem mem_linkFamily {H : Finset (Finset α)} {S e : Finset α} :
    e ∈ linkFamily H S ↔ ∃ f ∈ H, S ⊆ f ∧ e = f \ S := by
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
    exact ⟨f, (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2, rfl⟩
  · rintro ⟨f, hfH, hSf, rfl⟩
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hfH, hSf⟩, rfl⟩

theorem linkFamily_card_eq_setDegree (H : Finset (Finset α)) (S : Finset α) :
    (linkFamily H S).card = setDegree H S := by
  unfold linkFamily setDegree
  classical
  calc
    (((H.filter fun e => S ⊆ e).image fun e => e \ S).card)
      = (H.filter fun e => S ⊆ e).card := by
          refine Finset.card_image_of_injOn ?_
          intro e he f hf hEq
          have hSe : S ⊆ e := (Finset.mem_filter.mp he).2
          have hSf : S ⊆ f := (Finset.mem_filter.mp hf).2
          calc
            e = S ∪ (e \ S) := by symm; exact Finset.union_sdiff_of_subset hSe
            _ = S ∪ (f \ S) := by simpa using congrArg (fun T => S ∪ T) hEq
            _ = f := Finset.union_sdiff_of_subset hSf
    _ = (H.filter fun e => S ⊆ e).card := rfl

theorem linkFamily_nonempty_of_setDegree_pos
    (H : Finset (Finset α)) {S : Finset α} (hdeg : 0 < setDegree H S) :
    (linkFamily H S).Nonempty := by
  rw [← linkFamily_card_eq_setDegree H S] at hdeg
  exact Finset.card_pos.mp hdeg

theorem linkFamily_uniform
    (H : Finset (Finset α)) {n : ℕ} (hH : IsRUniform H n) (S : Finset α) :
    IsRUniform (linkFamily H S) (n - S.card) := by
  intro e he
  rcases mem_linkFamily.mp he with ⟨f, hf, hSf, rfl⟩
  rw [Finset.card_sdiff_of_subset hSf, hH f hf]

theorem linkFamily_disjoint_right
    {H : Finset (Finset α)} {S e : Finset α} (he : e ∈ linkFamily H S) :
    Disjoint e S := by
  rcases mem_linkFamily.mp he with ⟨f, hf, hSf, rfl⟩
  rw [Finset.disjoint_left]
  intro x hx hxS
  exact (Finset.mem_sdiff.mp hx).2 hxS

theorem union_sdiff_cancel_left_of_disjoint {A S : Finset α} (hAS : Disjoint A S) :
    (S ∪ A) \ S = A := by
  ext x
  by_cases hxS : x ∈ S
  · have hxA : x ∉ A := by
      exact fun hxA => (Finset.disjoint_left.mp hAS hxA hxS)
    simp [hxS, hxA]
  · simp [hxS]

theorem linkFamily_sunflowerFree
    (H : Finset (Finset α)) {k : ℕ} (hH : SunflowerFree H k) (S : Finset α) :
    SunflowerFree (linkFamily H S) k := by
  intro A hA hInj hSun
  let A' : Fin k → Finset α := fun i => S ∪ A i
  have hA' : ∀ i, A' i ∈ H := by
    intro i
    rcases mem_linkFamily.mp (hA i) with ⟨e, heH, hSe, hAi⟩
    simpa [A', hAi, Finset.union_sdiff_of_subset hSe] using heH
  have hDisj : ∀ i, Disjoint (A i) S := fun i => linkFamily_disjoint_right (hA i)
  have hInj' : Function.Injective A' := by
    intro i j hij
    apply hInj
    have hEq := congrArg (fun T => T \ S) hij
    simpa [A', union_sdiff_cancel_left_of_disjoint (hDisj i),
      union_sdiff_cancel_left_of_disjoint (hDisj j)] using hEq
  have hSun' : IsSunflowerTuple A' := by
    intro i j i' j' hij hi'j'
    have hEq := hSun hij hi'j'
    ext x
    by_cases hxS : x ∈ S
    · simp [A', hxS]
    · simpa [A', hxS, Finset.mem_inter] using congrArg (fun T : Finset α => x ∈ T) hEq
  exact hH A' hA' hInj' hSun'

theorem levelSets_nonempty_of_uniform_nonempty
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    (levelSets (α := α) t).Nonempty := by
  obtain ⟨e, he⟩ := hne
  have hpow : (e.powersetCard t).Nonempty := by
    apply Finset.powersetCard_nonempty.2
    simpa [hH e he] using ht
  rcases hpow with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  exact (mem_levelSets (α := α)).2 (Finset.mem_powersetCard.mp hB).2

/-- There is an actual `t`-set attaining the heavy-set lower bound. -/
theorem exists_heavy_set_betaPrefix
    (H : Finset (Finset α)) {n t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (ht : t ≤ n) :
    ∃ B ∈ levelSets t, (H.card : ℚ) * betaPrefix H n t ≤ setDegree H B := by
  have hlevel : (levelSets (α := α) t).Nonempty :=
    levelSets_nonempty_of_uniform_nonempty H hH hne ht
  rcases Finset.exists_mem_eq_sup (s := levelSets t) hlevel (f := setDegree H) with
    ⟨B, hB, hmax⟩
  refine ⟨B, hB, ?_⟩
  simpa [maxDegreeLevel, hmax] using heavy_set_betaPrefix_bound H hH hne ht

/-- The heavy-set lemma applied inside a link. -/
theorem heavy_link_betaPrefix_bound
    (H : Finset (Finset α)) {n r : ℕ} (S : Finset α)
    (hH : IsRUniform H n) (hdeg : 0 < setDegree H S) (hr : r ≤ n - S.card) :
    (setDegree H S : ℚ) * betaPrefix (linkFamily H S) (n - S.card) r ≤
      maxDegreeLevel (linkFamily H S) r := by
  have hne : (linkFamily H S).Nonempty := linkFamily_nonempty_of_setDegree_pos H hdeg
  have hlink : IsRUniform (linkFamily H S) (n - S.card) := linkFamily_uniform H hH S
  simpa [linkFamily_card_eq_setDegree] using
    heavy_set_betaPrefix_bound (H := linkFamily H S) (n := n - S.card) (t := r) hlink hne hr

/-- A concrete heavy set also exists inside every nonempty link. -/
theorem exists_heavy_set_in_link
    (H : Finset (Finset α)) {n r : ℕ} (S : Finset α)
    (hH : IsRUniform H n) (hdeg : 0 < setDegree H S) (hr : r ≤ n - S.card) :
    ∃ T ∈ levelSets r,
      (setDegree H S : ℚ) * betaPrefix (linkFamily H S) (n - S.card) r ≤
        setDegree (linkFamily H S) T := by
  have hne : (linkFamily H S).Nonempty := linkFamily_nonempty_of_setDegree_pos H hdeg
  have hlink : IsRUniform (linkFamily H S) (n - S.card) := linkFamily_uniform H hH S
  simpa [linkFamily_card_eq_setDegree] using
    exists_heavy_set_betaPrefix (H := linkFamily H S) (n := n - S.card) (t := r) hlink hne hr

/-- An abstract sunflower-size bound: every `k`-sunflower-free `n`-uniform family
has size at most `g n k`. -/
def IsSunflowerSizeBound (α : Type*) [DecidableEq α] [Fintype α] (g : ℕ → ℕ → ℕ) : Prop :=
  ∀ (G : Finset (Finset α)) {n k : ℕ},
    IsRUniform G n → SunflowerFree G k → G.card ≤ g n k

theorem maxDegreeLevel_le_sunflowerBound
    {g : ℕ → ℕ → ℕ} (hg : IsSunflowerSizeBound α g)
    (H : Finset (Finset α)) {n k t : ℕ}
    (hH : IsRUniform H n) (hfree : SunflowerFree H k) (ht : t ≤ n) :
    maxDegreeLevel H t ≤ g (n - t) k := by
  refine Finset.sup_le ?_
  intro B hB
  have hBt : B.card = t := (mem_levelSets.mp hB)
  let G : Finset (Finset α) := linkFamily H B
  have hlink : IsRUniform G (n - t) := by
    simpa [hBt] using linkFamily_uniform H hH B
  have hfreeLink : SunflowerFree G k := by
    simpa [G] using linkFamily_sunflowerFree H hfree B
  have hcap : G.card ≤ g (n - t) k := hg G (n := n - t) (k := k) hlink hfreeLink
  simpa [G, linkFamily_card_eq_setDegree, hBt] using hcap

/-- Heavy-set recursion against any abstract sunflower-size upper bound. -/
theorem heavy_set_betaPrefix_le_sunflowerBound
    {g : ℕ → ℕ → ℕ} (hg : IsSunflowerSizeBound α g)
    (H : Finset (Finset α)) {n k t : ℕ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (hfree : SunflowerFree H k) (ht : t ≤ n) :
    (H.card : ℚ) * betaPrefix H n t ≤ (g (n - t) k : ℚ) := by
  exact le_trans (heavy_set_betaPrefix_bound H hH hne ht)
    (by exact_mod_cast maxDegreeLevel_le_sunflowerBound hg H hH hfree ht)

/-- If `b` is a lower bound for the prefix product, then the family size is bounded
by the recursive quotient `g(n - t, k) / b`. -/
theorem sunflower_size_le_div_of_betaPrefix_lower
    {g : ℕ → ℕ → ℕ} (hg : IsSunflowerSizeBound α g)
    (H : Finset (Finset α)) {n k t : ℕ} {b : ℚ}
    (hH : IsRUniform H n) (hne : H.Nonempty) (hfree : SunflowerFree H k) (ht : t ≤ n)
    (hb : 0 < b) (hβ : b ≤ betaPrefix H n t) :
    (H.card : ℚ) ≤ (g (n - t) k : ℚ) / b := by
  have hmain :
      (H.card : ℚ) * betaPrefix H n t ≤ (g (n - t) k : ℚ) :=
    heavy_set_betaPrefix_le_sunflowerBound hg H hH hne hfree ht
  have hmul :
      (H.card : ℚ) * b ≤ (H.card : ℚ) * betaPrefix H n t := by
    exact mul_le_mul_of_nonneg_left hβ (by positivity)
  exact (le_div_iff₀ hb).2 (le_trans hmul hmain)

end FormalConjectures.Problems.Erdos.E20
