import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.Correlation

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Local Branching Counterexample

This file formalizes the complete-graph dual counterexample to the proposed
local branching lower bound

`Σ_x d_H(x)^2 ≥ c_k * r * |H|^2`

for `r`-uniform `k`-sunflower-free families.

The counterexample family is the collection of stars in the complete graph `K_m`,
viewed on the ground set of graph edges. Its members have size `m - 1`, any three
distinct members fail to form a sunflower, and

`Σ_x d_H(x)^2 = 2m(m - 1)` while `r * |H|^2 = (m - 1)m^2`.

Hence the normalized ratio is `2 / m`, so no positive constant can work.
-/

variable {α : Type*} [DecidableEq α]

/-- A `k`-tuple of sets is a sunflower if all pairwise intersections agree. -/
def IsSunflowerTuple {k : ℕ} (A : Fin k → Finset α) : Prop :=
  ∀ ⦃i j i' j' : Fin k⦄, i ≠ j → i' ≠ j' → A i ∩ A j = A i' ∩ A j'

/-- A family is `k`-sunflower-free if no injective `k`-tuple drawn from it is a sunflower. -/
def SunflowerFree (H : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ A : Fin k → Finset α, (∀ i, A i ∈ H) → Function.Injective A → ¬ IsSunflowerTuple A

section SunflowerFree

variable {H : Finset (Finset α)}

/-- `3`-sunflower-free already implies `k`-sunflower-free for every `k ≥ 3`. -/
theorem SunflowerFree.of_three (hH : SunflowerFree H 3) {k : ℕ} (hk : 3 ≤ k) :
    SunflowerFree H k := by
  intro A hA hInj hSun
  let emb : Fin 3 → Fin k := fun i => ⟨i.1, by omega⟩
  have hEmbInj : Function.Injective emb := by
    intro i j hij
    apply Fin.ext
    simpa [emb] using congrArg Fin.val hij
  have hA' : ∀ i, A (emb i) ∈ H := fun i => hA (emb i)
  have hInj' : Function.Injective (fun i => A (emb i)) := by
    intro i j hij
    exact hEmbInj (hInj hij)
  have hSun' : IsSunflowerTuple (fun i => A (emb i)) := by
    intro i j i' j' hij hi'j'
    exact hSun (hEmbInj.ne hij) (hEmbInj.ne hi'j')
  exact hH (fun i => A (emb i)) hA' hInj' hSun'

end SunflowerFree

section CompleteGraphDual

open scoped BigOperators

/-- The ground elements are unordered pairs of vertices. -/
def pairEdge {m : ℕ} (i j : Fin m) : Finset (Fin m) :=
  {i, j}

/-- The star at vertex `i` in `K_m`, viewed as a hyperedge on the ground set of graph edges. -/
def completeGraphStar (m : ℕ) (i : Fin m) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).erase i).image (pairEdge i)

/-- The dual family of the complete graph: one hyperedge for each vertex-star. -/
def completeGraphDualFamily (m : ℕ) : Finset (Finset (Finset (Fin m))) :=
  (Finset.univ : Finset (Fin m)).image (completeGraphStar m)

/-- The squared-degree sum `S(H) = Σ_x d_H(x)^2`. -/
noncomputable def degreeSquareSum {β : Type*} [DecidableEq β] [Fintype β]
    (H : Finset (Finset β)) : ℕ :=
  ∑ x : β, vertexDegree' H x ^ 2

@[simp] theorem degreeSquareSum_eq_intersection_sum {β : Type*} [DecidableEq β] [Fintype β]
    (H : Finset (Finset β)) :
    degreeSquareSum H = ∑ A ∈ H, ∑ B ∈ H, (A ∩ B).card := by
  simpa [degreeSquareSum] using degree_sq_sum_eq_intersection_sum' H

@[simp] lemma mem_pairEdge {m : ℕ} {i j x : Fin m} :
    x ∈ pairEdge i j ↔ x = i ∨ x = j := by
  simp [pairEdge, eq_comm]

@[simp] lemma card_pairEdge {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (pairEdge i j).card = 2 := by
  simp [pairEdge, hij]

lemma mem_completeGraphStar_iff {m : ℕ} {i : Fin m} {e : Finset (Fin m)} :
    e ∈ completeGraphStar m i ↔ e.card = 2 ∧ i ∈ e := by
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    constructor
    · simpa [pairEdge, hji] using card_pairEdge (show i ≠ j from hji.symm)
    · simp [pairEdge]
  · rintro ⟨hcard, hi⟩
    rcases Finset.card_eq_two.mp hcard with ⟨x, y, hxy, rfl⟩
    have hi' : i = x ∨ i = y := by
      simpa [pairEdge, eq_comm] using hi
    apply Finset.mem_image.mpr
    rcases hi' with rfl | rfl
    · exact ⟨y, by simpa using hxy.symm, by ext z <;> simp [pairEdge, eq_comm, or_comm]⟩
    · exact ⟨x, by simpa using hxy, by ext z <;> simp [pairEdge, eq_comm, or_comm]⟩

lemma pairEdge_mem_completeGraphStar_iff {m : ℕ} {i j l : Fin m} (hij : i ≠ j) :
    pairEdge i j ∈ completeGraphStar m l ↔ l = i ∨ l = j := by
  simpa [mem_completeGraphStar_iff, pairEdge, hij, eq_comm]

lemma card_completeGraphStar {m : ℕ} (i : Fin m) :
    (completeGraphStar m i).card = m - 1 := by
  unfold completeGraphStar
  rw [Finset.card_image_of_injOn]
  · simp
  · intro j hj l hl hEq
    have hji : j ≠ i := Finset.ne_of_mem_erase (Finset.mem_coe.mp hj)
    have hjmem : j ∈ pairEdge i j := by simp [pairEdge]
    have : j ∈ pairEdge i l := by simpa [hEq] using hjmem
    simpa [pairEdge, hji, eq_comm] using this

lemma exists_third_vertex {m : ℕ} (hm : 3 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ∃ l : Fin m, l ≠ i ∧ l ≠ j := by
  have hsubset : ({i, j} : Finset (Fin m)) ⊆ (Finset.univ : Finset (Fin m)) := by
    simp
  have hne : ({i, j} : Finset (Fin m)) ≠ (Finset.univ : Finset (Fin m)) := by
    intro hEq
    have : 2 = m := by
      calc
        2 = ({i, j} : Finset (Fin m)).card := by simp [hij]
        _ = (Finset.univ : Finset (Fin m)).card := by simpa [hEq]
        _ = m := by simp
    omega
  have hnot : ¬ (Finset.univ : Finset (Fin m)) ⊆ ({i, j} : Finset (Fin m)) := by
    intro hrev
    exact hne (Finset.Subset.antisymm hsubset hrev)
  have hssub : ({i, j} : Finset (Fin m)) ⊂ (Finset.univ : Finset (Fin m)) :=
    ⟨hsubset, hnot⟩
  rcases Finset.exists_of_ssubset hssub with ⟨l, -, hl⟩
  have hl' : l ≠ i ∧ l ≠ j := by simpa [pairEdge, eq_comm] using hl
  exact ⟨l, hl'.1, hl'.2⟩

lemma completeGraphStar_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (completeGraphStar m) := by
  intro i j hEq
  by_contra hij
  obtain ⟨l, hli, hlj⟩ := exists_third_vertex hm i j hij
  have hlmem : pairEdge i l ∈ completeGraphStar m i := by
    exact (pairEdge_mem_completeGraphStar_iff hli.symm).2 (Or.inl rfl)
  have : pairEdge i l ∈ completeGraphStar m j := by simpa [hEq] using hlmem
  have hj' := (pairEdge_mem_completeGraphStar_iff hli.symm).1 this
  cases hj' with
  | inl hji => exact hij hji.symm
  | inr hjl => exact hlj hjl.symm

lemma card_completeGraphDualFamily {m : ℕ} (hm : 3 ≤ m) :
    (completeGraphDualFamily m).card = m := by
  unfold completeGraphDualFamily
  rw [Finset.card_image_of_injective]
  · simp
  · exact completeGraphStar_injective hm

/-- The complete-graph dual family is `(m - 1)`-uniform. -/
theorem completeGraphDualFamily_uniform {m : ℕ} :
    IsRUniform (completeGraphDualFamily m) (m - 1) := by
  intro F hF
  rcases Finset.mem_image.mp hF with ⟨i, -, rfl⟩
  exact card_completeGraphStar i

lemma star_inter_eq_singleton {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    completeGraphStar m i ∩ completeGraphStar m j = {pairEdge i j} := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_inter.mp he with ⟨hi, hj⟩
    have hi' := (mem_completeGraphStar_iff (i := i) (e := e)).1 hi
    have hj' := (mem_completeGraphStar_iff (i := j) (e := e)).1 hj
    have hsubset : pairEdge i j ⊆ e := by
      intro x hx
      rcases (mem_pairEdge).1 hx with rfl | rfl
      · exact hi'.2
      · exact hj'.2
    have hEq : pairEdge i j = e := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [card_pairEdge hij, hi'.1]
    simp [hEq]
  · intro he
    simp only [Finset.mem_singleton] at he
    subst he
    exact Finset.mem_inter.mpr
      ⟨(pairEdge_mem_completeGraphStar_iff hij).2 (Or.inl rfl),
        (pairEdge_mem_completeGraphStar_iff hij).2 (Or.inr rfl)⟩

lemma star_inter_card {m : ℕ} (i j : Fin m) :
    ((completeGraphStar m i) ∩ (completeGraphStar m j)).card =
      if i = j then m - 1 else 1 := by
  by_cases hij : i = j
  · subst hij
    simp [card_completeGraphStar]
  · rw [if_neg hij, star_inter_eq_singleton hij]
    simp

/-- Any three distinct stars in the complete-graph dual family fail to form a sunflower. -/
theorem completeGraphDualFamily_three_sunflowerFree {m : ℕ} (hm : 3 ≤ m) :
    SunflowerFree (completeGraphDualFamily m) 3 := by
  intro A hA hInj hSun
  rcases Finset.mem_image.mp (hA 0) with ⟨i, -, h0⟩
  rcases Finset.mem_image.mp (hA 1) with ⟨j, -, h1⟩
  rcases Finset.mem_image.mp (hA 2) with ⟨l, -, h2⟩
  have h01 : A 0 ≠ A 1 := by
    exact fun h => Fin.zero_ne_one (hInj h)
  have h02 : A 0 ≠ A 2 := by
    have hneq : (0 : Fin 3) ≠ 2 := by decide
    exact fun h => hneq (hInj h)
  have h12 : A 1 ≠ A 2 := by
    have hneq : (1 : Fin 3) ≠ 2 := by decide
    exact fun h => hneq (hInj h)
  have hij : i ≠ j := by
    intro h
    have : completeGraphStar m i = completeGraphStar m j := by simpa [h]
    exact h01 <| by simpa [h0, h1] using this
  have hil : i ≠ l := by
    intro h
    have : completeGraphStar m i = completeGraphStar m l := by simpa [h]
    exact h02 <| by simpa [h0, h2] using this
  have hjl : j ≠ l := by
    intro h
    have : completeGraphStar m j = completeGraphStar m l := by simpa [h]
    exact h12 <| by simpa [h1, h2] using this
  let e : Finset (Fin m) := pairEdge i j
  have he01 : e ∈ A 0 ∩ A 1 := by
    subst e
    rw [← h0, ← h1]
    exact Finset.mem_inter.mpr
      ⟨(pairEdge_mem_completeGraphStar_iff hij).2 (Or.inl rfl),
        (pairEdge_mem_completeGraphStar_iff hij).2 (Or.inr rfl)⟩
  have he02_not : e ∉ A 0 ∩ A 2 := by
    intro he
    have hel : e ∈ completeGraphStar m l := by
      simpa [h2] using (Finset.mem_inter.mp he).2
    have h' := (pairEdge_mem_completeGraphStar_iff hij).1 hel
    cases h' with
    | inl hli => exact hil hli.symm
    | inr hlj => exact hjl hlj.symm
  have hEq : A 0 ∩ A 1 = A 0 ∩ A 2 := by
    exact hSun (i := 0) (j := 1) (i' := 0) (j' := 2) (by decide) (by decide)
  exact he02_not <| by simpa [hEq] using he01

/-- Hence the family is `k`-sunflower-free for every `k ≥ 3`. -/
theorem completeGraphDualFamily_sunflowerFree {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k) :
    SunflowerFree (completeGraphDualFamily m) k :=
  (completeGraphDualFamily_three_sunflowerFree hm).of_three hk

/-- Exact evaluation of the total overlap / squared-degree sum for the complete-graph dual family. -/
theorem degreeSquareSum_completeGraphDualFamily {m : ℕ} (hm : 3 ≤ m) :
    degreeSquareSum (completeGraphDualFamily m) = 2 * m * (m - 1) := by
  have hInj : Function.Injective (completeGraphStar m) := completeGraphStar_injective hm
  rw [degreeSquareSum_eq_intersection_sum]
  unfold completeGraphDualFamily
  simp [Finset.sum_image, hInj.injOn]
  calc
    ∑ i : Fin m, ∑ j : Fin m,
        ((completeGraphStar m i) ∩ (completeGraphStar m j)).card
      = ∑ i : Fin m, ((m - 1) + ((Finset.univ : Finset (Fin m)).erase i).sum (fun _ => 1)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hsplit :
              ((Finset.univ : Finset (Fin m)).sum fun j =>
                ((completeGraphStar m i) ∩ (completeGraphStar m j)).card)
                =
                  ((completeGraphStar m i) ∩ (completeGraphStar m i)).card +
                    (((Finset.univ : Finset (Fin m)).erase i).sum fun x =>
                      ((completeGraphStar m i) ∩ (completeGraphStar m x)).card) := by
            have h := (Finset.add_sum_erase
                (Finset.univ : Finset (Fin m))
                (fun j => ((completeGraphStar m i) ∩ (completeGraphStar m j)).card)
                (Finset.mem_univ i)).symm
            simp only [Finset.inter_self] at h ⊢
            exact h
          have hsumErase :
              (((Finset.univ : Finset (Fin m)).erase i).sum fun x =>
                if i = x then m - 1 else 1)
                =
                  (((Finset.univ : Finset (Fin m)).erase i).sum fun _ => 1) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxi : x ≠ i := Finset.ne_of_mem_erase hx
            simp [hxi.symm]
          simpa [Finset.sdiff_singleton_eq_erase, star_inter_card, card_completeGraphStar, hsumErase]
            using hsplit
    _ = ∑ _ : Fin m, 2 * (m - 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp
          ring
    _ = m * (2 * (m - 1)) := by simp
    _ = 2 * m * (m - 1) := by ring

/-- The normalized ratio is exactly `2 / m`. -/
theorem normalized_degreeSquareRatio_completeGraphDualFamily {m : ℕ} (hm : 3 ≤ m) :
    ((degreeSquareSum (completeGraphDualFamily m) : ℝ) /
        ((((m - 1 : ℕ) : ℝ) * (completeGraphDualFamily m).card ^ 2))) =
      2 / m := by
  have hcard := card_completeGraphDualFamily hm
  have hsum := degreeSquareSum_completeGraphDualFamily hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hm1_nat : 0 < m - 1 := by omega
  have hm1 : (0 : ℝ) < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hm1_nat
  rw [hcard, hsum]
  field_simp [hm0.ne', hm1.ne']
  norm_num [Nat.cast_mul]
  ring_nf

/-- No positive constant lower bound of the form `c * r * |H|^2 ≤ S(H)` can hold. -/
theorem no_positive_local_branching_constant (k : ℕ) (hk : 3 ≤ k) :
    ∀ c : ℝ, 0 < c →
      ∃ m ≥ 3,
        let H := completeGraphDualFamily m
        SunflowerFree H k ∧
        IsRUniform H (m - 1) ∧
        ((degreeSquareSum H : ℝ) < c * (((m - 1 : ℕ) : ℝ)) * H.card ^ 2) := by
  intro c hc
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / c)
  let m := max 3 n
  have hm : 3 ≤ m := le_max_left _ _
  have hm_gt : 2 / c < (m : ℝ) := by
    exact lt_of_lt_of_le hn (by exact_mod_cast le_max_right 3 n)
  have hcm : 2 < c * (m : ℝ) := by
    have hcm' : 2 < (m : ℝ) * c := by
      exact (_root_.div_lt_iff₀ hc).mp hm_gt
    simpa [mul_comm] using hcm'
  have hm0 : (0 : ℝ) < m := by positivity
  have hm1_nat : 0 < m - 1 := by omega
  have hm1 : (0 : ℝ) < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hm1_nat
  refine ⟨m, hm, ?_⟩
  dsimp
  refine ⟨completeGraphDualFamily_sunflowerFree hm hk, completeGraphDualFamily_uniform, ?_⟩
  have hstep1 : 2 * (((m - 1 : ℕ) : ℝ)) < c * (m : ℝ) * (((m - 1 : ℕ) : ℝ)) := by
    exact mul_lt_mul_of_pos_right hcm hm1
  have hstep2 :
      2 * (m : ℝ) * (((m - 1 : ℕ) : ℝ)) <
        (c * (m : ℝ) * (((m - 1 : ℕ) : ℝ))) * m := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_lt_mul_of_pos_right hstep1 hm0
  rw [degreeSquareSum_completeGraphDualFamily hm, card_completeGraphDualFamily hm]
  have hfinal : ((2 * m * (m - 1) : ℕ) : ℝ) < c * (((m - 1 : ℕ) : ℝ)) * (m : ℝ) ^ 2 := by
    calc
      ((2 * m * (m - 1) : ℕ) : ℝ) = 2 * (m : ℝ) * (((m - 1 : ℕ) : ℝ)) := by
        norm_num [Nat.cast_mul]
      _ < (c * (m : ℝ) * (((m - 1 : ℕ) : ℝ))) * m := hstep2
      _ = c * (((m - 1 : ℕ) : ℝ)) * (m : ℝ) ^ 2 := by ring
  exact hfinal

end CompleteGraphDual

end FormalConjectures.Problems.Erdos.E20
