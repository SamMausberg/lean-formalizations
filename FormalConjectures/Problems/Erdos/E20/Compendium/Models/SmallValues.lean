import FormalConjectures.Problems.Erdos.E20.Compendium.Models.CodeModels

open Finset

namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-!
# Small Fixed- Alphabet Values

This file records small concrete code-model certificates from
`sunflower_selected_results.tex`, including the Hall-theoretic proof of
`F_{5,5}(2) = 16`.
-/

/-- The inclusion `Fin 4 ↪ Fin 5`. -/
def fin4ToFin5 (a : Fin 4) : Fin 5 :=
  ⟨a.1, by omega⟩

/-- The `4 × 4` grid inside `[5]^2`. -/
def fourByFourGridInFive : Finset (Fin 2 → Fin 5) :=
  (Finset.univ : Finset (Fin 2 → Fin 4)).image fun x => fun i => fin4ToFin5 (x i)

/-- The point `(r,c)` in `[5]^2`. -/
def codeWord2 (r c : Fin 5) : Fin 2 → Fin 5 := ![r, c]

/-- Points of a code in row `r`. -/
def rowSet (C : Finset (Fin 2 → Fin 5)) (r : Fin 5) : Finset (Fin 2 → Fin 5) :=
  C.filter fun x => x 0 = r

/-- Points of a code in column `c`. -/
def colSet (C : Finset (Fin 2 → Fin 5)) (c : Fin 5) : Finset (Fin 2 → Fin 5) :=
  C.filter fun x => x 1 = c

/-- The full row `r` in `[5]^2`. -/
def fullRow (r : Fin 5) : Finset (Fin 2 → Fin 5) :=
  (Finset.univ : Finset (Fin 5)).image fun c => codeWord2 r c

/-- The full column `c` in `[5]^2`. -/
def fullCol (c : Fin 5) : Finset (Fin 2 → Fin 5) :=
  (Finset.univ : Finset (Fin 5)).image fun r => codeWord2 r c

/-- Neighbor columns of a row in the bipartite graph associated to a code. -/
def rowNeighbors (C : Finset (Fin 2 → Fin 5)) (r : Fin 5) : Finset (Fin 5) :=
  (rowSet C r).image fun x => x 1

@[simp] theorem codeWord2_zero (r c : Fin 5) : codeWord2 r c 0 = r := by
  rfl

@[simp] theorem codeWord2_one (r c : Fin 5) : codeWord2 r c 1 = c := by
  rfl

theorem codeWord2_injective_left (r : Fin 5) :
    Function.Injective fun c : Fin 5 => codeWord2 r c := by
  intro a b h
  simpa [codeWord2] using congrArg (fun x : Fin 2 → Fin 5 => x 1) h

theorem codeWord2_injective_right (c : Fin 5) :
    Function.Injective fun r : Fin 5 => codeWord2 r c := by
  intro a b h
  simpa [codeWord2] using congrArg (fun x : Fin 2 → Fin 5 => x 0) h

theorem mem_fullRow_iff {r : Fin 5} {x : Fin 2 → Fin 5} :
    x ∈ fullRow r ↔ x 0 = r := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨c, _hc, rfl⟩
    simp [codeWord2]
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨x 1, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i <;> simp [codeWord2, hx]

theorem mem_fullCol_iff {c : Fin 5} {x : Fin 2 → Fin 5} :
    x ∈ fullCol c ↔ x 1 = c := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨r, _hr, rfl⟩
    simp [codeWord2]
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨x 0, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i <;> simp [codeWord2, hx]

@[simp] theorem card_fullRow (r : Fin 5) : (fullRow r).card = 5 := by
  unfold fullRow
  rw [Finset.card_image_of_injective]
  · simp
  · exact codeWord2_injective_left r

@[simp] theorem card_fullCol (c : Fin 5) : (fullCol c).card = 5 := by
  unfold fullCol
  rw [Finset.card_image_of_injective]
  · simp
  · exact codeWord2_injective_right c

theorem mem_rowNeighbors_iff {C : Finset (Fin 2 → Fin 5)} {r c : Fin 5} :
    c ∈ rowNeighbors C r ↔ codeWord2 r c ∈ C := by
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨x, hx, hxc⟩
    have hxC : x ∈ C := (Finset.mem_filter.mp hx).1
    have hxr : x 0 = r := (Finset.mem_filter.mp hx).2
    have hxc' : x 1 = c := by simpa using hxc
    have hxword : x = codeWord2 r c := by
      funext i
      fin_cases i <;> simp [codeWord2, hxr, hxc']
    simpa [hxword] using hxC
  · intro hc
    refine Finset.mem_image.mpr ?_
    refine ⟨codeWord2 r c, Finset.mem_filter.mpr ⟨hc, by simp [codeWord2]⟩, by simp [codeWord2]⟩

theorem fourByFourGridInFive_card :
    fourByFourGridInFive.card = 16 := by
  unfold fourByFourGridInFive
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    funext i
    have h := congrArg (fun f : Fin 2 → Fin 5 => f i) hxy
    apply Fin.ext
    simpa [fin4ToFin5] using congrArg Fin.val h

theorem mem_fourByFourGridInFive_iff {x : Fin 2 → Fin 5} :
    x ∈ fourByFourGridInFive ↔ ∀ i : Fin 2, (x i).1 < 4 := by
  constructor
  · intro hx i
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    simp [fin4ToFin5]
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨fun i => ⟨(x i).1, hx i⟩, by simp, ?_⟩
    funext i
    apply Fin.ext
    simp [fin4ToFin5]

theorem fourByFourGridInFive_codeModelFree :
    CodeModelFree 5 5 2 fourByFourGridInFive := by
  intro f hfInj hfMem
  have hlt : ∀ t : Fin 5, ∀ j : Fin 2, (f t j).1 < 4 := by
    intro t j
    exact (mem_fourByFourGridInFive_iff.mp (hfMem t)) j
  have hcoord_not_inj :
      ∀ j : Fin 2, ¬ Function.Injective fun t : Fin 5 => f t j := by
    intro j hj
    let g : Fin 5 → Fin 4 := fun t => ⟨(f t j).1, hlt t j⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply hj
      apply Fin.ext
      simpa [g] using congrArg Fin.val hab
    have hcard := Fintype.card_le_of_injective g hg
    norm_num [g] at hcard
  by_contra hno
  have hall : ∀ j : Fin 2, ∀ a b : Fin 5, f a j = f b j := by
    intro j
    by_contra hnot
    exact hno ⟨j, hnot, hcoord_not_inj j⟩
  have h01 : f 0 = f 1 := by
    funext j
    exact hall j 0 1
  have hfin : (0 : Fin 5) = 1 := hfInj h01
  norm_num at hfin

theorem not_fullRow_subset_of_codeModelFree
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) (r : Fin 5) :
    ¬ fullRow r ⊆ C := by
  intro hsub
  let f : Fin 5 → Fin 2 → Fin 5 := fun c => codeWord2 r c
  have hfInj : Function.Injective f := codeWord2_injective_left r
  have hfMem : ∀ c, f c ∈ C := by
    intro c
    exact hsub (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)
  rcases hfree f hfInj hfMem with ⟨j, hnotConst, hnotInj⟩
  fin_cases j
  · exact hnotConst (by intro a b; simp [f, codeWord2])
  · exact hnotInj (by
      intro a b h
      simpa [f, codeWord2] using h)

theorem not_fullCol_subset_of_codeModelFree
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) (c : Fin 5) :
    ¬ fullCol c ⊆ C := by
  intro hsub
  let f : Fin 5 → Fin 2 → Fin 5 := fun r => codeWord2 r c
  have hfInj : Function.Injective f := codeWord2_injective_right c
  have hfMem : ∀ r, f r ∈ C := by
    intro r
    exact hsub (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  rcases hfree f hfInj hfMem with ⟨j, hnotConst, hnotInj⟩
  fin_cases j
  · exact hnotInj (by
      intro a b h
      simpa [f, codeWord2] using h)
  · exact hnotConst (by intro a b; simp [f, codeWord2])

theorem rowSet_card_le_four_of_codeModelFree
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) (r : Fin 5) :
    (rowSet C r).card ≤ 4 := by
  by_contra hle
  have hfive : 5 ≤ (rowSet C r).card := by omega
  have hsubset : rowSet C r ⊆ fullRow r := by
    intro x hx
    exact mem_fullRow_iff.mpr (Finset.mem_filter.mp hx).2
  have heq : rowSet C r = fullRow r := by
    exact Finset.eq_of_subset_of_card_le hsubset (by simpa using hfive)
  exact not_fullRow_subset_of_codeModelFree hfree r (by
    intro x hx
    have hxrow : x ∈ rowSet C r := by simpa [heq] using hx
    exact (Finset.mem_filter.mp hxrow).1)

theorem colSet_card_le_four_of_codeModelFree
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) (c : Fin 5) :
    (colSet C c).card ≤ 4 := by
  by_contra hle
  have hfive : 5 ≤ (colSet C c).card := by omega
  have hsubset : colSet C c ⊆ fullCol c := by
    intro x hx
    exact mem_fullCol_iff.mpr (Finset.mem_filter.mp hx).2
  have heq : colSet C c = fullCol c := by
    exact Finset.eq_of_subset_of_card_le hsubset (by simpa using hfive)
  exact not_fullCol_subset_of_codeModelFree hfree c (by
    intro x hx
    have hxcol : x ∈ colSet C c := by simpa [heq] using hx
    exact (Finset.mem_filter.mp hxcol).1)

theorem no_perfectMatching_of_codeModelFree
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) :
    ¬ ∃ p : Fin 5 → Fin 5, Function.Injective p ∧ ∀ r, codeWord2 r (p r) ∈ C := by
  rintro ⟨p, hpInj, hpMem⟩
  let f : Fin 5 → Fin 2 → Fin 5 := fun r => codeWord2 r (p r)
  have hfInj : Function.Injective f := by
    intro a b h
    simpa [f, codeWord2] using congrArg (fun x : Fin 2 → Fin 5 => x 0) h
  rcases hfree f hfInj hpMem with ⟨j, hnotConst, hnotInj⟩
  fin_cases j
  · exact hnotInj (by
      intro a b h
      simpa [f, codeWord2] using h)
  · exact hnotInj (by
      intro a b h
      exact hpInj (by
        simpa [f, codeWord2] using h))

theorem no_neighborSDR_of_codeModelFree
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) :
    ¬ ∃ p : Fin 5 → Fin 5, Function.Injective p ∧ ∀ r, p r ∈ rowNeighbors C r := by
  rintro ⟨p, hpInj, hpMem⟩
  exact no_perfectMatching_of_codeModelFree hfree
    ⟨p, hpInj, fun r => mem_rowNeighbors_iff.mp (hpMem r)⟩

theorem card_rows_in_set_le
    (C : Finset (Fin 2 → Fin 5)) (S : Finset (Fin 5)) :
    (C.filter fun x => x 0 ∈ S).card ≤
      S.card * (S.biUnion fun r => rowNeighbors C r).card := by
  classical
  let φ : ↥(C.filter fun x => x 0 ∈ S) →
      S × (S.biUnion fun r => rowNeighbors C r) := fun x =>
    ⟨⟨x.1 0, (Finset.mem_filter.mp x.2).2⟩,
      ⟨x.1 1, by
        exact Finset.mem_biUnion.mpr
          ⟨x.1 0, (Finset.mem_filter.mp x.2).2,
            Finset.mem_image.mpr
              ⟨x.1, Finset.mem_filter.mpr
                ⟨(Finset.mem_filter.mp x.2).1, rfl⟩, rfl⟩⟩⟩⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg
        (fun p : S × (S.biUnion fun r => rowNeighbors C r) => (p.1 : Fin 5)) hxy
    · exact congrArg
        (fun p : S × (S.biUnion fun r => rowNeighbors C r) => (p.2 : Fin 5)) hxy
  have hcard := Fintype.card_le_of_injective φ hφ
  rw [← Fintype.card_coe (C.filter fun x => x 0 ∈ S),
    ← Fintype.card_coe S,
    ← Fintype.card_coe (S.biUnion fun r => rowNeighbors C r)]
  simpa [Fintype.card_prod] using hcard

theorem card_rows_outside_set_le
    {C : Finset (Fin 2 → Fin 5)} (hrow : ∀ r, (rowSet C r).card ≤ 4)
    (S : Finset (Fin 5)) :
    (C.filter fun x => x 0 ∉ S).card ≤
      4 * ((Finset.univ : Finset (Fin 5)).filter fun r => r ∉ S).card := by
  classical
  let R : Finset (Fin 5) := (Finset.univ : Finset (Fin 5)).filter fun r => r ∉ S
  have hcover : (C.filter fun x => x 0 ∉ S) ⊆ R.biUnion (rowSet C) := by
    intro x hx
    exact Finset.mem_biUnion.mpr
      ⟨x 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩,
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, rfl⟩⟩
  calc
    (C.filter fun x => x 0 ∉ S).card ≤ (R.biUnion (rowSet C)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ r ∈ R, (rowSet C r).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, 4 := by
      exact Finset.sum_le_sum fun r _hr => hrow r
    _ = 4 * R.card := by
      simp [Nat.mul_comm]

theorem card_columns_in_set_le
    {C : Finset (Fin 2 → Fin 5)} (hcol : ∀ c, (colSet C c).card ≤ 4)
    (N : Finset (Fin 5)) (hCN : ∀ x ∈ C, x 1 ∈ N) :
    C.card ≤ 4 * N.card := by
  classical
  have hcover : C ⊆ N.biUnion (colSet C) := by
    intro x hx
    exact Finset.mem_biUnion.mpr
      ⟨x 1, hCN x hx, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  calc
    C.card ≤ (N.biUnion (colSet C)).card := Finset.card_le_card hcover
    _ ≤ ∑ c ∈ N, (colSet C c).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ N, 4 := by
      exact Finset.sum_le_sum fun c _hc => hcol c
    _ = 4 * N.card := by
      simp [Nat.mul_comm]

theorem codeModelFree_5_5_2_card_le_sixteen
    {C : Finset (Fin 2 → Fin 5)} (hfree : CodeModelFree 5 5 2 C) :
    C.card ≤ 16 := by
  classical
  let Nbr : Fin 5 → Finset (Fin 5) := rowNeighbors C
  have hnoSDR : ¬ ∃ p : Fin 5 → Fin 5, Function.Injective p ∧ ∀ r, p r ∈ Nbr r := by
    simpa [Nbr] using no_neighborSDR_of_codeModelFree hfree
  have hnotHall :
      ¬ ∀ S : Finset (Fin 5), S.card ≤ (S.biUnion fun r => Nbr r).card := by
    intro hHall
    exact hnoSDR ((Finset.all_card_le_biUnion_card_iff_existsInjective' Nbr).1 hHall)
  rcases not_forall.mp hnotHall with ⟨S, hHallBad⟩
  let N : Finset (Fin 5) := S.biUnion fun r => Nbr r
  have hNlt : N.card < S.card := by
    exact Nat.lt_of_not_ge (by simpa [N] using hHallBad)
  have hSpos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hNlt
  have hrow : ∀ r, (rowSet C r).card ≤ 4 :=
    rowSet_card_le_four_of_codeModelFree hfree
  have hcol : ∀ c, (colSet C c).card ≤ 4 :=
    colSet_card_le_four_of_codeModelFree hfree
  by_cases hSfull : S.card = 5
  · have hNle4 : N.card ≤ 4 := by omega
    have hCN : ∀ x ∈ C, x 1 ∈ N := by
      intro x hx
      have hxrow : x 0 ∈ S := by
        have hSuniv : S = Finset.univ := (S.card_eq_iff_eq_univ).mp hSfull
        simp [hSuniv]
      exact Finset.mem_biUnion.mpr
        ⟨x 0, hxrow, by
          exact Finset.mem_image.mpr
            ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩⟩
    calc
      C.card ≤ 4 * N.card := card_columns_in_set_le hcol N hCN
      _ ≤ 4 * 4 := Nat.mul_le_mul_left 4 hNle4
      _ = 16 := by norm_num
  · have hSle4 : S.card ≤ 4 := by
      have hSle5 : S.card ≤ 5 := by
        simpa using Finset.card_le_univ S
      omega
    let R : Finset (Fin 5) := (Finset.univ : Finset (Fin 5)).filter fun r => r ∉ S
    have hRcard : R.card = 5 - S.card := by
      have hsplit :=
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin 5))) (p := fun r => r ∈ S)
      have hfilter : ((Finset.univ : Finset (Fin 5)).filter fun r => r ∈ S).card = S.card := by
        congr
        ext r
        simp
      have huniv : (Finset.univ : Finset (Fin 5)).card = 5 := by simp
      have hsplit' : S.card + R.card = 5 := by
        simpa [R, hfilter, huniv] using hsplit
      omega
    have hsplitC :
        C.card =
          (C.filter fun x => x 0 ∈ S).card + (C.filter fun x => x 0 ∉ S).card := by
      exact
        (Finset.card_filter_add_card_filter_not
          (s := C) (p := fun x => x 0 ∈ S)).symm
    have hinside :
        (C.filter fun x => x 0 ∈ S).card ≤ S.card * N.card := by
      simpa [N, Nbr] using card_rows_in_set_le C S
    have houtside :
        (C.filter fun x => x 0 ∉ S).card ≤ 4 * R.card := by
      simpa [R] using card_rows_outside_set_le hrow S
    have hNle : N.card ≤ S.card - 1 := by omega
    calc
      C.card =
          (C.filter fun x => x 0 ∈ S).card + (C.filter fun x => x 0 ∉ S).card := hsplitC
      _ ≤ S.card * N.card + 4 * R.card := Nat.add_le_add hinside houtside
      _ ≤ S.card * (S.card - 1) + 4 * R.card := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left S.card hNle) _
      _ ≤ 4 * (S.card - 1) + 4 * R.card := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_right (S.card - 1) hSle4) _
      _ = 16 := by omega

/-- The lower-bound half of the paper statement `F_{5,5}(2)=16`. -/
theorem sixteen_le_codeModelNumber_5_5_2 :
    16 ≤ codeModelNumber 5 5 2 := by
  have h := card_le_codeModelNumber (C := fourByFourGridInFive)
    fourByFourGridInFive_codeModelFree
  simpa [fourByFourGridInFive_card] using h

theorem codeModelNumber_5_5_2_le_sixteen :
    codeModelNumber 5 5 2 ≤ 16 := by
  apply codeModelNumber_le_of_code_bound
  intro C hfree
  exact codeModelFree_5_5_2_card_le_sixteen hfree

/-- The paper statement `F_{5,5}(2)=16`. -/
theorem codeModelNumber_5_5_2_eq_sixteen :
    codeModelNumber 5 5 2 = 16 :=
  le_antisymm codeModelNumber_5_5_2_le_sixteen sixteen_le_codeModelNumber_5_5_2

end FormalConjectures.Problems.Erdos.E20.Compendium
