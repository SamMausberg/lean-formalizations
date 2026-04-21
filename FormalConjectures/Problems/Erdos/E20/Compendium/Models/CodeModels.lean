import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Core.Defs

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium

def CodeModelFree (q k m : ℕ) (C : Finset (Fin m → Fin q)) : Prop :=
  ∀ (f : Fin k → Fin m → Fin q),
    Function.Injective f →
    (∀ i, f i ∈ C) →
    ∃ j : Fin m, ¬(∀ a b : Fin k, f a j = f b j) ∧
                  ¬(Function.Injective (fun a => f a j))

/-- The same fixed-alphabet code model over an arbitrary finite coordinate type. -/
def CodeModelFreeOn (ι : Type*) [Fintype ι] (q k : ℕ) (C : Finset (ι → Fin q)) :
    Prop :=
  ∀ (f : Fin k → ι → Fin q),
    Function.Injective f →
    (∀ i, f i ∈ C) →
    ∃ j : ι, ¬(∀ a b : Fin k, f a j = f b j) ∧
                  ¬(Function.Injective (fun a => f a j))

theorem codeModelNumber_bddAbove (q k m : ℕ) :
    BddAbove {c : ℕ | ∃ (C : Finset (Fin m → Fin q)),
      C.card = c ∧ CodeModelFree q k m C} := by
  refine ⟨Fintype.card (Fin m → Fin q), ?_⟩
  rintro c ⟨C, rfl, -⟩
  exact Finset.card_le_univ C

theorem card_le_codeModelNumber {q k m : ℕ} {C : Finset (Fin m → Fin q)}
    (hfree : CodeModelFree q k m C) :
    C.card ≤ codeModelNumber q k m := by
  unfold codeModelNumber
  exact le_csSup (codeModelNumber_bddAbove q k m) ⟨C, rfl, hfree⟩

/-- Reindexing an admissible code on any finite coordinate type by an equivalence with `Fin n`
shows that its size is bounded by the corresponding extremal number. -/
theorem card_le_codeModelNumber_of_codeModelFreeOn
    {ι : Type*} [Fintype ι] {q k : ℕ} {C : Finset (ι → Fin q)}
    (hfree : CodeModelFreeOn ι q k C) :
    C.card ≤ codeModelNumber q k (Fintype.card ι) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let D : Finset (Fin (Fintype.card ι) → Fin q) :=
    C.image fun x => fun j => x (e.symm j)
  have hDfree : CodeModelFree q k (Fintype.card ι) D := by
    intro f hf hmem
    let g : Fin k → ι → Fin q := fun i a => f i (e a)
    have hgmem : ∀ i, g i ∈ C := by
      intro i
      rcases Finset.mem_image.mp (hmem i) with ⟨x, hxC, hx⟩
      have hgi : g i = x := by
        funext a
        have hcoord := congr_fun hx (e a)
        simpa [g] using hcoord.symm
      simpa [hgi] using hxC
    have hginj : Function.Injective g := by
      intro i j hij
      apply hf
      funext a
      have hcoord := congr_fun hij (e.symm a)
      simpa [g] using hcoord
    obtain ⟨a, hnotAll, hnotInj⟩ := hfree g hginj hgmem
    refine ⟨e a, ?_, ?_⟩
    · intro hall
      apply hnotAll
      intro u v
      simpa [g] using hall u v
    · intro hinj
      apply hnotInj
      intro u v huv
      apply hinj
      simpa [g] using huv
  have hle := card_le_codeModelNumber (C := D) hDfree
  have hcard : D.card = C.card := by
    dsimp [D]
    rw [Finset.card_image_of_injective]
    intro x y hxy
    funext a
    have hcoord := congr_fun hxy (e a)
    simpa using hcoord
  simpa [hcard] using hle


/-!
# Section 10: Fixed-Alphabet Code Models

This file packages the results from Section 10 of the sunflower compendium
(sunflower_compendium.pdf): "Fixed-alphabet code models: rigorous recurrences
and provisional local tensors." The recurrence statements below are kept
honest: when the current local definitions do not yet support a full proof, the file
only records the checked extremalization step from an explicit per-code bound.
-/

/-- If every admissible code has size at most `B`, then the extremal code-model number is at
most `B`.  This is the `csSup` packaging step used by the conditional recurrence reductions
below. -/
theorem codeModelNumber_le_of_code_bound
    {q k m B : ℕ}
    (hbound : ∀ (C : Finset (Fin m → Fin q)), CodeModelFree q k m C → C.card ≤ B) :
    codeModelNumber q k m ≤ B := by
  unfold codeModelNumber
  apply csSup_le'
  intro c hc
  rcases hc with ⟨C, rfl, hfree⟩
  exact hbound C hfree

/-- Coordinates on which a word over `[q+1]` uses one of the original `q` symbols. -/
def baseSupport (q m : ℕ) (x : Fin m → Fin (q + 1)) : Finset (Fin m) :=
  Finset.univ.filter fun j => x j ≠ Fin.last q

@[simp] theorem mem_baseSupport_iff {q m : ℕ} {x : Fin m → Fin (q + 1)}
    {j : Fin m} :
    j ∈ baseSupport q m x ↔ x j ≠ Fin.last q := by
  simp [baseSupport]

@[simp] theorem not_mem_baseSupport_iff {q m : ℕ} {x : Fin m → Fin (q + 1)}
    {j : Fin m} :
    j ∉ baseSupport q m x ↔ x j = Fin.last q := by
  simp [baseSupport]

/-- The class of codewords with a fixed set of original-symbol coordinates. -/
def supportFiber (q : ℕ) {m : ℕ} (C : Finset (Fin m → Fin (q + 1)))
    (T : Finset (Fin m)) : Finset (Fin m → Fin (q + 1)) :=
  C.filter fun x => baseSupport q m x = T

@[simp] theorem mem_supportFiber_iff {q m : ℕ} {C : Finset (Fin m → Fin (q + 1))}
    {T : Finset (Fin m)} {x : Fin m → Fin (q + 1)} :
    x ∈ supportFiber q C T ↔ x ∈ C ∧ baseSupport q m x = T := by
  simp [supportFiber]

theorem supportFiber_baseSupport_eq {q m : ℕ} {C : Finset (Fin m → Fin (q + 1))}
    {T : Finset (Fin m)} {x : Fin m → Fin (q + 1)}
    (hx : x ∈ supportFiber q C T) :
    baseSupport q m x = T :=
  (mem_supportFiber_iff.mp hx).2

/-- Delete the coordinates carrying the extra symbol from a member of a fixed support fiber. -/
noncomputable def supportFiberProjection {q m : ℕ} {T : Finset (Fin m)}
    (x : Fin m → Fin (q + 1)) (hx : baseSupport q m x = T) : T → Fin q :=
  fun j =>
    Fin.castPred (x j.1) (by
      have hj : j.1 ∈ baseSupport q m x := by simp [hx, j.2]
      simpa using (mem_baseSupport_iff.mp hj))

theorem supportFiberProjection_castSucc {q m : ℕ} {T : Finset (Fin m)}
    (x : Fin m → Fin (q + 1)) (hx : baseSupport q m x = T) (j : T) :
    Fin.castSucc (supportFiberProjection x hx j) = x j.1 := by
  simp [supportFiberProjection]

theorem supportFiberProjection_attach_injective {q m : ℕ}
    {C : Finset (Fin m → Fin (q + 1))} {T : Finset (Fin m)} :
    Function.Injective
      (fun x : {x // x ∈ supportFiber q C T} =>
        supportFiberProjection x.1 (supportFiber_baseSupport_eq x.2)) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ T
  · have hcoord := congr_fun hxy ⟨j, hj⟩
    calc
      x.1 j =
          Fin.castSucc
            (supportFiberProjection x.1 (supportFiber_baseSupport_eq x.2) ⟨j, hj⟩) :=
        (supportFiberProjection_castSucc x.1 (supportFiber_baseSupport_eq x.2) ⟨j, hj⟩).symm
      _ =
          Fin.castSucc
            (supportFiberProjection y.1 (supportFiber_baseSupport_eq y.2) ⟨j, hj⟩) := by
        exact congrArg Fin.castSucc hcoord
      _ = y.1 j :=
        supportFiberProjection_castSucc y.1 (supportFiber_baseSupport_eq y.2) ⟨j, hj⟩
  · have hxSupport : baseSupport q m x.1 = T := supportFiber_baseSupport_eq x.2
    have hySupport : baseSupport q m y.1 = T := supportFiber_baseSupport_eq y.2
    have hxlast : x.1 j = Fin.last q := by
      have : j ∉ baseSupport q m x.1 := by simpa [hxSupport] using hj
      simpa using (not_mem_baseSupport_iff.mp this)
    have hylast : y.1 j = Fin.last q := by
      have : j ∉ baseSupport q m y.1 := by simpa [hySupport] using hj
      simpa using (not_mem_baseSupport_iff.mp this)
    rw [hxlast, hylast]

/-- The projected code attached to one fixed support class. -/
noncomputable def supportFiberCode (q : ℕ) {m : ℕ}
    (C : Finset (Fin m → Fin (q + 1))) (T : Finset (Fin m)) : Finset (T → Fin q) :=
  (supportFiber q C T).attach.image fun x =>
    supportFiberProjection x.1 (supportFiber_baseSupport_eq x.2)

theorem supportFiberCode_card {q m : ℕ} (C : Finset (Fin m → Fin (q + 1)))
    (T : Finset (Fin m)) :
    (supportFiberCode q C T).card = (supportFiber q C T).card := by
  classical
  unfold supportFiberCode
  rw [Finset.card_image_of_injective]
  · simp
  · exact supportFiberProjection_attach_injective

theorem supportFiberCode_free {q k m : ℕ} {C : Finset (Fin m → Fin (q + 1))}
    (hfree : CodeModelFree (q + 1) k m C) (T : Finset (Fin m)) :
    CodeModelFreeOn T q k (supportFiberCode q C T) := by
  classical
  intro f hf hmem
  have hpre :
      ∀ i, ∃ x : {x // x ∈ supportFiber q C T},
        supportFiberProjection x.1 (supportFiber_baseSupport_eq x.2) = f i := by
    intro i
    rcases Finset.mem_image.mp (hmem i) with ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  choose x hxproj using hpre
  let g : Fin k → Fin m → Fin (q + 1) := fun i => x i
  have hgmem : ∀ i, g i ∈ C := by
    intro i
    exact (mem_supportFiber_iff.mp (x i).2).1
  have hginj : Function.Injective g := by
    intro i j hij
    apply hf
    calc
      f i = supportFiberProjection (x i).1 (supportFiber_baseSupport_eq (x i).2) :=
        (hxproj i).symm
      _ = supportFiberProjection (x j).1 (supportFiber_baseSupport_eq (x j).2) := by
        have hsub : x i = x j := Subtype.ext hij
        rw [hsub]
      _ = f j := hxproj j
  obtain ⟨j, hnotAll, hnotInj⟩ := hfree g hginj hgmem
  have hjT : j ∈ T := by
    by_contra hj
    apply hnotAll
    intro a b
    have haSupport : baseSupport q m (g a) = T := supportFiber_baseSupport_eq (x a).2
    have hbSupport : baseSupport q m (g b) = T := supportFiber_baseSupport_eq (x b).2
    have hja : j ∉ baseSupport q m (g a) := by simpa [haSupport] using hj
    have hjb : j ∉ baseSupport q m (g b) := by simpa [hbSupport] using hj
    rw [not_mem_baseSupport_iff.mp hja, not_mem_baseSupport_iff.mp hjb]
  refine ⟨⟨j, hjT⟩, ?_, ?_⟩
  · intro hall
    apply hnotAll
    intro a b
    have hcast : ∀ i, Fin.castSucc (f i ⟨j, hjT⟩) = g i j := by
      intro i
      have hcoord := congr_fun (hxproj i) ⟨j, hjT⟩
      rw [← hcoord]
      exact supportFiberProjection_castSucc (x i).1 (supportFiber_baseSupport_eq (x i).2) ⟨j, hjT⟩
    calc
      g a j = Fin.castSucc (f a ⟨j, hjT⟩) := (hcast a).symm
      _ = Fin.castSucc (f b ⟨j, hjT⟩) := by rw [hall a b]
      _ = g b j := hcast b
  · intro hinj
    apply hnotInj
    intro a b hab
    apply hinj
    apply Fin.castSucc_injective q
    have hcast : ∀ i, Fin.castSucc (f i ⟨j, hjT⟩) = g i j := by
      intro i
      have hcoord := congr_fun (hxproj i) ⟨j, hjT⟩
      rw [← hcoord]
      exact supportFiberProjection_castSucc (x i).1 (supportFiber_baseSupport_eq (x i).2) ⟨j, hjT⟩
    calc
      Fin.castSucc (f a ⟨j, hjT⟩) = g a j := hcast a
      _ = g b j := hab
      _ = Fin.castSucc (f b ⟨j, hjT⟩) := (hcast b).symm

theorem supportFiber_card_le_codeModelNumber {q k m : ℕ}
    {C : Finset (Fin m → Fin (q + 1))} (hfree : CodeModelFree (q + 1) k m C)
    (T : Finset (Fin m)) :
    (supportFiber q C T).card ≤ codeModelNumber q k T.card := by
  have hcode := supportFiberCode_free hfree T
  have hle :=
    card_le_codeModelNumber_of_codeModelFreeOn
      (C := supportFiberCode q C T) hcode
  simpa [supportFiberCode_card C T, Fintype.card_coe] using hle

theorem sum_codeModelNumber_by_support_card (q k m : ℕ) :
    (∑ T ∈ (Finset.univ : Finset (Fin m)).powerset, codeModelNumber q k T.card) =
      ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r := by
  classical
  let U : Finset (Fin m) := Finset.univ
  calc
    (∑ T ∈ (Finset.univ : Finset (Fin m)).powerset, codeModelNumber q k T.card)
        = ∑ T ∈ U.powerset, codeModelNumber q k T.card := by
          simp [U]
    _ = ∑ T ∈ (Finset.range (U.card + 1)).biUnion (fun r => U.powersetCard r),
          codeModelNumber q k T.card := by
          rw [← Finset.powerset_card_biUnion U]
    _ = ∑ r ∈ Finset.range (U.card + 1), ∑ T ∈ U.powersetCard r,
          codeModelNumber q k T.card := by
          rw [Finset.sum_biUnion]
          exact U.pairwise_disjoint_powersetCard.set_pairwise _
    _ = ∑ r ∈ Finset.range (U.card + 1),
          (U.powersetCard r).card * codeModelNumber q k r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_const_nat]
          intro T hT
          rw [(Finset.mem_powersetCard.mp hT).2]
    _ = ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r := by
          simp [U]

/-- **Theorem 10.1 (one extra symbol), support-class bound.**
Partitioning by the coordinates carrying the added symbol gives the exact per-code inequality. -/
theorem one_extra_symbol_support_class_bound
    {q k m : ℕ} {C : Finset (Fin m → Fin (q + 1))}
    (hfree : CodeModelFree (q + 1) k m C) :
    C.card ≤ ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r := by
  classical
  let σ : (Fin m → Fin (q + 1)) → Finset (Fin m) := baseSupport q m
  have hpartition :
      C.card = ∑ T ∈ C.image σ, (supportFiber q C T).card := by
    simpa [supportFiber, σ] using Finset.card_eq_sum_card_image (f := σ) (s := C)
  calc
    C.card = ∑ T ∈ C.image σ, (supportFiber q C T).card := hpartition
    _ ≤ ∑ T ∈ C.image σ, codeModelNumber q k T.card := by
      apply Finset.sum_le_sum
      intro T hT
      exact supportFiber_card_le_codeModelNumber hfree T
    _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset, codeModelNumber q k T.card := by
      apply Finset.sum_le_sum_of_subset
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨x, -, rfl⟩
      exact Finset.mem_powerset.mpr (by intro j hj; simp)
    _ = ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r :=
      sum_codeModelNumber_by_support_card q k m

/-- **Theorem 10.1 (one extra symbol).**
Adding one symbol to the alphabet costs the binomial convolution over support classes. -/
theorem one_extra_symbol_recurrence (q k m : ℕ) :
    codeModelNumber (q + 1) k m ≤
      ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r :=
  codeModelNumber_le_of_code_bound fun C hfree =>
    one_extra_symbol_support_class_bound (C := C) hfree

/-- Codewords surviving a coordinatewise restriction of the alphabet. -/
def coordinateSubsetSurvivors {Q m : ℕ} (C : Finset (Fin m → Fin Q))
    (A : Fin m → Finset (Fin Q)) : Finset (Fin m → Fin Q) :=
  C.filter fun x => ∀ j, x j ∈ A j

@[simp] theorem mem_coordinateSubsetSurvivors_iff {Q m : ℕ}
    {C : Finset (Fin m → Fin Q)} {A : Fin m → Finset (Fin Q)}
    {x : Fin m → Fin Q} :
    x ∈ coordinateSubsetSurvivors C A ↔ x ∈ C ∧ ∀ j, x j ∈ A j := by
  simp [coordinateSubsetSurvivors]

/-- Relabel a coordinatewise survivor code by equivalences from the chosen symbol sets
to `Fin q`. -/
noncomputable def coordinateSubsetCode {Q q m : ℕ} (C : Finset (Fin m → Fin Q))
    (A : Fin m → Finset (Fin Q)) (hA : ∀ j, (A j).card = q) :
    Finset (Fin m → Fin q) :=
  (coordinateSubsetSurvivors C A).attach.image fun x j =>
    (A j).equivFinOfCardEq (hA j)
      ⟨x.1 j, (mem_coordinateSubsetSurvivors_iff.mp x.2).2 j⟩

theorem coordinateSubsetProjection_attach_injective {Q q m : ℕ}
    {C : Finset (Fin m → Fin Q)} {A : Fin m → Finset (Fin Q)}
    (hA : ∀ j, (A j).card = q) :
    Function.Injective
      (fun x : {x // x ∈ coordinateSubsetSurvivors C A} => fun j =>
        (A j).equivFinOfCardEq (hA j)
          ⟨x.1 j, (mem_coordinateSubsetSurvivors_iff.mp x.2).2 j⟩) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  have hcoord := congr_fun hxy j
  have hsub :
      (⟨x.1 j, (mem_coordinateSubsetSurvivors_iff.mp x.2).2 j⟩ :
        {a // a ∈ A j}) =
      ⟨y.1 j, (mem_coordinateSubsetSurvivors_iff.mp y.2).2 j⟩ :=
    ((A j).equivFinOfCardEq (hA j)).injective hcoord
  exact congrArg Subtype.val hsub

theorem coordinateSubsetCode_card {Q q m : ℕ} (C : Finset (Fin m → Fin Q))
    (A : Fin m → Finset (Fin Q)) (hA : ∀ j, (A j).card = q) :
    (coordinateSubsetCode C A hA).card = (coordinateSubsetSurvivors C A).card := by
  classical
  unfold coordinateSubsetCode
  rw [Finset.card_image_of_injective]
  · simp
  · exact coordinateSubsetProjection_attach_injective hA

/-- The deterministic preservation step behind randomized deletion: after keeping any
coordinatewise `q`-subsets of symbols and relabeling them as `[q]`, admissibility is preserved. -/
theorem coordinateSubsetCode_free {Q q k m : ℕ} {C : Finset (Fin m → Fin Q)}
    (hfree : CodeModelFree Q k m C) (A : Fin m → Finset (Fin Q))
    (hA : ∀ j, (A j).card = q) :
    CodeModelFree q k m (coordinateSubsetCode C A hA) := by
  classical
  intro f hf hmem
  have hpre :
      ∀ i, ∃ x : {x // x ∈ coordinateSubsetSurvivors C A},
        (fun j =>
          (A j).equivFinOfCardEq (hA j)
            ⟨x.1 j, (mem_coordinateSubsetSurvivors_iff.mp x.2).2 j⟩) = f i := by
    intro i
    rcases Finset.mem_image.mp (hmem i) with ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  choose x hxproj using hpre
  let g : Fin k → Fin m → Fin Q := fun i => x i
  have hgmem : ∀ i, g i ∈ C := by
    intro i
    exact (mem_coordinateSubsetSurvivors_iff.mp (x i).2).1
  have hginj : Function.Injective g := by
    intro i i' hij
    apply hf
    calc
      f i =
          (fun c =>
            (A c).equivFinOfCardEq (hA c)
              ⟨(x i).1 c, (mem_coordinateSubsetSurvivors_iff.mp (x i).2).2 c⟩) :=
        (hxproj i).symm
      _ =
          (fun c =>
            (A c).equivFinOfCardEq (hA c)
              ⟨(x i').1 c, (mem_coordinateSubsetSurvivors_iff.mp (x i').2).2 c⟩) := by
        have hsub : x i = x i' := Subtype.ext hij
        rw [hsub]
      _ = f i' := hxproj i'
  obtain ⟨j, hnotAll, hnotInj⟩ := hfree g hginj hgmem
  refine ⟨j, ?_, ?_⟩
  · intro hall
    apply hnotAll
    intro a b
    have hcoordA := congr_fun (hxproj a) j
    have hcoordB := congr_fun (hxproj b) j
    have heqImage :
        (A j).equivFinOfCardEq (hA j)
            ⟨g a j, (mem_coordinateSubsetSurvivors_iff.mp (x a).2).2 j⟩ =
          (A j).equivFinOfCardEq (hA j)
            ⟨g b j, (mem_coordinateSubsetSurvivors_iff.mp (x b).2).2 j⟩ := by
      rw [hcoordA, hcoordB, hall a b]
    have hsub :=
      ((A j).equivFinOfCardEq (hA j)).injective heqImage
    exact congrArg Subtype.val hsub
  · intro hinj
    apply hnotInj
    intro a b hab
    apply hinj
    have hcoordA := congr_fun (hxproj a) j
    have hcoordB := congr_fun (hxproj b) j
    have hsub :
        (⟨g a j, (mem_coordinateSubsetSurvivors_iff.mp (x a).2).2 j⟩ :
          {s // s ∈ A j}) =
        ⟨g b j, (mem_coordinateSubsetSurvivors_iff.mp (x b).2).2 j⟩ :=
      Subtype.ext hab
    calc
      f a j =
          (A j).equivFinOfCardEq (hA j)
            ⟨g a j, (mem_coordinateSubsetSurvivors_iff.mp (x a).2).2 j⟩ :=
        hcoordA.symm
      _ =
          (A j).equivFinOfCardEq (hA j)
            ⟨g b j, (mem_coordinateSubsetSurvivors_iff.mp (x b).2).2 j⟩ := by
        rw [hsub]
      _ = f b j := hcoordB

/-- Every deterministic survivor code from coordinatewise `q`-subset deletion has size at most
the fixed-alphabet extremal number. -/
theorem coordinateSubset_survivor_card_le_codeModelNumber {Q q k m : ℕ}
    {C : Finset (Fin m → Fin Q)} (hfree : CodeModelFree Q k m C)
    (A : Fin m → Finset (Fin Q)) (hA : ∀ j, (A j).card = q) :
    (coordinateSubsetSurvivors C A).card ≤ codeModelNumber q k m := by
  have hcode := coordinateSubsetCode_free hfree A hA
  have hle := card_le_codeModelNumber (C := coordinateSubsetCode C A hA) hcode
  simpa [coordinateSubsetCode_card C A hA] using hle

/-- Extremalization helper for one-symbol support-class estimates.  The unconditional
support-class estimate above gives the concrete theorem `one_extra_symbol_recurrence`. -/
theorem one_extra_symbol_recurrence_of_support_class_bound
    (q k m : ℕ)
    (hbound : ∀ (C : Finset (Fin m → Fin (q + 1))),
      CodeModelFree (q + 1) k m C →
      C.card ≤ ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r) :
    codeModelNumber (q + 1) k m ≤
      ∑ r ∈ Finset.range (m + 1), m.choose r * codeModelNumber q k r :=
  codeModelNumber_le_of_code_bound hbound

/-- **Theorem 10.1, iterated form, extremalization step.**
If the iterated deletion/convolution estimate has already been proved for every concrete
`CodeModelFree (q + t) k m` code, then the stated extremal recurrence follows. -/
theorem iterated_extra_symbol_recurrence_of_code_bound
    (q k m t : ℕ)
    (hbound : ∀ (C : Finset (Fin m → Fin (q + t))),
      CodeModelFree (q + t) k m C →
      C.card ≤
        ∑ r ∈ Finset.range (m + 1), m.choose r * t ^ (m - r) * codeModelNumber q k r) :
    codeModelNumber (q + t) k m ≤
      ∑ r ∈ Finset.range (m + 1), m.choose r * t ^ (m - r) * codeModelNumber q k r :=
  codeModelNumber_le_of_code_bound hbound

/- **Theorem 10.2 (sharper randomized deletion lift).**
The deterministic deletion/relabeling step is formalized above as
`coordinateSubsetCode_free` and `coordinateSubset_survivor_card_le_codeModelNumber`.
The final scaled averaging over all coordinatewise `q`-subset selections is not proved in this
file, so no theorem for the final randomized inequality is asserted here. -/
end FormalConjectures.Problems.Erdos.E20.Compendium
