import FormalConjectures.Problems.Erdos.E20.Compendium.Models.CodeModels

open scoped BigOperators Pointwise
open Finset

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-!
# Iterated Extra-Symbol Recurrence

This file gives the direct support decomposition for adding `t` symbols to a
fixed alphabet.  A word over `Fin (q + t)` is split into the coordinates using
one of the first `q` symbols and, on the complement, the chosen extra symbol.
Each fixed support/pattern fiber projects injectively to a code over `Fin q`.
-/

/-- Coordinates on which a word over `[q+t]` uses one of the original `q` symbols. -/
def iteratedBaseSupport (q t m : ℕ) (x : Fin m → Fin (q + t)) : Finset (Fin m) :=
  Finset.univ.filter fun j => (x j).val < q

@[simp] theorem mem_iteratedBaseSupport_iff {q t m : ℕ} {x : Fin m → Fin (q + t)}
    {j : Fin m} :
    j ∈ iteratedBaseSupport q t m x ↔ (x j).val < q := by
  simp [iteratedBaseSupport]

@[simp] theorem not_mem_iteratedBaseSupport_iff {q t m : ℕ}
    {x : Fin m → Fin (q + t)} {j : Fin m} :
    j ∉ iteratedBaseSupport q t m x ↔ q ≤ (x j).val := by
  simp [iteratedBaseSupport, not_lt]

/-- On the complement of a fixed base support, record which of the `t` extra symbols occurs. -/
noncomputable def iteratedExtraPattern {q t m : ℕ} {T : Finset (Fin m)}
    (x : Fin m → Fin (q + t)) (hxT : iteratedBaseSupport q t m x = T) :
    {j : Fin m // j ∉ T} → Fin t :=
  fun j =>
    ⟨(x j.1).val - q, by
      have hjnot : j.1 ∉ iteratedBaseSupport q t m x := by
        simpa [hxT] using j.2
      have hge : q ≤ (x j.1).val := not_mem_iteratedBaseSupport_iff.mp hjnot
      have hlt : (x j.1).val < q + t := (x j.1).isLt
      omega⟩

theorem iteratedExtraPattern_val {q t m : ℕ} {T : Finset (Fin m)}
    (x : Fin m → Fin (q + t)) (hxT : iteratedBaseSupport q t m x = T)
    (j : {j : Fin m // j ∉ T}) :
    (x j.1).val = q + (iteratedExtraPattern x hxT j).val := by
  have hjnot : j.1 ∉ iteratedBaseSupport q t m x := by
    simpa [hxT] using j.2
  have hge : q ≤ (x j.1).val := not_mem_iteratedBaseSupport_iff.mp hjnot
  simp [iteratedExtraPattern]
  omega

/-- The class of codewords with a fixed base support and fixed choices of the extra symbols
on its complement. -/
def iteratedSupportFiber (q t : ℕ) {m : ℕ} (C : Finset (Fin m → Fin (q + t)))
    (T : Finset (Fin m)) (η : {j : Fin m // j ∉ T} → Fin t) :
    Finset (Fin m → Fin (q + t)) :=
  C.filter fun x =>
    iteratedBaseSupport q t m x = T ∧
      ∀ j : {j : Fin m // j ∉ T}, (x j.1).val = q + (η j).val

@[simp] theorem mem_iteratedSupportFiber_iff {q t m : ℕ}
    {C : Finset (Fin m → Fin (q + t))} {T : Finset (Fin m)}
    {η : {j : Fin m // j ∉ T} → Fin t} {x : Fin m → Fin (q + t)} :
    x ∈ iteratedSupportFiber q t C T η ↔
      x ∈ C ∧ iteratedBaseSupport q t m x = T ∧
        ∀ j : {j : Fin m // j ∉ T}, (x j.1).val = q + (η j).val := by
  simp [iteratedSupportFiber]

theorem iteratedSupportFiber_baseSupport_eq {q t m : ℕ}
    {C : Finset (Fin m → Fin (q + t))} {T : Finset (Fin m)}
    {η : {j : Fin m // j ∉ T} → Fin t} {x : Fin m → Fin (q + t)}
    (hx : x ∈ iteratedSupportFiber q t C T η) :
    iteratedBaseSupport q t m x = T :=
  (mem_iteratedSupportFiber_iff.mp hx).2.1

/-- Delete the extra-symbol coordinates from a member of a fixed support/pattern fiber. -/
noncomputable def iteratedSupportFiberProjection {q t m : ℕ}
    {C : Finset (Fin m → Fin (q + t))} {T : Finset (Fin m)}
    {η : {j : Fin m // j ∉ T} → Fin t}
    (x : Fin m → Fin (q + t)) (hx : x ∈ iteratedSupportFiber q t C T η) :
    T → Fin q :=
  fun j =>
    ⟨(x j.1).val, by
      have hsupport : iteratedBaseSupport q t m x = T :=
        iteratedSupportFiber_baseSupport_eq hx
      have hj : j.1 ∈ iteratedBaseSupport q t m x := by
        simp [hsupport, j.2]
      exact mem_iteratedBaseSupport_iff.mp hj⟩

theorem iteratedSupportFiberProjection_val {q t m : ℕ}
    {C : Finset (Fin m → Fin (q + t))} {T : Finset (Fin m)}
    {η : {j : Fin m // j ∉ T} → Fin t}
    (x : Fin m → Fin (q + t)) (hx : x ∈ iteratedSupportFiber q t C T η)
    (j : T) :
    (iteratedSupportFiberProjection x hx j).val = (x j.1).val :=
  rfl

theorem iteratedSupportFiberProjection_attach_injective {q t m : ℕ}
    {C : Finset (Fin m → Fin (q + t))} {T : Finset (Fin m)}
    {η : {j : Fin m // j ∉ T} → Fin t} :
    Function.Injective
      (fun x : {x // x ∈ iteratedSupportFiber q t C T η} =>
        iteratedSupportFiberProjection x.1 x.2) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  apply Fin.ext
  by_cases hj : j ∈ T
  · have hcoord := congr_fun hxy ⟨j, hj⟩
    simpa [iteratedSupportFiberProjection] using congrArg Fin.val hcoord
  · have hxextra := (mem_iteratedSupportFiber_iff.mp x.2).2.2 ⟨j, hj⟩
    have hyextra := (mem_iteratedSupportFiber_iff.mp y.2).2.2 ⟨j, hj⟩
    rw [hxextra, hyextra]

/-- The projected code attached to one fixed support/pattern class. -/
noncomputable def iteratedSupportFiberCode (q t : ℕ) {m : ℕ}
    (C : Finset (Fin m → Fin (q + t))) (T : Finset (Fin m))
    (η : {j : Fin m // j ∉ T} → Fin t) : Finset (T → Fin q) :=
  (iteratedSupportFiber q t C T η).attach.image fun x =>
    iteratedSupportFiberProjection x.1 x.2

theorem iteratedSupportFiberCode_card {q t m : ℕ}
    (C : Finset (Fin m → Fin (q + t))) (T : Finset (Fin m))
    (η : {j : Fin m // j ∉ T} → Fin t) :
    (iteratedSupportFiberCode q t C T η).card =
      (iteratedSupportFiber q t C T η).card := by
  classical
  unfold iteratedSupportFiberCode
  rw [Finset.card_image_of_injective]
  · simp
  · exact iteratedSupportFiberProjection_attach_injective

theorem iteratedSupportFiberCode_free {q t k m : ℕ}
    {C : Finset (Fin m → Fin (q + t))}
    (hfree : CodeModelFree (q + t) k m C) (T : Finset (Fin m))
    (η : {j : Fin m // j ∉ T} → Fin t) :
    CodeModelFreeOn T q k (iteratedSupportFiberCode q t C T η) := by
  classical
  intro f hf hmem
  have hpre :
      ∀ i, ∃ x : {x // x ∈ iteratedSupportFiber q t C T η},
        iteratedSupportFiberProjection x.1 x.2 = f i := by
    intro i
    rcases Finset.mem_image.mp (hmem i) with ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  choose x hxproj using hpre
  let g : Fin k → Fin m → Fin (q + t) := fun i => x i
  have hgmem : ∀ i, g i ∈ C := by
    intro i
    exact (mem_iteratedSupportFiber_iff.mp (x i).2).1
  have hginj : Function.Injective g := by
    intro i i' hij
    apply hf
    calc
      f i = iteratedSupportFiberProjection (x i).1 (x i).2 := (hxproj i).symm
      _ = iteratedSupportFiberProjection (x i').1 (x i').2 := by
        have hsub : x i = x i' := Subtype.ext hij
        rw [hsub]
      _ = f i' := hxproj i'
  obtain ⟨j, hnotAll, hnotInj⟩ := hfree g hginj hgmem
  have hjT : j ∈ T := by
    by_contra hj
    apply hnotAll
    intro a b
    apply Fin.ext
    have ha := (mem_iteratedSupportFiber_iff.mp (x a).2).2.2 ⟨j, hj⟩
    have hb := (mem_iteratedSupportFiber_iff.mp (x b).2).2.2 ⟨j, hj⟩
    simpa [g] using ha.trans hb.symm
  refine ⟨⟨j, hjT⟩, ?_, ?_⟩
  · intro hall
    apply hnotAll
    intro a b
    apply Fin.ext
    have hproj :
        iteratedSupportFiberProjection (x a).1 (x a).2 ⟨j, hjT⟩ =
          iteratedSupportFiberProjection (x b).1 (x b).2 ⟨j, hjT⟩ := by
      calc
        iteratedSupportFiberProjection (x a).1 (x a).2 ⟨j, hjT⟩ = f a ⟨j, hjT⟩ :=
          congr_fun (hxproj a) ⟨j, hjT⟩
        _ = f b ⟨j, hjT⟩ := hall a b
        _ = iteratedSupportFiberProjection (x b).1 (x b).2 ⟨j, hjT⟩ :=
          (congr_fun (hxproj b) ⟨j, hjT⟩).symm
    simpa [iteratedSupportFiberProjection, g] using congrArg Fin.val hproj
  · intro hinj
    apply hnotInj
    intro a b hab
    apply hinj
    have hproj :
        iteratedSupportFiberProjection (x a).1 (x a).2 ⟨j, hjT⟩ =
          iteratedSupportFiberProjection (x b).1 (x b).2 ⟨j, hjT⟩ := by
      apply Fin.ext
      simpa [iteratedSupportFiberProjection, g] using congrArg Fin.val hab
    calc
      f a ⟨j, hjT⟩ = iteratedSupportFiberProjection (x a).1 (x a).2 ⟨j, hjT⟩ :=
        (congr_fun (hxproj a) ⟨j, hjT⟩).symm
      _ = iteratedSupportFiberProjection (x b).1 (x b).2 ⟨j, hjT⟩ := hproj
      _ = f b ⟨j, hjT⟩ := congr_fun (hxproj b) ⟨j, hjT⟩

theorem iteratedSupportFiber_card_le_codeModelNumber {q t k m : ℕ}
    {C : Finset (Fin m → Fin (q + t))}
    (hfree : CodeModelFree (q + t) k m C) (T : Finset (Fin m))
    (η : {j : Fin m // j ∉ T} → Fin t) :
    (iteratedSupportFiber q t C T η).card ≤ codeModelNumber q k T.card := by
  have hcode := iteratedSupportFiberCode_free hfree T η
  have hle :=
    card_le_codeModelNumber_of_codeModelFreeOn
      (C := iteratedSupportFiberCode q t C T η) hcode
  simpa [iteratedSupportFiberCode_card C T η, Fintype.card_coe] using hle

theorem card_support_complement_subtype {m : ℕ} (T : Finset (Fin m)) :
    Fintype.card {j : Fin m // j ∉ T} = m - T.card := by
  classical
  rw [Fintype.card_subtype_compl (α := Fin m) (p := fun j : Fin m => j ∈ T)]
  simp [Fintype.card_fin, Fintype.card_coe]

theorem card_extra_patterns {t m : ℕ} (T : Finset (Fin m)) :
    (Finset.univ : Finset ({j : Fin m // j ∉ T} → Fin t)).card =
      t ^ (m - T.card) := by
  classical
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    card_support_complement_subtype T]

theorem sum_codeModelNumber_by_weighted_support_card (q k m t : ℕ) :
    (∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
        t ^ (m - T.card) * codeModelNumber q k T.card) =
      ∑ r ∈ Finset.range (m + 1),
        m.choose r * t ^ (m - r) * codeModelNumber q k r := by
  classical
  let U : Finset (Fin m) := Finset.univ
  calc
    (∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
        t ^ (m - T.card) * codeModelNumber q k T.card)
        = ∑ T ∈ U.powerset, t ^ (m - T.card) * codeModelNumber q k T.card := by
          simp [U]
    _ = ∑ T ∈ (Finset.range (U.card + 1)).biUnion (fun r => U.powersetCard r),
          t ^ (m - T.card) * codeModelNumber q k T.card := by
          rw [← Finset.powerset_card_biUnion U]
    _ = ∑ r ∈ Finset.range (U.card + 1), ∑ T ∈ U.powersetCard r,
          t ^ (m - T.card) * codeModelNumber q k T.card := by
          rw [Finset.sum_biUnion]
          exact U.pairwise_disjoint_powersetCard.set_pairwise _
    _ = ∑ r ∈ Finset.range (U.card + 1),
          (U.powersetCard r).card * (t ^ (m - r) * codeModelNumber q k r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_const_nat]
          intro T hT
          rw [(Finset.mem_powersetCard.mp hT).2]
    _ = ∑ r ∈ Finset.range (m + 1),
          m.choose r * t ^ (m - r) * codeModelNumber q k r := by
          simp [U, Nat.mul_assoc]

/-- **Theorem 10.1, iterated form, support-pattern bound.**
Partitioning by base coordinates and the extra-symbol choices on the complement gives the
concrete per-code inequality. -/
theorem iterated_extra_symbol_support_class_bound
    {q k m t : ℕ} {C : Finset (Fin m → Fin (q + t))}
    (hfree : CodeModelFree (q + t) k m C) :
    C.card ≤
      ∑ r ∈ Finset.range (m + 1),
        m.choose r * t ^ (m - r) * codeModelNumber q k r := by
  classical
  let U : Finset (Fin m) := Finset.univ
  let cover : Finset (Fin m → Fin (q + t)) :=
    U.powerset.biUnion fun T =>
      (Finset.univ : Finset ({j : Fin m // j ∉ T} → Fin t)).biUnion fun η =>
        iteratedSupportFiber q t C T η
  have hcover : C ⊆ cover := by
    intro x hxC
    let T : Finset (Fin m) := iteratedBaseSupport q t m x
    have hTpowerset : T ∈ U.powerset := by
      exact Finset.mem_powerset.mpr (by intro j hj; simp [U])
    let η : {j : Fin m // j ∉ T} → Fin t :=
      iteratedExtraPattern (q := q) (t := t) (m := m) (T := T) x rfl
    apply Finset.mem_biUnion.mpr
    refine ⟨T, hTpowerset, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨η, Finset.mem_univ η, ?_⟩
    exact mem_iteratedSupportFiber_iff.mpr
      ⟨hxC, rfl, fun j =>
        iteratedExtraPattern_val (q := q) (t := t) (m := m) (T := T) x rfl j⟩
  calc
    C.card ≤ cover.card := Finset.card_le_card hcover
    _ ≤ ∑ T ∈ U.powerset,
        ∑ η ∈ (Finset.univ : Finset ({j : Fin m // j ∉ T} → Fin t)),
          (iteratedSupportFiber q t C T η).card := by
          calc
            cover.card ≤ ∑ T ∈ U.powerset,
                ((Finset.univ : Finset ({j : Fin m // j ∉ T} → Fin t)).biUnion
                  fun η => iteratedSupportFiber q t C T η).card := by
              simpa [cover] using Finset.card_biUnion_le
            _ ≤ ∑ T ∈ U.powerset,
                ∑ η ∈ (Finset.univ : Finset ({j : Fin m // j ∉ T} → Fin t)),
                  (iteratedSupportFiber q t C T η).card := by
              apply Finset.sum_le_sum
              intro T hT
              exact Finset.card_biUnion_le
    _ ≤ ∑ T ∈ U.powerset,
        ∑ η ∈ (Finset.univ : Finset ({j : Fin m // j ∉ T} → Fin t)),
          codeModelNumber q k T.card := by
          apply Finset.sum_le_sum
          intro T hT
          apply Finset.sum_le_sum
          intro η hη
          exact iteratedSupportFiber_card_le_codeModelNumber hfree T η
    _ = ∑ T ∈ U.powerset, t ^ (m - T.card) * codeModelNumber q k T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [Finset.sum_const_nat]
          · rw [card_extra_patterns T]
          · intro η hη
            rfl
    _ = ∑ r ∈ Finset.range (m + 1),
        m.choose r * t ^ (m - r) * codeModelNumber q k r := by
          simpa [U] using sum_codeModelNumber_by_weighted_support_card q k m t

/-- **Theorem 10.1, iterated form.**
Adding `t` symbols to the alphabet costs the binomial convolution over base supports and
extra-symbol patterns on their complements. -/
theorem iterated_extra_symbol_recurrence (q k m t : ℕ) :
    codeModelNumber (q + t) k m ≤
      ∑ r ∈ Finset.range (m + 1),
        m.choose r * t ^ (m - r) * codeModelNumber q k r :=
  codeModelNumber_le_of_code_bound fun C hfree =>
    iterated_extra_symbol_support_class_bound (C := C) hfree

end FormalConjectures.Problems.Erdos.E20.Compendium
