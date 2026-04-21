import FormalConjectures.Problems.Erdos.E20.Compendium.Models.BlockProducts

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-!
# Ordered sunflower counts for exact block products

This file adds the finite counting layer for the tagged singleton block-product model from
`BlockProducts.lean`.
-/

/-- In one coordinate of an ordered `k`-sunflower tuple, the coordinate is either constant
across the `k` petals or injective across the `k` petals. -/
abbrev BlockProductCoordinateChoice (k n : ℕ) : Type :=
  Fin n ⊕ (Fin k ↪ Fin n)

/-- The coordinate tuple encoded by a constant-or-injective local choice. -/
def coordinateChoiceTuple {k n : ℕ} :
    BlockProductCoordinateChoice k n → Fin k → Fin n
  | Sum.inl a => fun _ => a
  | Sum.inr e => fun t => e t

@[simp] theorem coordinateChoiceTuple_const {k n : ℕ} (a : Fin n) (t : Fin k) :
    coordinateChoiceTuple (Sum.inl a : BlockProductCoordinateChoice k n) t = a := rfl

@[simp] theorem coordinateChoiceTuple_injective {k n : ℕ} (e : Fin k ↪ Fin n) (t : Fin k) :
    coordinateChoiceTuple (Sum.inr e : BlockProductCoordinateChoice k n) t = e t := rfl

@[simp] theorem card_coordinateChoice (k n : ℕ) :
    Fintype.card (BlockProductCoordinateChoice k n) = n + n.descFactorial k := by
  simp [BlockProductCoordinateChoice, Fintype.card_embedding_eq]

/-- A coordinatewise constant/injective description of an ordered block-product sunflower.
At least one coordinate must be injective, so the `k` global petals are distinct. -/
abbrev BlockProductSunflowerChoice (r k : ℕ) (w : Fin r → ℕ) : Type :=
  { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
      ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e }

/-- The `t`th product word produced by a coordinatewise sunflower choice. -/
def choiceWord {r k : ℕ} {w : Fin r → ℕ}
    (c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i)) (t : Fin k) :
    BlockProductWord r w :=
  fun i => coordinateChoiceTuple (c i) t

/-- The common kernel of the sunflower encoded by coordinate choices: keep exactly the
coordinates that are locally constant. -/
noncomputable def choiceKernel {r k : ℕ} {w : Fin r → ℕ}
    (c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i)) :
    Finset (Sigma fun i : Fin r => Fin (w i)) :=
  Finset.univ.filter fun z =>
    match z with
    | Sigma.mk i a => c i = Sum.inl a

@[simp] theorem mem_choiceKernel_iff {r k : ℕ} {w : Fin r → ℕ}
    (c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i))
    (i : Fin r) (a : Fin (w i)) :
    Sigma.mk i a ∈ choiceKernel c ↔ c i = Sum.inl a := by
  simp [choiceKernel]

theorem choiceWord_inter {r k : ℕ} {w : Fin r → ℕ}
    (c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i)) {t u : Fin k}
    (htu : t ≠ u) :
    blockProductEdge (choiceWord c t) ∩ blockProductEdge (choiceWord c u) =
      choiceKernel c := by
  ext z
  rcases z with ⟨i, a⟩
  rw [Finset.mem_inter, mem_blockProductEdge_iff, mem_blockProductEdge_iff,
    mem_choiceKernel_iff]
  cases hc : c i with
  | inl b =>
      simp [choiceWord, hc]
  | inr e =>
      constructor
      · intro h
        have hetu : e t = e u := by
          simpa [choiceWord, hc] using h.1.trans h.2.symm
        exact False.elim (htu (e.injective hetu))
      · intro h
        cases h

theorem choiceWord_injective {r k : ℕ} {w : Fin r → ℕ}
    (c : BlockProductSunflowerChoice r k w) :
    Function.Injective (choiceWord c.1) := by
  rcases c.2 with ⟨i, e, hi⟩
  intro t u htu
  have hcoord : coordinateChoiceTuple (c.1 i) t = coordinateChoiceTuple (c.1 i) u := by
    exact congrFun htu i
  exact e.injective (by simpa [choiceWord, hi] using hcoord)

/-- The ordered petal function encoded by a coordinatewise sunflower choice. -/
noncomputable def choicePetals {r k : ℕ} {w : Fin r → ℕ}
    (c : BlockProductSunflowerChoice r k w) :
    Fin k → Finset (Sigma fun i : Fin r => Fin (w i)) :=
  fun t => blockProductEdge (choiceWord c.1 t)

theorem choicePetals_injective {r k : ℕ} {w : Fin r → ℕ}
    (c : BlockProductSunflowerChoice r k w) :
    Function.Injective (choicePetals c) := by
  intro t u htu
  exact choiceWord_injective c (blockProductEdge_injective htu)

/-- Every coordinatewise constant/injective choice gives an ordered `k`-sunflower in the
tagged singleton exact block product. -/
theorem choicePetals_isSunflower {r k : ℕ} {w : Fin r → ℕ}
    (c : BlockProductSunflowerChoice r k w) :
    IsSunflower (exactBlockProductFamily r w) k := by
  refine ⟨choicePetals c, choiceKernel c.1, ?_, choicePetals_injective c, ?_⟩
  · intro t
    exact blockProductEdge_mem_exactBlockProductFamily _
  · intro t u htu
    exact choiceWord_inter c.1 htu

/-- A no-injective-coordinate choice has a constant value in every coordinate. -/
private theorem exists_const_of_noInjectiveChoice {r k : ℕ} {w : Fin r → ℕ}
    (c :
      { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
        ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e })
    (i : Fin r) :
    ∃ a : Fin (w i), c.1 i = Sum.inl a := by
  cases hc : c.1 i with
  | inl a => exact ⟨a, rfl⟩
  | inr e => exact False.elim (c.2 ⟨i, e, hc⟩)

private noncomputable def noInjectiveChoiceValue {r k : ℕ} {w : Fin r → ℕ}
    (c :
      { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
        ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e })
    (i : Fin r) : Fin (w i) :=
  Classical.choose (exists_const_of_noInjectiveChoice c i)

private theorem noInjectiveChoiceValue_spec {r k : ℕ} {w : Fin r → ℕ}
    (c :
      { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
        ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e })
    (i : Fin r) :
    c.1 i = Sum.inl (noInjectiveChoiceValue c i) :=
  Classical.choose_spec (exists_const_of_noInjectiveChoice c i)

/-- Choices with no injective coordinate are exactly ordinary block-product words. -/
noncomputable def noInjectiveChoiceEquivWord (r k : ℕ) (w : Fin r → ℕ) :
    { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
        ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e } ≃
      BlockProductWord r w where
  toFun c := fun i => noInjectiveChoiceValue c i
  invFun x :=
    ⟨fun i => Sum.inl (x i), by
      rintro ⟨i, e, hi⟩
      cases hi⟩
  left_inv c := by
    ext i
    exact (noInjectiveChoiceValue_spec c i).symm
  right_inv x := by
    funext i
    let c0 :
        { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
          ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e } :=
      ⟨fun i => Sum.inl (x i), by
        rintro ⟨i, e, hi⟩
        cases hi⟩
    have hspec := noInjectiveChoiceValue_spec c0 i
    exact (Sum.inl.inj hspec).symm

theorem card_noInjectiveChoices (r k : ℕ) (w : Fin r → ℕ) :
    Fintype.card
        { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
          ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e } =
      blockProductCard r w := by
  classical
  calc
    Fintype.card
        { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
          ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e } =
        Fintype.card (BlockProductWord r w) :=
          Fintype.card_congr (noInjectiveChoiceEquivWord r k w)
    _ = blockProductCard r w := by
      simp [BlockProductWord, blockProductCard, Fintype.card_pi]

theorem card_allCoordinateChoices (r k : ℕ) (w : Fin r → ℕ) :
    Fintype.card (∀ i : Fin r, BlockProductCoordinateChoice k (w i)) =
      ∏ i : Fin r, (w i + (w i).descFactorial k) := by
  classical
  simp [BlockProductCoordinateChoice, Fintype.card_pi, Fintype.card_embedding_eq]

/-- Ordered coordinatewise sunflower choices are counted by choosing, independently in each
coordinate, either a constant value or an injection `Fin k ↪ Fin (w i)`, and deleting the
all-constant choices. -/
theorem card_blockProductSunflowerChoices (r k : ℕ) (w : Fin r → ℕ) :
    Fintype.card (BlockProductSunflowerChoice r k w) =
      (∏ i : Fin r, (w i + (w i).descFactorial k)) - blockProductCard r w := by
  classical
  let U : Finset (∀ i : Fin r, BlockProductCoordinateChoice k (w i)) := Finset.univ
  let P : (∀ i : Fin r, BlockProductCoordinateChoice k (w i)) → Prop :=
    fun c => ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e
  have hgood :
      (U.filter P).card = Fintype.card (BlockProductSunflowerChoice r k w) := by
    rw [← Finset.card_subtype (s := U) (p := P)]
    congr
    ext c
    simp [U, P, BlockProductSunflowerChoice]
  have hbad :
      (U.filter fun c => ¬ P c).card = blockProductCard r w := by
    rw [← Finset.card_subtype (s := U) (p := fun c => ¬ P c)]
    have hsub :
        U.subtype (fun c => ¬ P c) =
          (Finset.univ :
            Finset
              { c : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) //
                ¬ ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), c i = Sum.inr e }) := by
      ext c
      simp [U, P]
    rw [hsub, Finset.card_univ, card_noInjectiveChoices]
  have htotal :
      U.card = ∏ i : Fin r, (w i + (w i).descFactorial k) := by
    simp [U, BlockProductCoordinateChoice, Fintype.card_pi, Fintype.card_embedding_eq]
  have hsplit := Finset.card_filter_add_card_filter_not (s := U) (p := P)
  have hfilter :
      (U.filter P).card = U.card - (U.filter fun c => ¬ P c).card := by
    omega
  rw [← hgood, hfilter, htotal, hbad]

/-- The actual ordered petal functions obtained from coordinatewise choices. -/
noncomputable def orderedBlockProductSunflowerPetals (r k : ℕ) (w : Fin r → ℕ) :
    Finset (Fin k → Finset (Sigma fun i : Fin r => Fin (w i))) :=
  Finset.univ.image (choicePetals (r := r) (k := k) (w := w))

theorem choicePetals_ext_of_eq {r k : ℕ} {w : Fin r → ℕ} (hk : 2 ≤ k)
    {c d : BlockProductSunflowerChoice r k w} (hcd : choicePetals c = choicePetals d) :
    c = d := by
  apply Subtype.ext
  funext i
  let t₀ : Fin k := ⟨0, by omega⟩
  let t₁ : Fin k := ⟨1, by omega⟩
  have ht₀t₁ : t₀ ≠ t₁ := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hcoord : ∀ t : Fin k,
      coordinateChoiceTuple (c.1 i) t = coordinateChoiceTuple (d.1 i) t := by
    intro t
    have hp : choicePetals c t = choicePetals d t := congrFun hcd t
    exact congrFun (blockProductEdge_injective hp) i
  cases hc : c.1 i with
  | inl a =>
      cases hd : d.1 i with
      | inl b =>
          have hab : a = b := by
            simpa [hc, hd] using hcoord t₀
          simp [hab]
      | inr e =>
          have h0 : a = e t₀ := by simpa [hc, hd] using hcoord t₀
          have h1 : a = e t₁ := by simpa [hc, hd] using hcoord t₁
          exact False.elim (ht₀t₁ (e.injective (h0.symm.trans h1)))
  | inr e =>
      cases hd : d.1 i with
      | inl b =>
          have h0 : e t₀ = b := by simpa [hc, hd] using hcoord t₀
          have h1 : e t₁ = b := by simpa [hc, hd] using hcoord t₁
          exact False.elim (ht₀t₁ (e.injective (h0.trans h1.symm)))
      | inr f =>
          have hef : e = f := by
            ext t
            exact congrArg Fin.val (by simpa [hc, hd] using hcoord t)
          simp [hef]

/-- Ordered block-product sunflower petal functions have the same count as the coordinatewise
constant/injective choices. -/
theorem card_orderedBlockProductSunflowerPetals (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) :
    (orderedBlockProductSunflowerPetals r k w).card =
      (∏ i : Fin r, (w i + (w i).descFactorial k)) - blockProductCard r w := by
  classical
  unfold orderedBlockProductSunflowerPetals
  rw [Finset.card_image_of_injective]
  · exact card_blockProductSunflowerChoices r k w
  · intro c d hcd
    exact choicePetals_ext_of_eq hk hcd

theorem orderedBlockProductSunflowerPetals_mem_isSunflower {r k : ℕ} {w : Fin r → ℕ}
    {petals : Fin k → Finset (Sigma fun i : Fin r => Fin (w i))}
    (hpetals : petals ∈ orderedBlockProductSunflowerPetals r k w) :
    (∀ t, petals t ∈ exactBlockProductFamily r w) ∧
      Function.Injective petals ∧
      ∃ Y, ∀ t u, t ≠ u → petals t ∩ petals u = Y := by
  classical
  rcases Finset.mem_image.mp hpetals with ⟨c, -, rfl⟩
  exact ⟨fun t => blockProductEdge_mem_exactBlockProductFamily _,
    choicePetals_injective c, ⟨choiceKernel c.1, fun t u htu => choiceWord_inter c.1 htu⟩⟩

/-- The finset of actual ordered `k`-sunflower petal functions in the exact block product. -/
noncomputable def orderedExactBlockProductSunflowers (r k : ℕ) (w : Fin r → ℕ) :
    Finset (Fin k → Finset (Sigma fun i : Fin r => Fin (w i))) :=
  Finset.univ.filter fun petals =>
    (∀ t, petals t ∈ exactBlockProductFamily r w) ∧
      Function.Injective petals ∧
      ∃ Y, ∀ t u, t ≠ u → petals t ∩ petals u = Y

private theorem coordinate_constant_of_not_injective_of_sunflower {r k : ℕ}
    {w : Fin r → ℕ} {petals : Fin k → Finset (Sigma fun i : Fin r => Fin (w i))}
    {x : Fin k → BlockProductWord r w} {Y : Finset (Sigma fun i : Fin r => Fin (w i))}
    (hx : ∀ t, petals t = blockProductEdge (x t))
    (hSun : ∀ t u, t ≠ u → petals t ∩ petals u = Y)
    (t₀ : Fin k) (i : Fin r)
    (hnot : ¬ Function.Injective fun t => x t i) :
    ∀ t, x t i = x t₀ i := by
  classical
  rw [Function.Injective] at hnot
  push Not at hnot
  rcases hnot with ⟨u, v, huvEq, huvNe⟩
  have hmem_uv : Sigma.mk i (x u i) ∈ petals u ∩ petals v := by
    rw [hx u, hx v]
    simp [mem_blockProductEdge_iff, huvEq]
  have hall : ∀ s, x s i = x u i := by
    intro s
    by_cases hsu : s = u
    · subst hsu
      rfl
    · have hEqInter : petals u ∩ petals v = petals u ∩ petals s := by
        exact (hSun u v huvNe).trans (hSun u s (by intro h; exact hsu h.symm)).symm
      have hmem_us : Sigma.mk i (x u i) ∈ petals u ∩ petals s := by
        simpa [hEqInter] using hmem_uv
      rw [hx u, hx s] at hmem_us
      exact mem_blockProductEdge_iff.mp (Finset.mem_inter.mp hmem_us).2
  intro t
  exact (hall t).trans (hall t₀).symm

/-- The coordinatewise constant/injective construction is exactly the actual ordered sunflower
finset in the tagged singleton model. -/
theorem orderedBlockProductSunflowerPetals_eq_orderedExactBlockProductSunflowers
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) :
    orderedBlockProductSunflowerPetals r k w =
      orderedExactBlockProductSunflowers r k w := by
  classical
  ext petals
  constructor
  · intro hpetals
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, orderedBlockProductSunflowerPetals_mem_isSunflower hpetals⟩
  · intro hpetals
    rcases Finset.mem_filter.mp hpetals with ⟨-, hmem, hinj, Y, hSun⟩
    let t₀ : Fin k := ⟨0, by omega⟩
    let t₁ : Fin k := ⟨1, by omega⟩
    have ht₀t₁ : t₀ ≠ t₁ := by
      intro h
      have : (0 : ℕ) = 1 := congrArg Fin.val h
      omega
    have hx_exists : ∀ t : Fin k, ∃ x : BlockProductWord r w,
        petals t = blockProductEdge x := by
      intro t
      rcases Finset.mem_image.mp (hmem t) with ⟨x, -, hx⟩
      exact ⟨x, hx.symm⟩
    choose x hx using hx_exists
    have hconst :
        ∀ i : Fin r, (¬ Function.Injective fun t => x t i) → ∀ t, x t i = x t₀ i := by
      intro i hnot
      exact coordinate_constant_of_not_injective_of_sunflower hx hSun t₀ i hnot
    let cRaw : ∀ i : Fin r, BlockProductCoordinateChoice k (w i) := fun i =>
      if hi : Function.Injective fun t => x t i then
        Sum.inr ({ toFun := fun t => x t i, inj' := hi } : Fin k ↪ Fin (w i))
      else
        Sum.inl (x t₀ i)
    have hhasInjective :
        ∃ i : Fin r, ∃ e : Fin k ↪ Fin (w i), cRaw i = Sum.inr e := by
      by_contra hnone
      have hnotinj : ∀ i : Fin r, ¬ Function.Injective fun t => x t i := by
        intro i hi
        exact hnone ⟨i, { toFun := fun t => x t i, inj' := hi }, by simp [cRaw, hi]⟩
      have hword : x t₀ = x t₁ := by
        funext i
        exact (hconst i (hnotinj i) t₁).symm
      have hpetal : petals t₀ = petals t₁ := by
        rw [hx t₀, hx t₁, hword]
      exact ht₀t₁ (hinj hpetal)
    let c : BlockProductSunflowerChoice r k w := ⟨cRaw, hhasInjective⟩
    refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
    funext t
    rw [hx t]
    apply congrArg blockProductEdge
    funext i
    by_cases hi : Function.Injective fun t => x t i
    · simp [choiceWord, c, cRaw, hi]
    · simp [choiceWord, c, cRaw, hi, hconst i hi t]

/-- Exact ordered count of actual `k`-sunflowers in the tagged singleton block product. -/
theorem card_orderedExactBlockProductSunflowers
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) :
    (orderedExactBlockProductSunflowers r k w).card =
      (∏ i : Fin r, (w i + (w i).descFactorial k)) - blockProductCard r w := by
  rw [← orderedBlockProductSunflowerPetals_eq_orderedExactBlockProductSunflowers r k w hk]
  exact card_orderedBlockProductSunflowerPetals r k w hk

/-- Permuting the labels of an ordered sunflower keeps it in the ordered count. -/
theorem orderedBlockProductSunflowerPetals_perm_mem {r k : ℕ} {w : Fin r → ℕ}
    {petals : Fin k → Finset (Sigma fun i : Fin r => Fin (w i))}
    (hpetals : petals ∈ orderedBlockProductSunflowerPetals r k w)
    (σ : Equiv.Perm (Fin k)) :
    (fun t => petals (σ t)) ∈ orderedBlockProductSunflowerPetals r k w := by
  classical
  rcases Finset.mem_image.mp hpetals with ⟨c, -, rfl⟩
  let cσ : BlockProductSunflowerChoice r k w :=
    ⟨fun i =>
      match c.1 i with
      | Sum.inl a => Sum.inl a
      | Sum.inr e =>
          Sum.inr
            { toFun := fun t => e (σ t)
              inj' := fun t u htu => σ.injective (e.injective htu) },
      by
        rcases c.2 with ⟨i, e, hi⟩
        refine ⟨i,
          { toFun := fun t => e (σ t)
            inj' := fun t u htu => σ.injective (e.injective htu) }, ?_⟩
        simp [hi]⟩
  refine Finset.mem_image.mpr ⟨cσ, Finset.mem_univ _, ?_⟩
  funext t
  apply congrArg blockProductEdge
  funext i
  cases hc : c.1 i with
  | inl a =>
      simp [choiceWord, cσ, hc]
  | inr e =>
      simp [choiceWord, cσ, hc]

/-- The permutation action on an ordered sunflower is free: no nontrivial permutation fixes an
ordered petal function whose petals are distinct. -/
theorem orderedBlockProductSunflowerPetals_perm_fixed {r k : ℕ} {w : Fin r → ℕ}
    {petals : Fin k → Finset (Sigma fun i : Fin r => Fin (w i))}
    (hpetals : petals ∈ orderedBlockProductSunflowerPetals r k w)
    (σ : Equiv.Perm (Fin k)) (hfix : (fun t => petals (σ t)) = petals) :
    σ = 1 := by
  classical
  have hinj := (orderedBlockProductSunflowerPetals_mem_isSunflower hpetals).2.1
  ext t
  exact congrArg Fin.val (hinj (congrFun hfix t))

/-! ## Maximal subproducts and near-extremal stability -/

/-- Any positive-width sunflower-free subproduct of an ambient block product has size at most
the product obtained by truncating each ambient width at `k - 1`. -/
theorem blockProductCard_le_truncated_of_sunflowerFree_subproduct
    (r k : ℕ) (w v : Fin r → ℕ) (hk : 2 ≤ k)
    (hsub : ∀ i, v i ≤ w i) (hpos : ∀ i, 0 < v i)
    (hfree : SunflowerFree (exactBlockProductFamily r v) k) :
    blockProductCard r v ≤ blockProductCard r (fun i => min (w i) (k - 1)) := by
  classical
  have hv : ∀ i, v i ≤ min (w i) (k - 1) := by
    intro i
    exact le_min (hsub i)
      ((width_le_of_exactBlockProductFamily_sunflowerFree r k v hk hpos hfree) i)
  unfold blockProductCard
  exact Finset.prod_le_prod' fun i _ => hv i

theorem truncatedBlockProduct_sunflowerFree
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) :
    SunflowerFree (exactBlockProductFamily r (fun i => min (w i) (k - 1))) k := by
  exact exactBlockProductFamily_sunflowerFree_of_width_le r k
    (fun i => min (w i) (k - 1)) hk (fun i => min_le_right _ _)

/-- The truncated subproduct is an exact maximum among positive-width sunflower-free
subproducts of the ambient product. -/
theorem truncatedBlockProduct_is_maximal_subproduct
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k) :
    (∀ v : Fin r → ℕ,
        (∀ i, v i ≤ w i) →
        (∀ i, 0 < v i) →
        SunflowerFree (exactBlockProductFamily r v) k →
        blockProductCard r v ≤ blockProductCard r (fun i => min (w i) (k - 1))) ∧
      SunflowerFree (exactBlockProductFamily r (fun i => min (w i) (k - 1))) k ∧
      (∀ i, min (w i) (k - 1) ≤ w i) := by
  refine ⟨?_, truncatedBlockProduct_sunflowerFree r k w hk, fun i => min_le_left _ _⟩
  intro v hsub hpos hfree
  exact blockProductCard_le_truncated_of_sunflowerFree_subproduct r k w v hk hsub hpos hfree

private theorem deficientCoordinateCount_le (r k : ℕ) (w : Fin r → ℕ) :
    deficientCoordinateCount r k w ≤ r := by
  classical
  unfold deficientCoordinateCount
  simpa using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin r))) (p := fun i => w i ≤ k - 2))

private theorem stability_profile_le_one_defect
    (r k d : ℕ) (hk : 2 ≤ k) (hdpos : 0 < d) (hdle : d ≤ r) :
    (k - 2) ^ d * (k - 1) ^ (r - d) ≤ (k - 2) * (k - 1) ^ (r - 1) := by
  have hbase : k - 2 ≤ k - 1 := by omega
  have hpow : (k - 2) ^ d = (k - 2) * (k - 2) ^ (d - 1) := by
    cases d with
    | zero => omega
    | succ d =>
        simp [pow_succ']
  calc
    (k - 2) ^ d * (k - 1) ^ (r - d)
        = ((k - 2) * (k - 2) ^ (d - 1)) * (k - 1) ^ (r - d) := by
          rw [hpow]
    _ ≤ ((k - 2) * (k - 1) ^ (d - 1)) * (k - 1) ^ (r - d) := by
          exact Nat.mul_le_mul_right _ <|
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (k - 2) * ((k - 1) ^ (d - 1) * (k - 1) ^ (r - d)) := by
          rw [Nat.mul_assoc]
    _ = (k - 2) * (k - 1) ^ (r - 1) := by
          rw [← pow_add]
          have hexp : d - 1 + (r - d) = r - 1 := by omega
          rw [hexp]

/-- Numeric near-extremal stability: once at least one coordinate is deficient
(`wᵢ ≤ k - 2`), a sunflower-free product loses at least one factor from the extremal
`(k - 1)^r` profile. -/
theorem blockProductCard_le_one_defect_of_deficient
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k)
    (hfree : ∀ i, w i ≤ k - 1)
    (hdef : 0 < deficientCoordinateCount r k w) :
    blockProductCard r w ≤ (k - 2) * (k - 1) ^ (r - 1) := by
  have hprofile := blockProductCard_le_stability_profile r k w hfree
  exact hprofile.trans
    (stability_profile_le_one_defect r k (deficientCoordinateCount r k w) hk hdef
      (deficientCoordinateCount_le r k w))

theorem deficientCoordinateCount_pos_of_width_le
    {r k : ℕ} {w : Fin r → ℕ} {i : Fin r} (hi : w i ≤ k - 2) :
    0 < deficientCoordinateCount r k w := by
  classical
  unfold deficientCoordinateCount
  exact Finset.card_pos.mpr
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- If a sunflower-free exact block product is larger than the one-defect threshold, every
coordinate has the extremal width `k - 1`. -/
theorem widths_eq_pred_of_near_extremal
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k)
    (hfree : ∀ i, w i ≤ k - 1)
    (hlarge : (k - 2) * (k - 1) ^ (r - 1) < blockProductCard r w) :
    ∀ i, w i = k - 1 := by
  intro i
  by_contra hne
  have hlt : w i < k - 1 := lt_of_le_of_ne (hfree i) hne
  have hle : w i ≤ k - 2 := by omega
  have hdef := deficientCoordinateCount_pos_of_width_le (r := r) (k := k) (w := w) (i := i) hle
  have hupper := blockProductCard_le_one_defect_of_deficient r k w hk hfree hdef
  omega

theorem blockProductCard_eq_extremal_of_near_extremal
    (r k : ℕ) (w : Fin r → ℕ) (hk : 2 ≤ k)
    (hfree : ∀ i, w i ≤ k - 1)
    (hlarge : (k - 2) * (k - 1) ^ (r - 1) < blockProductCard r w) :
    blockProductCard r w = (k - 1) ^ r := by
  classical
  unfold blockProductCard
  calc
    (∏ i : Fin r, w i) = ∏ _i : Fin r, (k - 1) := by
      apply Finset.prod_congr rfl
      intro i _
      exact widths_eq_pred_of_near_extremal r k w hk hfree hlarge i
    _ = (k - 1) ^ r := by
      simp

end FormalConjectures.Problems.Erdos.E20.Compendium
