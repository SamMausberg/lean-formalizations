import FormalConjectures.Problems.Erdos.E61.ArityTwo

/-!
# Full arity-two pullback packaging

This file packages the checked coordinate and parity line arguments behind
`prop:arity-two` from `eh_forum_trimmed_v9.tex`.
-/

namespace Erdos61

open Finset

variable {α β : Type*}

/-- The three affine-line directions in `Bool × Bool = F₂²`. -/
inductive BoolAffineLine where
  | first : Bool → BoolAffineLine
  | second : Bool → BoolAffineLine
  | parity : Bool → BoolAffineLine
  deriving DecidableEq

namespace BoolAffineLine

/-- Membership in one of the six affine lines of `F₂²`. -/
def Contains : BoolAffineLine → Bool × Bool → Prop
  | first c, p => p.1 = c
  | second c, p => p.2 = c
  | parity c, p => (p.1 != p.2) = c

instance (L : BoolAffineLine) (p : Bool × Bool) : Decidable (L.Contains p) := by
  cases L <;> dsimp [Contains] <;> infer_instance

end BoolAffineLine

/--
If the second endpoint of every pair in `A` lies in the class prescribed by the
first endpoint, some prescribed class has multiplicative size at least
`|A| / |α|`.
-/
theorem exists_large_second_class
    [Fintype α] [DecidableEq τ] [Nonempty α]
    (A : Finset (α × α)) (f target : α → τ)
    (hpair : ∀ p ∈ A, f p.2 = target p.1) :
    ∃ x₀ : α,
      A.card ≤ Fintype.card α *
        ((Finset.univ : Finset α).filter fun x => f x = target x₀).card := by
  classical
  let cls : τ → Finset α := fun t =>
    (Finset.univ : Finset α).filter fun x => f x = t
  let w : α → ℕ := fun x => (cls (target x)).card
  have hfiber : ∀ x ∈ A.image Prod.fst, (fiberOver A Prod.fst x).card ≤ w x := by
    intro x hx
    refine card_le_card_of_injOn Prod.snd ?_ ?_
    · intro p hp
      have hpA : p ∈ A := (mem_fiberOver_iff.mp hp).1
      have hxeq : p.1 = x := (mem_fiberOver_iff.mp hp).2
      exact mem_filter.mpr ⟨mem_univ p.2, by
        exact (hpair p hpA).trans (congrArg target hxeq)⟩
    · intro p hp q hq hsnd
      have hpf : p.1 = x := (mem_fiberOver_iff.mp hp).2
      have hqf : q.1 = x := (mem_fiberOver_iff.mp hq).2
      exact Prod.ext (hpf.trans hqf.symm) hsnd
  have hcard_sum :
      A.card ≤ ∑ x ∈ A.image Prod.fst, w x := by
    rw [card_eq_sum_card_fiberOver_image A Prod.fst]
    exact sum_le_sum hfiber
  obtain ⟨x₀, _hx₀, hx₀max⟩ :=
    exists_max_image (Finset.univ : Finset α) w (Finset.univ_nonempty)
  refine ⟨x₀, ?_⟩
  calc
    A.card ≤ ∑ x ∈ A.image Prod.fst, w x := hcard_sum
    _ ≤ ∑ _x ∈ A.image Prod.fst, w x₀ := by
      refine sum_le_sum ?_
      intro x hx
      exact hx₀max x (mem_univ x)
    _ = (A.image Prod.fst).card * w x₀ := by simp
    _ ≤ Fintype.card α * w x₀ := by
      exact Nat.mul_le_mul_right _ (card_le_univ (A.image Prod.fst))
    _ = Fintype.card α *
        ((Finset.univ : Finset α).filter fun x => f x = target x₀).card := rfl

/-- Parity-line pullback for the line `x₁ + x₂ = 0`. -/
theorem arity_two_equal_trace_pullback
    [Fintype α]
    (R : α → β → Prop)
    (A : Finset (α × α)) (Y : Finset β)
    (hsame : ∀ p ∈ A, ∀ y ∈ Y, (R p.1 y ↔ R p.2 y)) :
    ∃ S : Finset α, ∃ U : Finset β,
      A.card ≤ Fintype.card α * S.card ∧
        U ⊆ Y ∧ Y.card ≤ 2 * U.card ∧
          (CompleteTo R S U ∨ Anticomplete R S U) := by
  classical
  by_cases hα : Nonempty α
  · letI : Nonempty α := hα
    let f : α → Finset β := traceFinset R Y
    have hpair : ∀ p ∈ A, f p.2 = f p.1 := by
      intro p hp
      ext y
      constructor
      · intro hy
        have hyY : y ∈ Y := (mem_filter.mp hy).1
        have hRy : R p.2 y := (mem_filter.mp hy).2
        exact mem_filter.mpr ⟨hyY, (hsame p hp y hyY).mpr hRy⟩
      · intro hy
        have hyY : y ∈ Y := (mem_filter.mp hy).1
        have hRy : R p.1 y := (mem_filter.mp hy).2
        exact mem_filter.mpr ⟨hyY, (hsame p hp y hyY).mp hRy⟩
    rcases exists_large_second_class A f f hpair with ⟨x₀, hlarge⟩
    let T : Finset β := f x₀
    let S : Finset α := (Finset.univ : Finset α).filter fun x => f x = T
    have htrace : ∀ x ∈ S, traceFinset R Y x = T := by
      intro x hx
      exact (mem_filter.mp hx).2
    have hTY : T ⊆ Y := by
      intro y hy
      exact (mem_filter.mp hy).1
    rcases trace_class_half_complete_or_anticomplete R S Y T hTY htrace with
      ⟨U, hUY, hUlarge, hpure⟩
    exact ⟨S, U, hlarge, hUY, hUlarge, hpure⟩
  · have hAempty : A = ∅ := by
      ext p
      constructor
      · intro _hp
        exact False.elim (hα ⟨p.1⟩)
      · intro hp
        simp at hp
    refine ⟨∅, Y, ?_, subset_rfl, by omega, Or.inl ?_⟩
    · simp [hAempty]
    · intro x hx _y _hy
      simp at hx

/-- Parity-line pullback for the line `x₁ + x₂ = 1`. -/
theorem arity_two_complement_trace_pullback
    [Fintype α]
    (R : α → β → Prop)
    (A : Finset (α × α)) (Y : Finset β)
    (hcomp : ∀ p ∈ A, ∀ y ∈ Y, (R p.1 y ↔ ¬ R p.2 y)) :
    ∃ S : Finset α, ∃ U : Finset β,
      A.card ≤ Fintype.card α * S.card ∧
        U ⊆ Y ∧ Y.card ≤ 2 * U.card ∧
          (CompleteTo R S U ∨ Anticomplete R S U) := by
  classical
  by_cases hα : Nonempty α
  · letI : Nonempty α := hα
    let f : α → Finset β := traceFinset R Y
    let target : α → Finset β := fun x => Y \ f x
    have hpair : ∀ p ∈ A, f p.2 = target p.1 := by
      intro p hp
      ext y
      constructor
      · intro hy
        have hyY : y ∈ Y := (mem_filter.mp hy).1
        have hR2 : R p.2 y := (mem_filter.mp hy).2
        refine mem_sdiff.mpr ⟨hyY, ?_⟩
        intro hyf
        have hR1 : R p.1 y := (mem_filter.mp hyf).2
        exact ((hcomp p hp y hyY).mp hR1) hR2
      · intro hy
        have hyY : y ∈ Y := (mem_sdiff.mp hy).1
        have hynot : y ∉ f p.1 := (mem_sdiff.mp hy).2
        refine mem_filter.mpr ⟨hyY, ?_⟩
        by_contra hR2
        have hR1 : R p.1 y := (hcomp p hp y hyY).mpr hR2
        exact hynot (mem_filter.mpr ⟨hyY, hR1⟩)
    rcases exists_large_second_class A f target hpair with ⟨x₀, hlarge⟩
    let T : Finset β := target x₀
    let S : Finset α := (Finset.univ : Finset α).filter fun x => f x = T
    have htrace : ∀ x ∈ S, traceFinset R Y x = T := by
      intro x hx
      exact (mem_filter.mp hx).2
    have hTY : T ⊆ Y := by
      intro y hy
      exact (mem_sdiff.mp hy).1
    rcases trace_class_half_complete_or_anticomplete R S Y T hTY htrace with
      ⟨U, hUY, hUlarge, hpure⟩
    exact ⟨S, U, hlarge, hUY, hUlarge, hpure⟩
  · have hAempty : A = ∅ := by
      ext p
      constructor
      · intro _hp
        exact False.elim (hα ⟨p.1⟩)
      · intro hp
        simp at hp
    refine ⟨∅, Y, ?_, subset_rfl, by omega, Or.inl ?_⟩
    · simp [hAempty]
    · intro x hx _y _hy
      simp at hx

/--
Full affine-line pullback packaging for `prop:arity-two(a)`.

The size lower bounds are stated multiplicatively:
`A.card ≤ |α| * S.card` and `Y.card ≤ 2 * U.card`.
-/
theorem arity_two_affine_line_pullback
    [Fintype α]
    (R : α → β → Bool)
    (A : Finset (α × α)) (Y : Finset β) (L : BoolAffineLine)
    (hline : ∀ p ∈ A, ∀ y ∈ Y, L.Contains (R p.1 y, R p.2 y)) :
    ∃ S : Finset α, ∃ U : Finset β,
      A.card ≤ Fintype.card α * S.card ∧
        U ⊆ Y ∧ Y.card ≤ 2 * U.card ∧
          (CompleteTo (fun x y => R x y = true) S U ∨
            Anticomplete (fun x y => R x y = true) S U) := by
  classical
  cases L with
  | first c =>
      rcases arity_two_first_coordinate_pullback R A Y c
          (by intro p hp y hy; exact hline p hp y hy) with ⟨hsize, hpure⟩
      refine ⟨A.image Prod.fst, Y, hsize, subset_rfl, by omega, ?_⟩
      cases c
      · exact Or.inr hpure
      · exact Or.inl hpure
  | second c =>
      rcases arity_two_second_coordinate_pullback R A Y c
          (by intro p hp y hy; exact hline p hp y hy) with ⟨hsize, hpure⟩
      refine ⟨A.image Prod.snd, Y, hsize, subset_rfl, by omega, ?_⟩
      cases c
      · exact Or.inr hpure
      · exact Or.inl hpure
  | parity c =>
      cases c
      · exact arity_two_equal_trace_pullback (fun x y => R x y = true) A Y (by
          intro p hp y hy
          have hxor := hline p hp y hy
          cases h₁ : R p.1 y <;> cases h₂ : R p.2 y <;>
            simp [BoolAffineLine.Contains, h₁, h₂] at hxor ⊢)
      · exact arity_two_complement_trace_pullback (fun x y => R x y = true) A Y (by
          intro p hp y hy
          have hxor := hline p hp y hy
          cases h₁ : R p.1 y <;> cases h₂ : R p.2 y <;>
            simp [BoolAffineLine.Contains, h₁, h₂] at hxor ⊢)

/--
Universality half of `prop:arity-two(b)`: arbitrary prescribed two-bit data is
realized by the explicit pair-matrix graph, so in particular any co-point-valued
matrix is realized.
-/
theorem arity_two_universality
    {I J : Type*} (C : Set (Bool × Bool)) (μ : I → J → Bool × Bool)
    (_hμ : ∀ i j, μ i j ∈ C) :
    ∀ i j,
      ((pairMatrixGraph μ).Adj (Sum.inl (i, false)) (Sum.inr j) ↔
          (μ i j).1 = true) ∧
        ((pairMatrixGraph μ).Adj (Sum.inl (i, true)) (Sum.inr j) ↔
          (μ i j).2 = true) := by
  intro i j
  exact ⟨pairMatrixGraph_u_y μ i j, pairMatrixGraph_v_y μ i j⟩

end Erdos61
