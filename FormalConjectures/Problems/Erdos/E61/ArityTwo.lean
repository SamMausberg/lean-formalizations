import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Arity-two shadow realization

This file formalizes the realization half of `prop:arity-two`: arbitrary
prescribed two-bit data on pairs `(u_i,v_i)` versus vertices `y_j` can be
realized by an explicit finite simple graph.
-/

namespace Erdos61

variable {I J : Type*}

/-- Vertex model with a pair `(u_i,v_i)` for every `i` and a vertex `y_j` for every `j`. -/
abbrev PairMatrixVertex (I J : Type*) := Sum (I × Bool) J

def pairMatrixRel (μ : I → J → Bool × Bool) :
    PairMatrixVertex I J → PairMatrixVertex I J → Prop
  | Sum.inl (i, false), Sum.inr j => (μ i j).1 = true
  | Sum.inl (i, true), Sum.inr j => (μ i j).2 = true
  | _, _ => False

/-- The graph realizing the prescribed two-bit matrix `μ`. -/
def pairMatrixGraph (μ : I → J → Bool × Bool) : SimpleGraph (PairMatrixVertex I J) :=
  SimpleGraph.fromRel (pairMatrixRel μ)

@[simp] lemma pairMatrixRel_y_left (μ : I → J → Bool × Bool) (j : J) (x : I × Bool) :
    pairMatrixRel μ (Sum.inr j) (Sum.inl x) = False := by
  cases x
  rfl

@[simp] lemma pairMatrixRel_u_y (μ : I → J → Bool × Bool) (i : I) (j : J) :
    pairMatrixRel μ (Sum.inl (i, false)) (Sum.inr j) ↔ (μ i j).1 = true := by
  rfl

@[simp] lemma pairMatrixRel_v_y (μ : I → J → Bool × Bool) (i : I) (j : J) :
    pairMatrixRel μ (Sum.inl (i, true)) (Sum.inr j) ↔ (μ i j).2 = true := by
  rfl

/-- The first coordinate of `μ(i,j)` is exactly the adjacency of `u_i` to `y_j`. -/
theorem pairMatrixGraph_u_y (μ : I → J → Bool × Bool) (i : I) (j : J) :
    (pairMatrixGraph μ).Adj (Sum.inl (i, false)) (Sum.inr j) ↔ (μ i j).1 = true := by
  simp [pairMatrixGraph, pairMatrixRel]

/-- The second coordinate of `μ(i,j)` is exactly the adjacency of `v_i` to `y_j`. -/
theorem pairMatrixGraph_v_y (μ : I → J → Bool × Bool) (i : I) (j : J) :
    (pairMatrixGraph μ).Adj (Sum.inl (i, true)) (Sum.inr j) ↔ (μ i j).2 = true := by
  simp [pairMatrixGraph, pairMatrixRel]

/-- The realized lambda value is the prescribed matrix entry. -/
theorem pairMatrixGraph_lambda (μ : I → J → Bool × Bool) (i : I) (j : J) :
    (((pairMatrixGraph μ).Adj (Sum.inl (i, false)) (Sum.inr j)),
      ((pairMatrixGraph μ).Adj (Sum.inl (i, true)) (Sum.inr j))) =
      ((μ i j).1 = true, (μ i j).2 = true) := by
  simp [pairMatrixGraph_u_y, pairMatrixGraph_v_y]

section PullbackLineCases

open Finset

variable {α β : Type*}

/--
Counting projection to the first coordinate of an ordered pair set.  This is
the finite `|A| / |G|` lower-bound ingredient used in the coordinate-line
cases of `prop:arity-two`, stated multiplicatively.
-/
theorem pair_first_image_count [Fintype α] [DecidableEq α]
    (A : Finset (α × α)) :
    A.card ≤ Fintype.card α * (A.image Prod.fst).card := by
  classical
  rw [card_eq_sum_card_fiberOver_image A Prod.fst]
  calc
    (∑ y ∈ A.image Prod.fst, (fiberOver A Prod.fst y).card) ≤
        ∑ _y ∈ A.image Prod.fst, Fintype.card α := by
      refine sum_le_sum ?_
      intro y _hy
      exact card_le_card_of_injOn Prod.snd
        (by intro p _hp; exact mem_univ (Prod.snd p))
        (by
          intro p hp q hq hsq
          have hpf : p.1 = y := (mem_fiberOver_iff.mp hp).2
          have hqf : q.1 = y := (mem_fiberOver_iff.mp hq).2
          cases p with
          | mk _ _ =>
              cases q with
              | mk _ _ =>
                  simp only [Prod.mk.injEq] at hpf hqf hsq ⊢
                  exact ⟨hpf.trans hqf.symm, hsq⟩)
    _ = (A.image Prod.fst).card * Fintype.card α := by simp
    _ = Fintype.card α * (A.image Prod.fst).card := by rw [Nat.mul_comm]

/-- The symmetric counting projection to the second coordinate. -/
theorem pair_second_image_count [Fintype α] [DecidableEq α]
    (A : Finset (α × α)) :
    A.card ≤ Fintype.card α * (A.image Prod.snd).card := by
  classical
  rw [card_eq_sum_card_fiberOver_image A Prod.snd]
  calc
    (∑ y ∈ A.image Prod.snd, (fiberOver A Prod.snd y).card) ≤
        ∑ _y ∈ A.image Prod.snd, Fintype.card α := by
      refine sum_le_sum ?_
      intro y _hy
      exact card_le_card_of_injOn Prod.fst
        (by intro p _hp; exact mem_univ (Prod.fst p))
        (by
          intro p hp q hq hfq
          have hps : p.2 = y := (mem_fiberOver_iff.mp hp).2
          have hqs : q.2 = y := (mem_fiberOver_iff.mp hq).2
          cases p with
          | mk _ _ =>
              cases q with
              | mk _ _ =>
                  simp only [Prod.mk.injEq] at hps hqs hfq ⊢
                  exact ⟨hfq, hps.trans hqs.symm⟩)
    _ = (A.image Prod.snd).card * Fintype.card α := by simp
    _ = Fintype.card α * (A.image Prod.snd).card := by rw [Nat.mul_comm]

/--
Coordinate-line pullback, first-coordinate case.

If every pair in `A` has first coordinate adjacency constantly `c` to all
vertices of `Y`, then the first-coordinate projection has the expected
multiplicative size lower bound and is complete or anticomplete to `Y`.
-/
theorem arity_two_first_coordinate_pullback [Fintype α] [DecidableEq α]
    (R : α → β → Bool) (A : Finset (α × α)) (Y : Finset β) (c : Bool)
    (hconst : ∀ p ∈ A, ∀ y ∈ Y, R p.1 y = c) :
    A.card ≤ Fintype.card α * (A.image Prod.fst).card ∧
      (if c then CompleteTo (fun x y => R x y = true) (A.image Prod.fst) Y
       else Anticomplete (fun x y => R x y = true) (A.image Prod.fst) Y) := by
  constructor
  · exact pair_first_image_count A
  · cases c
    · intro x hx y hy hxy
      rcases mem_image.mp hx with ⟨p, hpA, rfl⟩
      have hfalse : R p.1 y = false := by simpa using hconst p hpA y hy
      rw [hfalse] at hxy
      exact Bool.noConfusion hxy
    · intro x hx y hy
      rcases mem_image.mp hx with ⟨p, hpA, rfl⟩
      simpa using hconst p hpA y hy

/-- Coordinate-line pullback, second-coordinate case. -/
theorem arity_two_second_coordinate_pullback [Fintype α] [DecidableEq α]
    (R : α → β → Bool) (A : Finset (α × α)) (Y : Finset β) (c : Bool)
    (hconst : ∀ p ∈ A, ∀ y ∈ Y, R p.2 y = c) :
    A.card ≤ Fintype.card α * (A.image Prod.snd).card ∧
      (if c then CompleteTo (fun x y => R x y = true) (A.image Prod.snd) Y
       else Anticomplete (fun x y => R x y = true) (A.image Prod.snd) Y) := by
  constructor
  · exact pair_second_image_count A
  · cases c
    · intro x hx y hy hxy
      rcases mem_image.mp hx with ⟨p, hpA, rfl⟩
      have hfalse : R p.2 y = false := by simpa using hconst p hpA y hy
      rw [hfalse] at hxy
      exact Bool.noConfusion hxy
    · intro x hx y hy
      rcases mem_image.mp hx with ⟨p, hpA, rfl⟩
      simpa using hconst p hpA y hy

end PullbackLineCases

section TraceClassCases

open Finset

variable {α β : Type*}

/--
Inside one exact trace class, either the common trace on `Y` or its complement
has at least half of `Y`, giving a complete or anticomplete pair.  This is the
checked finite core used in the `x₁ + x₂ = c` affine-line cases of
`prop:arity-two`.
-/
theorem trace_class_half_complete_or_anticomplete
    [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (S : Finset α) (Y T : Finset β)
    (hTY : T ⊆ Y)
    (htrace : ∀ x ∈ S, traceFinset R Y x = T) :
    ∃ U : Finset β, U ⊆ Y ∧ Y.card ≤ 2 * U.card ∧
      (CompleteTo R S U ∨ Anticomplete R S U) := by
  classical
  by_cases hhalf : Y.card ≤ 2 * T.card
  · refine ⟨T, hTY, hhalf, Or.inl ?_⟩
    intro x hx y hy
    have hytrace : y ∈ traceFinset R Y x := by
      rw [htrace x hx]
      exact hy
    exact (mem_filter.mp hytrace).2
  · let U : Finset β := Y \ T
    have hUsub : U ⊆ Y := by
      intro y hy
      exact (mem_sdiff.mp hy).1
    have hcard_split : U.card + T.card = Y.card := by
      simpa [U] using card_sdiff_add_card_eq_card hTY
    have hUlarge : Y.card ≤ 2 * U.card := by
      have hTsmall : 2 * T.card < Y.card := Nat.lt_of_not_ge hhalf
      omega
    refine ⟨U, hUsub, hUlarge, Or.inr ?_⟩
    intro x hx y hy hxy
    have hyY : y ∈ Y := (mem_sdiff.mp hy).1
    have hyT : y ∉ T := (mem_sdiff.mp hy).2
    have hytrace : y ∈ traceFinset R Y x := mem_filter.mpr ⟨hyY, hxy⟩
    rw [htrace x hx] at hytrace
    exact hyT hytrace

end TraceClassCases

end Erdos61
