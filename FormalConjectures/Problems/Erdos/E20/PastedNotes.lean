import Mathlib
import FormalConjectures.Problems.Erdos.E20.Kernels.BridgeLock
import FormalConjectures.Problems.Erdos.E20.Recurrences.OneCounterHolonomy
import FormalConjectures.Problems.Erdos.E20.Tensors.ApolarRigidity

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false

open scoped BigOperators Classical

namespace FormalConjectures.Problems.Erdos.E20
namespace PastedNotes

/-!
# Formal interfaces for the pasted E20 notes

This file records the exact Lean content of the pasted E20 follow-up notes.  It deliberately
separates formal consequences from missing mathematical inputs:

* a statement from the notes that is still a genuine gap is represented as a field of a structure
  or an explicit theorem hypothesis;
* theorems in this file prove only the logical, finite, algebraic, or order-theoretic consequences
  of those hypotheses.

Every declaration is either proved directly or records an explicit assumption as a structure field.
-/

section TerminalPruning

variable {Obj Piece : Type*}

/-- Minimal unresolved exact-support descendants are terminal, provided every nonterminal
unresolved object has a strictly lower-complexity unresolved child. -/
theorem exists_terminal_minimal_unresolved
    (complexity : Obj → ℕ) (Unresolved Terminal : Obj → Prop) (child : Obj → Obj → Prop)
    (hmin : ∃ X, Unresolved X ∧ ∀ Y, Unresolved Y → complexity X ≤ complexity Y)
    (hchild_lt : ∀ {X Y}, child X Y → complexity Y < complexity X)
    (hnonterminal_child : ∀ X, Unresolved X → ¬ Terminal X → ∃ Y, child X Y ∧ Unresolved Y) :
    ∃ X, Unresolved X ∧ Terminal X := by
  rcases hmin with ⟨X, hX, hminimal⟩
  by_cases hterm : Terminal X
  · exact ⟨X, hX, hterm⟩
  · rcases hnonterminal_child X hX hterm with ⟨Y, hXY, hY⟩
    have hle : complexity X ≤ complexity Y := hminimal Y hY
    have hlt : complexity Y < complexity X := hchild_lt hXY
    exact (Nat.not_lt_of_ge hle hlt).elim

/-- The local hereditary-failure exactification package from `Pasted markdown (21).md`.

The field `local_exactification` is the explicit missing lemma from the note.  Downstream
statements may use it as an assumption, but this structure does not pretend to prove it. -/
structure HereditaryFailureExactification (Obj Piece : Type*) where
  SupportIrreducible : Obj → Prop
  LowCoherence : Obj → Prop
  Neutral : Obj → Prop
  UnresolvedTerminal : Obj → Prop
  ProperPiece : Obj → Piece → Prop
  HereditarilyFaithfulTrace : Obj → Piece → Prop
  StrictUnresolvedDescendantInside : Obj → Piece → Obj → Prop
  local_exactification :
    ∀ {X P},
      SupportIrreducible X →
      LowCoherence X →
      Neutral X →
      UnresolvedTerminal X →
      ProperPiece X P →
      ¬ HereditarilyFaithfulTrace X P →
      ∃ Y, StrictUnresolvedDescendantInside X P Y

namespace HereditaryFailureExactification

variable (E : HereditaryFailureExactification Obj Piece)

/-- Once the local exactification lemma is assumed, a minimal unresolved terminal has no proper
non-hereditarily-faithful trace. -/
theorem faithful_on_proper_pieces_of_minimal
    {X : Obj}
    (hsi : E.SupportIrreducible X) (hlc : E.LowCoherence X) (hneut : E.Neutral X)
    (hterm : E.UnresolvedTerminal X)
    (hminimal : ∀ {P Y}, E.ProperPiece X P → E.StrictUnresolvedDescendantInside X P Y → False) :
    ∀ P, E.ProperPiece X P → E.HereditarilyFaithfulTrace X P := by
  intro P hP
  by_contra hbad
  rcases E.local_exactification hsi hlc hneut hterm hP hbad with ⟨Y, hY⟩
  exact hminimal hP hY

/-- If every root hereditary failure appears on a proper piece, the local exactification lemma
turns minimality into root hereditary faithfulness. -/
theorem root_faithful_of_first_failure_below
    {RootFaithful : Obj → Prop} {X : Obj}
    (hsi : E.SupportIrreducible X) (hlc : E.LowCoherence X) (hneut : E.Neutral X)
    (hterm : E.UnresolvedTerminal X)
    (hminimal : ∀ {P Y}, E.ProperPiece X P → E.StrictUnresolvedDescendantInside X P Y → False)
    (hfirst :
      ¬ RootFaithful X → ∃ P, E.ProperPiece X P ∧ ¬ E.HereditarilyFaithfulTrace X P) :
    RootFaithful X := by
  by_contra hroot
  rcases hfirst hroot with ⟨P, hP, hbad⟩
  have hfaith := E.faithful_on_proper_pieces_of_minimal hsi hlc hneut hterm hminimal P hP
  exact hbad hfaith

end HereditaryFailureExactification

/-- Defect localization is the sharper form suggested in `Pasted markdown (21).md`. -/
structure DefectLocalization (Obj Piece : Type*) where
  Terminal : Obj → Prop
  ProperPiece : Obj → Piece → Prop
  Faithful : Obj → Piece → Prop
  defect : Obj → Piece → ℕ
  ChildWithPositiveDefect : Obj → Piece → Obj → Prop
  positive_defect_of_unfaithful :
    ∀ {X P}, Terminal X → ProperPiece X P → ¬ Faithful X P → 0 < defect X P
  localizes :
    ∀ {X P}, Terminal X → ProperPiece X P → 0 < defect X P →
      ∃ Y, ChildWithPositiveDefect X P Y

namespace DefectLocalization

variable (D : DefectLocalization Obj Piece)

/-- The defect-localization package implies the weaker local exactification conclusion. -/
theorem child_of_unfaithful {X : Obj} {P : Piece}
    (hterm : D.Terminal X) (hP : D.ProperPiece X P) (hbad : ¬ D.Faithful X P) :
    ∃ Y, D.ChildWithPositiveDefect X P Y := by
  exact D.localizes hterm hP (D.positive_defect_of_unfaithful hterm hP hbad)

end DefectLocalization

end TerminalPruning

section ChildGluing

variable {Parent : Type*}

/-- The precise closure assumption isolated in `Pasted markdown (8) (3).md`: compatible resolved
children glue to a resolved parent. -/
structure ChildGluingClosure (Parent : Type*) where
  HasCompatibleResolvedChildren : Parent → Prop
  ParentResolved : Parent → Prop
  closes : ∀ P, HasCompatibleResolvedChildren P → ParentResolved P

namespace ChildGluingClosure

variable (G : ChildGluingClosure Parent)

/-- A minimal unresolved parent cannot have a compatible family of resolved sibling children. -/
theorem unresolved_excludes_compatible_children {P : Parent}
    (hP : ¬ G.ParentResolved P) :
    ¬ G.HasCompatibleResolvedChildren P := by
  intro hchildren
  exact hP (G.closes P hchildren)

end ChildGluingClosure

end ChildGluing

section RouteAutomata

variable {Prefix Suffix Profile Route Realization : Type*}

/-- Finite continuation memory for one exact bridge class.  The profile set is intended to be
finite in applications, but the core implication does not need to inspect that finiteness. -/
structure FiniteContinuationMemory (Prefix Suffix Profile : Type*) where
  profile : Prefix → Profile
  feasibleSuffix : Prefix → Suffix → Prop
  same_profile :
    ∀ {ρ ρ'}, profile ρ = profile ρ' →
      ∀ η, feasibleSuffix ρ η ↔ feasibleSuffix ρ' η

namespace FiniteContinuationMemory

variable (M : FiniteContinuationMemory Prefix Suffix Profile)

/-- Prefixes with the same exact terminal profile have identical continuation languages. -/
theorem same_continuation_language {ρ ρ' : Prefix} (h : M.profile ρ = M.profile ρ') :
    ∀ η, M.feasibleSuffix ρ η ↔ M.feasibleSuffix ρ' η :=
  M.same_profile h

end FiniteContinuationMemory

/-- The exact route-disjointness semantics from the route-automaton notes. -/
structure ExactRouteDisjointness (Route Realization : Type*) where
  routeOf : Realization → Route
  EdgeDisjoint : Route → Route → Prop
  Sunflower : List Realization → Prop
  pairwise_route_disjoint_forces_sunflower :
    ∀ L : List Realization,
      (∀ A ∈ L, True) →
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → EdgeDisjoint (routeOf A) (routeOf B)) →
      Sunflower L

namespace ExactRouteDisjointness

variable (R : ExactRouteDisjointness Route Realization)

/-- In an exact bridge class, sunflower-freeness rules out `k` route-disjoint realizations. -/
theorem no_route_disjoint_family_of_sunflower_free
    {L : List Realization}
    (hfree : ¬ R.Sunflower L) :
    ¬ (∀ A ∈ L, ∀ B ∈ L, A ≠ B → R.EdgeDisjoint (R.routeOf A) (R.routeOf B)) := by
  intro hdis
  exact hfree (R.pairwise_route_disjoint_forces_sunflower L (by simp) hdis)

end ExactRouteDisjointness

section HeavyClass

variable {ι : Type*}

/-- A finite averaging lemma used by the bridge-class reduction: in a nonempty finite partition,
one class has at least average mass. -/
theorem exists_mass_ge_average
    (classes : Finset ι) (hclasses : classes.Nonempty) (mass : ι → ℝ) :
    ∃ i ∈ classes, (∑ j ∈ classes, mass j) / (classes.card : ℝ) ≤ mass i := by
  by_contra h
  have hlt : ∀ i ∈ classes, mass i < (∑ j ∈ classes, mass j) / (classes.card : ℝ) := by
    intro i hi
    by_contra hge
    exact h ⟨i, hi, le_of_not_gt hge⟩
  have hsumlt :
      ∑ i ∈ classes, mass i <
        ∑ i ∈ classes, (∑ j ∈ classes, mass j) / (classes.card : ℝ) := by
    exact Finset.sum_lt_sum_of_nonempty hclasses hlt
  have hcard_ne : (classes.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.2 hclasses
  have hsumconst :
      ∑ i ∈ classes, (∑ j ∈ classes, mass j) / (classes.card : ℝ) =
        ∑ j ∈ classes, mass j := by
    simp [Finset.sum_const, hcard_ne]
    field_simp [hcard_ne]
  linarith

end HeavyClass

end RouteAutomata

section NeutralConfluence

variable {Word Profile State Normal : Type*}

/-- A unique-normal-form package for the neutral exact-interface quotient. -/
structure NeutralNormalForm (Word Profile State Normal : Type*) where
  endpointProfile : Word → Profile
  continuationState : Word → State
  normalForm : Word → Normal
  stateOfNormal : Normal → State
  normal_eq_of_same_endpoint :
    ∀ {u v}, endpointProfile u = endpointProfile v → normalForm u = normalForm v
  state_factors :
    ∀ u, continuationState u = stateOfNormal (normalForm u)

namespace NeutralNormalForm

variable (N : NeutralNormalForm Word Profile State Normal)

/-- Bounded exact-interface confluence implies universal routing: continuation state depends
only on the endpoint profile. -/
theorem universal_routing {u v : Word} (h : N.endpointProfile u = N.endpointProfile v) :
    N.continuationState u = N.continuationState v := by
  rw [N.state_factors u, N.state_factors v, N.normal_eq_of_same_endpoint h]

end NeutralNormalForm

/-- The missing neutral localizability lemma is packaged as a hypothesis, matching
`Pasted markdown (3) (14).md`. -/
structure NeutralLocalizability (Word Distinguisher : Type*) where
  ReducedNeutralNonconfluent : Word → Word → Prop
  HasBoundedDiamond : Word → Word → Prop
  ProperLocalizedPair : Distinguisher → Word → Word → Prop
  localizes :
    ∀ {u v}, ReducedNeutralNonconfluent u v →
      HasBoundedDiamond u v ∨ ∃ D, ProperLocalizedPair D u v

end NeutralConfluence

section CommonRay

/-- If a positive linear combination of nonnegative face coordinates is zero, every coordinate
is zero.  This is the formal exposed-face step in the common-ray note. -/
theorem positive_weighted_sum_eq_zero_forces_terms_zero
    {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 < w i) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, w i * a i = 0) :
    ∀ i, a i = 0 := by
  intro i
  by_contra hne
  have hai_pos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hne)
  have hterm_pos : 0 < w i * a i := mul_pos (hw i) hai_pos
  have hnonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ w j * a j := by
    intro j hj
    exact mul_nonneg (le_of_lt (hw j)) (ha j)
  have hle : w i * a i ≤ ∑ j, w j * a j := by
    exact Finset.single_le_sum hnonneg (by simp)
  linarith

/-- For four ordered atoms with zero total signed mass, a nonzero measure has a nonzero
interior tail.  This is the finite `2:2` common-ray imbalance step. -/
theorem four_atom_zero_total_has_nonzero_interior_tail
    (m₁ m₂ m₃ m₄ : ℝ)
    (htotal : m₁ + m₂ + m₃ + m₄ = 0)
    (hnonzero : m₁ ≠ 0 ∨ m₂ ≠ 0 ∨ m₃ ≠ 0 ∨ m₄ ≠ 0) :
    m₂ + m₃ + m₄ ≠ 0 ∨ m₃ + m₄ ≠ 0 ∨ m₄ ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨h234, h34, h4⟩
  have h3 : m₃ = 0 := by linarith
  have h2 : m₂ = 0 := by linarith
  have h1 : m₁ = 0 := by linarith
  rcases hnonzero with h1nz | h2nz | h3nz | h4nz
  · exact h1nz h1
  · exact h2nz h2
  · exact h3nz h3
  · exact h4nz h4

/-- After possibly reversing the ray orientation, a nonzero interior tail is positive. -/
theorem four_atom_zero_total_has_positive_oriented_tail
    (m₁ m₂ m₃ m₄ : ℝ)
    (htotal : m₁ + m₂ + m₃ + m₄ = 0)
    (hnonzero : m₁ ≠ 0 ∨ m₂ ≠ 0 ∨ m₃ ≠ 0 ∨ m₄ ≠ 0) :
    ∃ t, (t = m₂ + m₃ + m₄ ∨ t = m₃ + m₄ ∨ t = m₄) ∧ (0 < t ∨ 0 < -t) := by
  rcases four_atom_zero_total_has_nonzero_interior_tail m₁ m₂ m₃ m₄ htotal hnonzero with
    htail | htail | htail
  · refine ⟨m₂ + m₃ + m₄, Or.inl rfl, ?_⟩
    exact (lt_or_gt_of_ne htail).elim (fun h => Or.inr (by linarith)) Or.inl
  · refine ⟨m₃ + m₄, Or.inr (Or.inl rfl), ?_⟩
    exact (lt_or_gt_of_ne htail).elim (fun h => Or.inr (by linarith)) Or.inl
  · refine ⟨m₄, Or.inr (Or.inr rfl), ?_⟩
    exact (lt_or_gt_of_ne htail).elim (fun h => Or.inr (by linarith)) Or.inl

/-- The separator common-ray missing geometry, stated explicitly as an assumption. -/
structure SeparatorCommonRayPackage where
  WeightedTraceMeasuresEqual : Prop
  PositiveSpliceChildExists : Prop
  first_differing_means_unequal : ¬ WeightedTraceMeasuresEqual
  ray_imbalance_gives_positive_splice : ¬ WeightedTraceMeasuresEqual → PositiveSpliceChildExists

namespace SeparatorCommonRayPackage

/-- If no positive-splice proper child exists, the first-differing common-ray lock cannot survive. -/
theorem contradiction_of_no_positive_splice (S : SeparatorCommonRayPackage)
    (hlock : ¬ S.PositiveSpliceChildExists) :
    False :=
  hlock (S.ray_imbalance_gives_positive_splice S.first_differing_means_unequal)

end SeparatorCommonRayPackage

end CommonRay

section ApolarHexagon

variable {K : Type*} [Field K]

/-- A linear transition preserving the product line `⟨uv⟩` is monomial: diagonal or
anti-diagonal.  The hypotheses `a*c = 0` and `b*d = 0` are exactly the coefficient equations
obtained by requiring `(a u + b v)(c u + d v)` to lie in the product line. -/
theorem monomial_of_preserves_product_line
    {a b c d : K} (hdet : a * d - b * c ≠ 0) (hac : a * c = 0) (hbd : b * d = 0) :
    (b = 0 ∧ c = 0) ∨ (a = 0 ∧ d = 0) := by
  rcases mul_eq_zero.mp hac with ha | hc
  · rcases mul_eq_zero.mp hbd with hb | hd
    · exfalso
      apply hdet
      simp [ha, hb]
    · exact Or.inr ⟨ha, hd⟩
  · rcases mul_eq_zero.mp hbd with hb | hd
    · exact Or.inl ⟨hb, hc⟩
    · exfalso
      apply hdet
      simp [hc, hd]

/-- Ratio cocycles on a six-cycle telescope to one.  This is the scalar Hall-holonomy step once
all charts share the same product factor line. -/
theorem six_cycle_ratio_cocycle
    {t₀ t₁ t₂ t₃ t₄ t₅ : K}
    (h₀ : t₀ ≠ 0) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)
    (h₃ : t₃ ≠ 0) (h₄ : t₄ ≠ 0) (h₅ : t₅ ≠ 0) :
    (t₀ / t₁) * (t₁ / t₂) * (t₂ / t₃) * (t₃ / t₄) * (t₄ / t₅) * (t₅ / t₀) = 1 := by
  field_simp [h₀, h₁, h₂, h₃, h₄, h₅]

end ApolarHexagon

section OneCounterExactification

variable {Prefix Phase Cont Edge : Type*}

/-- Rank-one OA exactification as a finite-phase one-counter interface.  The affine-value field
is the formal version of equation `(2)` in `Pasted text (5) (6).txt`. -/
structure RankOneOneCounterExactification (Prefix Phase Cont : Type*) where
  phase : Prefix → Phase
  counter : Prefix → ℤ
  feasible : Prefix → Cont → Prop
  value : Prefix → Cont → ℝ
  baseValue : Phase → Cont → ℝ
  slope : Phase → ℝ
  feasible_of_same_phase :
    ∀ {x y}, phase x = phase y → ∀ γ, feasible x γ ↔ feasible y γ
  affine_value :
    ∀ {x γ}, feasible x γ →
      value x γ = baseValue (phase x) γ + slope (phase x) * (counter x : ℝ)

namespace RankOneOneCounterExactification

variable (E : RankOneOneCounterExactification Prefix Phase Cont)

/-- Equal finite phase and equal counter give identical feasible continuations and Bellman values. -/
theorem exact_of_equal_machine_state {x y : Prefix}
    (hphase : E.phase x = E.phase y) (hcounter : E.counter x = E.counter y) :
    (∀ γ, E.feasible x γ ↔ E.feasible y γ) ∧
      ∀ γ, E.feasible x γ → E.value x γ = E.value y γ := by
  constructor
  · exact E.feasible_of_same_phase hphase
  · intro γ hγ
    have hy : E.feasible y γ := (E.feasible_of_same_phase hphase γ).1 hγ
    rw [E.affine_value hγ, E.affine_value hy, hphase, hcounter]

end RankOneOneCounterExactification

/-- A finite set of edge increments always has a uniform absolute bound. -/
theorem exists_uniform_increment_bound [Fintype Edge] (weight : Edge → ℤ) :
    ∃ L : ℕ, ∀ e, (weight e).natAbs ≤ L := by
  let L : ℕ := Finset.univ.sup fun e : Edge => (weight e).natAbs
  refine ⟨L, ?_⟩
  intro e
  simpa [L] using
    (Finset.le_sup (s := (Finset.univ : Finset Edge))
      (f := fun e : Edge => (weight e).natAbs) (b := e) (by simp))

/-- One-counter updates are exactly additive in the visible scalar coordinate. -/
theorem counter_update_of_profile_increment
    {Profile : Type*} [AddCommGroup Profile] (χ : Profile →+ ℤ)
    (profile : Prefix → Profile) (increment : Edge → Profile)
    (step : Prefix → Edge → Prefix)
    (hstep : ∀ x e, profile (step x e) = profile x + increment e)
    (x : Prefix) (e : Edge) :
    χ (profile (step x e)) = χ (profile x) + χ (increment e) := by
  rw [hstep, map_add]

end OneCounterExactification

end PastedNotes
end FormalConjectures.Problems.Erdos.E20
