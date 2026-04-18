import FormalConjectures.Problems.Erdos.E119.Findings.Defs
import FormalConjectures.Problems.Erdos.E119.Findings.FixedCenterCoherence

/-!
# Erdős 119 Findings: Analytic Fact Interfaces

This file turns the cited external inputs from the user-supplied source note into explicit Lean
propositions. These declarations are interfaces: they record the exact assumptions used by the
current E119 findings, without pretending that those analytic facts have already been derived in
this repository.
-/

open scoped BigOperators

namespace Erdos119
namespace Findings

/--
Formalizes the ordered-index input used in
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 0 ("Fact 2") and Section 1 ("Dyadic affine-rank rigidity theorem"):
`indices` is a strictly increasing list of ranks in `{1, ..., n}`, encoded on `Fin m`.
-/
def LocalIndexModel (m n : ℕ) (indices : Fin m → ℕ) : Prop :=
  StrictMono indices ∧ ∀ r : Fin m, 1 ≤ indices r ∧ indices r ≤ n

/--
Formalizes the cited "Fact 1" from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 0 and Section 1 ("Geometric 'after rotation' version").

This is the explicit interface used by the source note: a top-scale prefix-norm bound implies that,
after a suitable rotation, the ordered arguments are square-close to a regular polygon.
-/
def Fact1TopScaleRegularity
    (q top : ℕ) (prefixNorm : ℕ → ℝ) (angles : Fin (2 ^ top) → ℝ) : Prop :=
  ∀ η : ℝ,
    prefixNorm (2 ^ top) ≤ Real.exp η * ((q : ℝ) / ((2 ^ top : ℕ) : ℝ)) →
      ∃ φ : ℝ,
        (∑ s : Fin (2 ^ top),
          (angles s - φ - 2 * Real.pi * (((s.1 + 1 : ℕ) : ℝ) / ((2 ^ top : ℕ) : ℝ))) ^ 2)
            ≤ 4 * η

/--
Formalizes the cited "Fact 2" from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 0 and Section 1 ("Step 1. Local affine-rank rigidity").

This interface states that an ordered family of indices in `{1, ..., n}` admits an affine-rank
approximation with squared error controlled by the local defect terms.
-/
def Fact2LocalAffineRankControl (delta : ℕ → ℝ) : Prop :=
  ∀ {m n : ℕ}, 1 ≤ m → m ≤ n →
    ∀ indices : Fin m → ℕ, LocalIndexModel m n indices →
      ∃ c : ℝ,
        (∑ r : Fin m,
          (((indices r : ℕ) : ℝ) / (n : ℝ) -
            (((r.1 + 1 : ℕ) : ℝ) / (m : ℝ)) - c) ^ 2)
              ≤ (2 / Real.pi ^ 2) * (delta m + delta n)

/--
Formalizes the cited "Fact 3" from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 0 and Section 7 ("Fixed-center coherence").

The source note uses this only through the following interface: if every dyadic band
`[ρ_{j+1}, ρ_j]` has centered defect at most `-Δ j`, then `u θ` is bounded below by a positive
constant times the sum of those band defects.
-/
def Fact3BandEnergyLowerBound
    (centeredDefect : ℝ → ℝ → ℝ) (u : ℝ → ℝ) : Prop :=
  ∃ c0 : ℝ, 0 ≤ c0 ∧
    ∀ {θ : ℝ} {m : ℕ} {ρ Δ : ℕ → ℝ},
      (∀ j, j < m → ρ (j + 1) = ρ j / 2) →
      (∀ j, j < m → ∀ r : ℝ, ρ (j + 1) ≤ r → r ≤ ρ j → centeredDefect θ r ≤ -Δ j) →
      c0 * Finset.sum (Finset.range m) (fun j => Δ j) ≤ u θ

/--
Formalizes the cited qualitative "Fact 5" from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 0 and Section 3 ("Version stable under bounded `q`-lifts").

The source note explicitly says that no exact constants were specified. Accordingly, this Lean
interface keeps the transfer relation abstract: for each source local-defect budget there exists
some lifted local-defect budget related to it by an external qualitative transfer relation.
-/
def Fact5QualitativeLiftTransfer
    (Transfer : (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  ∀ sourceBudget : ℕ → ℝ, ∃ liftedBudget : ℕ → ℝ, Transfer sourceBudget liftedBudget

/--
Formalizes the way the repaired trimmed fixed-center recursion combines with the cited Fact 3 from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7.

Starting from the recursive inequalities `B j ≤ B (j + 1) - δ j`, this theorem converts the band
functional lower bound from Fact 3 into the cumulative tail-sum lower bound
`c₀ * ∑_j tailSum m δ j ≤ u θ`.
-/
theorem fact3_tailSumLowerBound_of_additiveBudget
    {centeredDefect : ℝ → ℝ → ℝ} {u : ℝ → ℝ}
    (h3 : Fact3BandEnergyLowerBound centeredDefect u)
    {θ : ℝ} {m : ℕ} {ρ B δ : ℕ → ℝ}
    (hdyadic : ∀ j, j < m → ρ (j + 1) = ρ j / 2)
    (hbase : B m ≤ 0)
    (hstep : ∀ j, j < m → B j ≤ B (j + 1) - δ j)
    (hband : ∀ j, j < m → ∀ r : ℝ, ρ (j + 1) ≤ r → r ≤ ρ j → centeredDefect θ r ≤ B j) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ c0 * Finset.sum (Finset.range m) (fun j => tailSum m δ j) ≤ u θ := by
  rcases h3 with ⟨c0, hc0, h3use⟩
  refine ⟨c0, hc0, ?_⟩
  have hbudget := additiveNegativeBudget (m := m) (B := B) (δ := δ) hbase hstep
  have hband' :
      ∀ j, j < m → ∀ r : ℝ, ρ (j + 1) ≤ r → r ≤ ρ j → centeredDefect θ r ≤ -tailSum m δ j := by
    intro j hj r hr1 hr2
    exact (hband j hj r hr1 hr2).trans (hbudget j (Nat.le_of_lt hj))
  exact h3use hdyadic hband'

/--
Formalizes the weighted lower bound `c₀ * ∑_k (k + 1) δ_k ≤ u θ` obtained by combining
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7, equation `(2)`, with the cited Fact 3 interface and the additive recursion.
-/
theorem fact3_weightedLowerBound_of_additiveBudget
    {centeredDefect : ℝ → ℝ → ℝ} {u : ℝ → ℝ}
    (h3 : Fact3BandEnergyLowerBound centeredDefect u)
    {θ : ℝ} {m : ℕ} {ρ B δ : ℕ → ℝ}
    (hdyadic : ∀ j, j < m → ρ (j + 1) = ρ j / 2)
    (hbase : B m ≤ 0)
    (hstep : ∀ j, j < m → B j ≤ B (j + 1) - δ j)
    (hband : ∀ j, j < m → ∀ r : ℝ, ρ (j + 1) ≤ r → r ≤ ρ j → centeredDefect θ r ≤ B j) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧
      c0 * Finset.sum (Finset.range m) (fun k => ((k + 1 : ℕ) : ℝ) * δ k) ≤ u θ := by
  rcases fact3_tailSumLowerBound_of_additiveBudget h3 hdyadic hbase hstep hband with
    ⟨c0, hc0, htail⟩
  refine ⟨c0, hc0, ?_⟩
  simpa [sum_tailSum_eq_weighted_sum] using htail

end Findings
end Erdos119
