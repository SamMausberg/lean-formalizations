import Mathlib

open scoped BigOperators

namespace FormalConjectures.Problems.Erdos.E20

/-- Frontier disintegration data for a solved-trace deficit argument.

The weight decomposition and the frontier family are the formal content of the
"frontier disintegration" step.  The low-coherence/gluing mechanism is *not*
proved here; it appears only in the later pressure-aggregation structure. -/
structure FrontierDisintegration (Obj : Type*) [DecidableEq Obj] where
  Frontier : Obj → Finset Obj
  residueWeight : Obj → ℝ
  frontierWeight : Obj → Obj → ℝ
  residue_nonneg : ∀ X, 0 ≤ residueWeight X
  frontier_nonneg : ∀ X Y, 0 ≤ frontierWeight X Y
  total_weight : ∀ X, residueWeight X + Finset.sum (Frontier X) (fun Y => frontierWeight X Y) = 1

/-- Frontier pressure aggregation packages the missing low-coherence/gluing input explicitly.

The `aggregate` field is the exact hypothesis that the note uses informally:
the parent pressure is bounded below by the residue contribution plus the
weighted sum of the frontier pressures. -/
structure FrontierPressureAggregation (Obj : Type*) [DecidableEq Obj]
    extends FrontierDisintegration Obj where
  Pressure : Obj → ℝ
  Baseline : Obj → ℝ
  baseline_le_one : ∀ X, Baseline X ≤ 1
  low_coherence : ∀ {X Y}, Y ∈ Frontier X → Baseline X ≤ Baseline Y
  aggregate :
    ∀ X, residueWeight X + Finset.sum (Frontier X) (fun Y => frontierWeight X Y * Pressure Y) ≤
      Pressure X

namespace FrontierPressureAggregation

variable {Obj : Type*} [DecidableEq Obj]
variable (D : FormalConjectures.Problems.Erdos.E20.FrontierPressureAggregation Obj)

/-- The solved-trace deficit is baseline pressure minus actual pressure. -/
def Deficit (X : Obj) : ℝ :=
  D.Baseline X - D.Pressure X

/-- Positive deficit is equivalent to the pressure being strictly below baseline. -/
theorem deficit_pos_iff {X : Obj} :
    0 < D.Deficit X ↔ D.Pressure X < D.Baseline X := by
  constructor
  · intro h
    simpa [Deficit] using (sub_pos.mp h)
  · intro h
    simpa [Deficit] using (sub_pos.mpr h)

/-- Pressure aggregation across the frontier: if every frontier child already meets the
baseline, then the parent also meets it. -/
theorem pressure_aggregation
    {X : Obj}
    (hchild : ∀ Y ∈ D.Frontier X, D.Baseline X ≤ D.Pressure Y) :
    D.Baseline X ≤ D.Pressure X := by
  have hsum :
      Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Baseline X) ≤
        Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Pressure Y) := by
    refine Finset.sum_le_sum ?_
    intro Y hY
    exact mul_le_mul_of_nonneg_left (hchild Y hY) (D.frontier_nonneg X Y)
  have hsum' :
      D.residueWeight X +
          Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Baseline X) ≤
        D.residueWeight X +
          Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Pressure Y) := by
    exact add_le_add_right hsum (D.residueWeight X)
  have hbase :
      D.Baseline X ≤
        D.residueWeight X +
          Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Baseline X) := by
    have hsumw :
        Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y) = 1 - D.residueWeight X := by
      linarith [D.total_weight X]
    have hmul :
        D.residueWeight X +
            Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Baseline X) =
          D.residueWeight X +
            Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y) * D.Baseline X := by
      rw [Finset.sum_mul]
    rw [hmul, hsumw]
    have h1 : D.Baseline X ≤ 1 := D.baseline_le_one X
    have hres : 0 ≤ D.residueWeight X := D.residue_nonneg X
    nlinarith
  have hge :
      D.residueWeight X + Finset.sum (D.Frontier X) (fun Y => D.frontierWeight X Y * D.Baseline X) ≤
        D.Pressure X := by
    exact le_trans hsum' (D.aggregate X)
  exact le_trans hbase hge

/-- Positive deficit localizes to some frontier child.

This is the formal replacement for the informal "positive deficit cannot vanish
into purely nonexact branching" step.  Any gluing or coherence needed to justify
the aggregation inequality has to be supplied in `aggregate` and `low_coherence`. -/
theorem positive_deficit_localizes
    {X : Obj} (hX : 0 < D.Deficit X) :
    ∃ Y ∈ D.Frontier X, 0 < D.Deficit Y := by
  have hX' : D.Pressure X < D.Baseline X := (D.deficit_pos_iff (X := X)).1 hX
  by_contra hno
  have hchild : ∀ Y ∈ D.Frontier X, D.Baseline X ≤ D.Pressure Y := by
    intro Y hY
    by_contra hbad
    have hltX : D.Pressure Y < D.Baseline X := lt_of_not_ge hbad
    have hltY : D.Pressure Y < D.Baseline Y := lt_of_lt_of_le hltX (D.low_coherence hY)
    exact hno ⟨Y, hY, (D.deficit_pos_iff (X := Y)).2 hltY⟩
  have hge : D.Baseline X ≤ D.Pressure X := D.pressure_aggregation hchild
  linarith

end FrontierPressureAggregation

end FormalConjectures.Problems.Erdos.E20
