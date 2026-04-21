import Mathlib

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Separator-Compatible Lifting

This file isolates the local hypotheses from the pasted separator note.

We do not prove the separator bridge unconditionally.  Instead, we name the missing hypotheses
explicitly and record the formal implication that a stronger visible-split forcing assumption
immediately yields the weaker separator-compatible lifting statement.
-/

variable {Kernel : Type*}

/-- Visible split forcing is stronger than separator-compatible lifting. -/
theorem visibleSplitForcing_implies_separatorCompatibleLifting
    {IsLarge IsCompatible HasProfitablePrefixBlock : Kernel → Prop}
    (hVS : ∀ K, IsLarge K → HasProfitablePrefixBlock K) :
    ∀ K, IsLarge K → IsCompatible K ∨ HasProfitablePrefixBlock K := by
  intro K hK
  exact Or.inr (hVS K hK)

section OneDimensionalCommonRay

/-!
The new common-ray note reduces the balanced `2:2` separator geometry to a
one-dimensional hinge calculation.  The theorem below proves the finite
three-cut calculation from the recurrence

`G₁ - G₂ = S₁ d₁`, `G₂ - G₃ = S₂ d₂`, `G₃ = S₃ d₃`

with positive gaps `dᵢ`.  It is intentionally stated only as the discrete
calculation; the geometric dictionary from separator children to these
quantities remains an external hypothesis in higher-level applications.
-/

/-- In a three-cut one-dimensional sweep, some oriented cut has cumulative
imbalance and hinge splice gap with the same positive sign. -/
theorem three_cut_hinge_positive
    (S₁ S₂ S₃ G₁ G₂ G₃ d₁ d₂ d₃ : ℝ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (h₁ : G₁ - G₂ = S₁ * d₁)
    (h₂ : G₂ - G₃ = S₂ * d₂)
    (h₃ : G₃ = S₃ * d₃)
    (hnz : G₁ ≠ 0 ∨ G₂ ≠ 0 ∨ G₃ ≠ 0) :
    ∃ S G,
      ((S = S₁ ∧ G = G₁) ∨ (S = S₂ ∧ G = G₂) ∨ (S = S₃ ∧ G = G₃)) ∧
        ((0 < S ∧ 0 < G) ∨ (0 < -S ∧ 0 < -G)) := by
  by_cases hG₃pos : 0 < G₃
  · refine ⟨S₃, G₃, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨?_, hG₃pos⟩⟩
    nlinarith
  have hG₃le : G₃ ≤ 0 := le_of_not_gt hG₃pos
  by_cases hG₂pos : 0 < G₂
  · refine ⟨S₂, G₂, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨?_, hG₂pos⟩⟩
    nlinarith
  have hG₂le : G₂ ≤ 0 := le_of_not_gt hG₂pos
  by_cases hG₁pos : 0 < G₁
  · refine ⟨S₁, G₁, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨?_, hG₁pos⟩⟩
    nlinarith
  have hG₁le : G₁ ≤ 0 := le_of_not_gt hG₁pos
  by_cases hG₃neg : G₃ < 0
  · refine ⟨S₃, G₃, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr ⟨?_, ?_⟩⟩
    · nlinarith
    · nlinarith
  have hG₃zero : G₃ = 0 := le_antisymm hG₃le (not_lt.mp hG₃neg)
  by_cases hG₂neg : G₂ < 0
  · refine ⟨S₂, G₂, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr ⟨?_, ?_⟩⟩
    · nlinarith
    · nlinarith
  have hG₂zero : G₂ = 0 := le_antisymm hG₂le (not_lt.mp hG₂neg)
  have hG₁neg : G₁ < 0 := by
    rcases hnz with hne | hne | hne
    · exact lt_of_le_of_ne hG₁le hne
    · exact (hne hG₂zero).elim
    · exact (hne hG₃zero).elim
  refine ⟨S₁, G₁, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith

end OneDimensionalCommonRay

end FormalConjectures.Problems.Erdos.E20
