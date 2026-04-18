import Mathlib

/-!
# Erdős 119 Findings: `W` Counterexample Arithmetic

This file formalizes the explicit arithmetic identities used in the `q = 8`
counterexample discussion from the user-supplied source note.
-/

namespace Erdos119
namespace Findings

noncomputable section

/--
Formalizes the explicit `q = 8` counterexample value
`21 + 4u + 2/u` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9 ("`W` versus parity recursion"), subsection "Explicit `q = 8` counterexample".
-/
def wEightCandidate (u : ℝ) : ℝ :=
  21 + 4 * u + 2 / u

/--
Formalizes the normalized constant `ρ = W(8) / 27` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9, subsection "Explicit candidate family beating exact `3^m`".
-/
def rhoW (u : ℝ) : ℝ :=
  wEightCandidate u / 27

/--
Formalizes the recursively propagated value `3^(m-3) W(8)` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9, subsection "Explicit candidate family beating exact `3^m`".
-/
def recursiveWFamilyValue (u : ℝ) (m : ℕ) : ℝ :=
  (3 : ℝ) ^ (m - 3) * wEightCandidate u

/--
Formalizes the arithmetic inequality `21 + 4u + 2/u < 27` proved in
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9, subsection "Explicit `q = 8` counterexample",
from the interval assumptions `1 / 2 < u < 1`.
-/
theorem wEightCandidate_lt_27_of_bounds {u : ℝ} (hu0 : 0 < u) (hhalf : (1 : ℝ) / 2 < u)
    (hone : u < 1) : wEightCandidate u < 27 := by
  have hu : u ≠ 0 := by linarith
  have hneg : (2 * u - 1) * (u - 1) < 0 := by
    have h1 : 0 < 2 * u - 1 := by linarith
    have h2 : u - 1 < 0 := by linarith
    exact mul_neg_of_pos_of_neg h1 h2
  have hpoly : 2 * u ^ 2 - 3 * u + 1 < 0 := by
    nlinarith
  have hfrac : 4 * u + 2 / u < 6 := by
    field_simp [hu]
    nlinarith [hu0, hpoly]
  unfold wEightCandidate
  linarith

/--
Formalizes the conclusion `ρ < 1` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9, subsection "Explicit candidate family beating exact `3^m`".
-/
theorem rhoW_lt_one_of_bounds {u : ℝ} (hu0 : 0 < u) (hhalf : (1 : ℝ) / 2 < u) (hone : u < 1) :
    rhoW u < 1 := by
  unfold rhoW
  have hw : wEightCandidate u < 27 := wEightCandidate_lt_27_of_bounds hu0 hhalf hone
  linarith

/--
Formalizes the identity `3^(m-3) W(8) = ρ 3^m` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 9, subsection "Explicit candidate family beating exact `3^m`".
-/
theorem recursiveWFamilyValue_eq_rho_mul (u : ℝ) {m : ℕ} (hm : 3 ≤ m) :
    recursiveWFamilyValue u m = rhoW u * (3 : ℝ) ^ m := by
  have hm' : m = (m - 3) + 3 := by
    omega
  unfold recursiveWFamilyValue rhoW wEightCandidate
  rw [hm', pow_add]
  norm_num
  field_simp

end
end Findings
end Erdos119
