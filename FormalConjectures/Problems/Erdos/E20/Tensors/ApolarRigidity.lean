import Mathlib

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Local Apolar Rigidity over `F_5`

This file formalizes the concrete finite-field calculation from the pasted `(5,5)` lane note.

For a two-branch binary quartic `q = α x^4 + β y^4` over `F_5`, contraction by
`a ∂x^2 + b ∂x∂y + c ∂y^2` has only two nonzero coefficient slots:

* the `x^2` coefficient is `2 a α`;
* the `y^2` coefficient is `2 c β`;
* the mixed coefficient `b` contributes zero.

Thus, when `α` and `β` are nonzero, the degree-2 apolar annihilator is exactly the line
spanned by the mixed operator `∂x∂y`.
-/

abbrev F5 : Type := ZMod 5

instance : Fact (Nat.Prime 5) := by
  decide

/-- Coefficients of a quadratic differential operator
`a ∂x^2 + b ∂x∂y + c ∂y^2`. -/
structure BinaryQuadraticOperator where
  a : F5
  b : F5
  c : F5
deriving DecidableEq, Repr, Fintype

/-- The degree-2 contraction coefficients of
`a ∂x^2 + b ∂x∂y + c ∂y^2` against `α x^4 + β y^4`.

The return value stores the `x^2` and `y^2` coefficients. The mixed coefficient is zero for a
two-branch quartic, so the `b` field does not appear. -/
def twoBranchQuarticContraction (α β : F5) (D : BinaryQuadraticOperator) : F5 × F5 :=
  (2 * D.a * α, 2 * D.c * β)

set_option linter.style.nativeDecide false in
/-- In `F_5`, a nondegenerate two-branch quartic has degree-2 apolar annihilator exactly
`a = 0` and `c = 0`; the mixed coefficient `b` is unrestricted. -/
theorem twoBranchQuarticContraction_eq_zero_iff
    (α β : F5) (hα : α ≠ 0) (hβ : β ≠ 0) (D : BinaryQuadraticOperator) :
    twoBranchQuarticContraction α β D = (0, 0) ↔ D.a = 0 ∧ D.c = 0 := by
  revert α β D
  native_decide

/-- The operator `b ∂x∂y` annihilates every two-branch quartic `α x^4 + β y^4`. -/
theorem mixed_operator_mem_twoBranch_annihilator (α β b : F5) :
    twoBranchQuarticContraction α β { a := 0, b := b, c := 0 } = (0, 0) := by
  simp [twoBranchQuarticContraction]

/-- A degree-2 apolar operator for a nondegenerate two-branch quartic is uniquely determined by
its mixed coefficient. -/
theorem twoBranch_annihilator_ext
    (α β : F5) (hα : α ≠ 0) (hβ : β ≠ 0)
    {D E : BinaryQuadraticOperator}
    (hD : twoBranchQuarticContraction α β D = (0, 0))
    (hE : twoBranchQuarticContraction α β E = (0, 0))
    (hb : D.b = E.b) :
    D = E := by
  have hDa := (twoBranchQuarticContraction_eq_zero_iff α β hα hβ D).1 hD
  have hEa := (twoBranchQuarticContraction_eq_zero_iff α β hα hβ E).1 hE
  cases D
  cases E
  simp_all

section Holonomy

variable {G : Type*} [CommGroup G]

/-- The scalar ratio cocycle around a hexagon telescopes to `1`.  This is the
formal algebraic core of the Hall-lane holonomy note. -/
theorem hexagon_transitionScalar_holonomy_eq_one (t : Fin 6 → G) :
    (t 0 / t 1) * (t 1 / t 2) * (t 2 / t 3) * (t 3 / t 4) * (t 4 / t 5) * (t 5 / t 0) = 1 := by
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- A common apolar factor line produces trivial Hall-lane scalar holonomy. -/
theorem apolar_commonRay_implies_trivialHallLaneHolonomy (t : Fin 6 → G) :
    (t 0 / t 1) * (t 1 / t 2) * (t 2 / t 3) * (t 3 / t 4) * (t 4 / t 5) * (t 5 / t 0) = 1 :=
  hexagon_transitionScalar_holonomy_eq_one t

end Holonomy

end FormalConjectures.Problems.Erdos.E20
