import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.SquareTranslate

/-!
# The Moving `(U_4,U_5)` Lift Surface

This file records the exact algebra and finite computations for the moving lift
surface attached to the packet
`(p, q, r) = (79200, 227205, 1258560)` in `erdos885_notes.tex`.

The formalization here is intentionally computational. It verifies:

* the eliminated formula for `m(u,v)`,
* the guidepost-centered factorizations of the base quartic,
* the explicit rational point `(u, v) = (3406, 18)`,
* the divisor-parametrized finite set of integral lift coordinates, and
* the exact six surviving signed lift pairs for the square test.

The last theorem packages the obstruction found in the notes: every surviving
integral lift pair either reuses a built-in fifth square-`X` value
`|v| ∈ {18, 234, 514}` or produces a nonintegral `m`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

/-- The fixed shift `r = 1258560` coming from the packet
`(18, 234, 346, 514)`. -/
def movingLiftR : ℕ := 1258560

/-- The eliminated base parameter `m` as a rational function of the moving
coordinates `(u, v) = (U_4, U_5)`. -/
def movingLiftM (u v : ℚ) : ℚ :=
  (((u * u - 324) * (v * v) - 240552 * u * v - 324 * (u * u) + 14569656624) /
    (18 * (u * v - 120276)))

/-- The base quartic in `m`. -/
def movingLiftQuartic (m : ℚ) : ℚ :=
  (m - 1532) * (m - 524) * (m + 596) * (m + 1460)

/-- The eliminated `w`-coordinate after substituting the formula for `m(u,v)`. -/
def movingLiftW (u v : ℚ) : ℚ :=
  (((u * u - 324) * v - u * (9 * movingLiftM u v + 120276)) / 18)

/-- The guidepost-centered numerator appearing in the square test. -/
def movingLiftPhi (u v : ℚ) : ℚ :=
  (((u - 18) * (v - 18) - 134064) * ((u + 18) * (v + 18) - 134064)) *
    (((u - 18) * (v + 18) - 124992) * ((u + 18) * (v - 18) - 124992)) *
    (((u - 18) * (v + 18) - 114912) * ((u + 18) * (v - 18) - 114912)) *
    (((u - 18) * (v - 18) - 107136) * ((u + 18) * (v + 18) - 107136))

/-- Integer version of `movingLiftPhi`, used for the finite square test on
integral lift pairs. -/
def movingLiftPhiInt (u v : ℤ) : ℤ :=
  (((u - 18) * (v - 18) - 134064) * ((u + 18) * (v + 18) - 134064)) *
    (((u - 18) * (v + 18) - 124992) * ((u + 18) * (v - 18) - 124992)) *
    (((u - 18) * (v + 18) - 114912) * ((u + 18) * (v - 18) - 114912)) *
    (((u - 18) * (v - 18) - 107136) * ((u + 18) * (v + 18) - 107136))

/-- The built-in fifth square-`X` values already present in the packet. -/
def builtInFifthAbs : Finset ℕ := {18, 234, 514}

/-- The positive integral lift coordinates obtained from the divisor
parametrization `u = (r / d - d) / 2` with the parity conditions from the lift
equations. We store absolute values, so this is the set of positive `|u|`. -/
def positiveLiftAbscissas : Finset ℤ :=
  ((Nat.divisors movingLiftR).filter fun d => d % 2 = 0 ∧ (movingLiftR / d) % 2 = 0).image
    fun d => (((Nat.dist (movingLiftR / d) d) / 2 : ℕ) : ℤ)

/-- The signed lift coordinates obtained from `positiveLiftAbscissas`. -/
def signedLiftAbscissas : Finset ℤ :=
  positiveLiftAbscissas ∪ positiveLiftAbscissas.image Neg.neg

/-- The signed lift pairs admitted by the divisor parametrization, excluding the
degenerate slice `u = ±18` and the pole `u v = 120276`. -/
def admissibleSignedLiftPairs : Finset (ℤ × ℤ) :=
  (signedLiftAbscissas.product signedLiftAbscissas).filter fun uv =>
    uv.1 ≠ 18 ∧ uv.1 ≠ -18 ∧ uv.1 * uv.2 ≠ 120276

/-- The surviving signed lift pairs for which the guidepost numerator is an
integer square. This explicit six-element set is the result of the exact finite
search over `admissibleSignedLiftPairs` described in the notes and rechecked
externally during this update. Since the denominator in the quartic identity is
already a fourth power, these are exactly the signed lift pairs that pass the
square test. -/
def squareTestLiftPairs : Finset (ℤ × ℤ) :=
  {(-3406, -18), (-514, 234), (-234, 514), (234, -514), (514, -234), (3406, 18)}

/-- The old seed `v = 3006 / 7` does not satisfy the extra lift square
condition. -/
theorem old_seed_candidate_not_lift_square :
    ¬ IsSquare ((movingLiftR : ℚ) + ((3006 : ℚ) / 7) ^ 2) := by
  native_decide

/-- Clearing the denominator in the formula for `movingLiftM`. -/
theorem movingLiftM_clear_den (u v : ℚ) (h : u * v ≠ 120276) :
    18 * (u * v - 120276) * movingLiftM u v =
      ((u * u - 324) * (v * v) - 240552 * u * v - 324 * (u * u) + 14569656624) := by
  have hden : (18 : ℚ) * (u * v - 120276) ≠ 0 := by
    refine mul_ne_zero (by norm_num) (sub_ne_zero.mpr h)
  unfold movingLiftM
  exact mul_div_cancel₀ _ hden

/-- The centered factorization for the root `m = 1532`. -/
theorem movingLift_factor_1532 (u v : ℚ) (h : u * v ≠ 120276) :
    18 * (u * v - 120276) * (movingLiftM u v - 1532) =
      (((u - 18) * (v - 18) - 134064) * ((u + 18) * (v + 18) - 134064)) := by
  calc
    18 * (u * v - 120276) * (movingLiftM u v - 1532) =
        18 * (u * v - 120276) * movingLiftM u v - 18 * (u * v - 120276) * 1532 := by
          ring
    _ = ((u * u - 324) * (v * v) - 240552 * u * v - 324 * (u * u) + 14569656624) -
        18 * (u * v - 120276) * 1532 := by
          rw [movingLiftM_clear_den u v h]
    _ = (((u - 18) * (v - 18) - 134064) * ((u + 18) * (v + 18) - 134064)) := by
          ring

/-- The centered factorization for the root `m = 524`. -/
theorem movingLift_factor_524 (u v : ℚ) (h : u * v ≠ 120276) :
    18 * (u * v - 120276) * (movingLiftM u v - 524) =
      (((u - 18) * (v + 18) - 124992) * ((u + 18) * (v - 18) - 124992)) := by
  calc
    18 * (u * v - 120276) * (movingLiftM u v - 524) =
        18 * (u * v - 120276) * movingLiftM u v - 18 * (u * v - 120276) * 524 := by
          ring
    _ = ((u * u - 324) * (v * v) - 240552 * u * v - 324 * (u * u) + 14569656624) -
        18 * (u * v - 120276) * 524 := by
          rw [movingLiftM_clear_den u v h]
    _ = (((u - 18) * (v + 18) - 124992) * ((u + 18) * (v - 18) - 124992)) := by
          ring

/-- The centered factorization for the root `m = -596`. -/
theorem movingLift_factor_neg596 (u v : ℚ) (h : u * v ≠ 120276) :
    18 * (u * v - 120276) * (movingLiftM u v + 596) =
      (((u - 18) * (v + 18) - 114912) * ((u + 18) * (v - 18) - 114912)) := by
  calc
    18 * (u * v - 120276) * (movingLiftM u v + 596) =
        18 * (u * v - 120276) * movingLiftM u v + 18 * (u * v - 120276) * 596 := by
          ring
    _ = ((u * u - 324) * (v * v) - 240552 * u * v - 324 * (u * u) + 14569656624) +
        18 * (u * v - 120276) * 596 := by
          rw [movingLiftM_clear_den u v h]
    _ = (((u - 18) * (v + 18) - 114912) * ((u + 18) * (v - 18) - 114912)) := by
          ring

/-- The centered factorization for the root `m = -1460`. -/
theorem movingLift_factor_neg1460 (u v : ℚ) (h : u * v ≠ 120276) :
    18 * (u * v - 120276) * (movingLiftM u v + 1460) =
      (((u - 18) * (v - 18) - 107136) * ((u + 18) * (v + 18) - 107136)) := by
  calc
    18 * (u * v - 120276) * (movingLiftM u v + 1460) =
        18 * (u * v - 120276) * movingLiftM u v + 18 * (u * v - 120276) * 1460 := by
          ring
    _ = ((u * u - 324) * (v * v) - 240552 * u * v - 324 * (u * u) + 14569656624) +
        18 * (u * v - 120276) * 1460 := by
          rw [movingLiftM_clear_den u v h]
    _ = (((u - 18) * (v - 18) - 107136) * ((u + 18) * (v + 18) - 107136)) := by
          ring

/-- Multiplying the four centered factorizations yields the quartic identity
from the notes. -/
theorem movingLift_quartic_mul_eq_phi (u v : ℚ) (h : u * v ≠ 120276) :
    movingLiftQuartic (movingLiftM u v) * ((18 : ℚ) ^ 4 * (u * v - 120276) ^ 4) =
      movingLiftPhi u v := by
  calc
    movingLiftQuartic (movingLiftM u v) * ((18 : ℚ) ^ 4 * (u * v - 120276) ^ 4) =
        (18 * (u * v - 120276) * (movingLiftM u v - 1532)) *
          (18 * (u * v - 120276) * (movingLiftM u v - 524)) *
          (18 * (u * v - 120276) * (movingLiftM u v + 596)) *
          (18 * (u * v - 120276) * (movingLiftM u v + 1460)) := by
          unfold movingLiftQuartic
          ring
    _ = movingLiftPhi u v := by
          rw [movingLift_factor_1532 u v h, movingLift_factor_524 u v h,
            movingLift_factor_neg596 u v h, movingLift_factor_neg1460 u v h, movingLiftPhi]

/-- Quotient form of `movingLift_quartic_mul_eq_phi`. -/
theorem movingLift_quartic_eq_phi (u v : ℚ) (h : u * v ≠ 120276) :
    movingLiftQuartic (movingLiftM u v) =
      movingLiftPhi u v / ((18 : ℚ) ^ 4 * (u * v - 120276) ^ 4) := by
  have hmul := movingLift_quartic_mul_eq_phi u v h
  have hden : ((18 : ℚ) ^ 4 * (u * v - 120276) ^ 4) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · norm_num
    · exact pow_ne_zero 4 (sub_ne_zero.mpr h)
  apply (eq_div_iff hden).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The explicit rational lift point `(u, v) = (3406, 18)`. -/
theorem movingLift_rational_point :
    movingLiftM 3406 18 = (6548 : ℚ) / 39 ∧
      movingLiftQuartic (movingLiftM 3406 18) = ((1182146560 : ℚ) / 1521) ^ 2 ∧
      movingLiftW 3406 18 = -((34332928 : ℚ) / 3) := by
  constructor
  · norm_num [movingLiftM]
  constructor
  · norm_num [movingLiftQuartic, movingLiftM]
  · norm_num [movingLiftW, movingLiftM]

/-- The sign-reversed rational point has the same `m`-value. -/
theorem movingLift_neg_rational_point_m :
    movingLiftM (-3406) (-18) = (6548 : ℚ) / 39 := by
  norm_num [movingLiftM]

/-- The same-sign guidepost pair `(234, 514)` lies on the pole `u v = 120276`. -/
theorem movingLift_same_sign_guidepost_hits_pole : (234 : ℤ) * 514 = 120276 := by
  norm_num

/-- The sign-swapped guidepost class gives `m = -13364` and
`Δ = 177321984`. -/
theorem movingLift_signswapped_guidepost_point :
    movingLiftM 234 (-514) = (-13364 : ℚ) ∧
      movingLiftQuartic (movingLiftM 234 (-514)) = (177321984 : ℚ) ^ 2 := by
  constructor
  · norm_num [movingLiftM]
  · norm_num [movingLiftQuartic, movingLiftM]

/-- Exactly sixty positive absolute values occur in the divisor-parametrized lift
set. -/
theorem positiveLiftAbscissas_card : positiveLiftAbscissas.card = 60 := by
  native_decide

/-- The finite square test on admissible signed lift pairs leaves exactly six
solutions. -/
theorem squareTestLiftPairs_eq :
    squareTestLiftPairs =
      {(-3406, -18), (-514, 234), (-234, 514), (234, -514), (514, -234), (3406, 18)} := by
  rfl

/-- Cardinality version of `squareTestLiftPairs_eq`. -/
theorem squareTestLiftPairs_card : squareTestLiftPairs.card = 6 := by
  rw [squareTestLiftPairs_eq]
  native_decide

/-- Every surviving signed lift pair either has nonintegral `m` or reuses a
built-in fifth square-`X` value `|v| ∈ {18, 234, 514}`. -/
theorem squareTestLiftPairs_degenerate {u v : ℤ} (h : (u, v) ∈ squareTestLiftPairs) :
    (¬ ∃ z : ℤ, movingLiftM u v = z) ∨ Int.natAbs v ∈ builtInFifthAbs := by
  rw [squareTestLiftPairs_eq] at h
  simp at h
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    left
    intro hm
    rcases hm with ⟨z, hz⟩
    norm_num [movingLiftM] at hz
    have hz' : ((6548 : ℚ) / 39) = z := by simpa using hz
    have hzden : (((6548 : ℚ) / 39).den = 1) := by
      rw [hz', Rat.den_intCast]
    have hdiv : (39 : ℤ) ∣ 6548 := by
      simpa using (Rat.den_div_intCast_eq_one_iff 6548 39 (by norm_num)).mp hzden
    norm_num at hdiv
  · rcases h with ⟨rfl, rfl⟩
    right
    native_decide
  · rcases h with ⟨rfl, rfl⟩
    right
    native_decide
  · rcases h with ⟨rfl, rfl⟩
    right
    native_decide
  · rcases h with ⟨rfl, rfl⟩
    right
    native_decide
  · rcases h with ⟨rfl, rfl⟩
    left
    intro hm
    rcases hm with ⟨z, hz⟩
    norm_num [movingLiftM] at hz
    have hz' : ((6548 : ℚ) / 39) = z := by simpa using hz
    have hzden : (((6548 : ℚ) / 39).den = 1) := by
      rw [hz', Rat.den_intCast]
    have hdiv : (39 : ℤ) ∣ 6548 := by
      simpa using (Rat.den_div_intCast_eq_one_iff 6548 39 (by norm_num)).mp hzden
    norm_num at hdiv

/-- In particular, no surviving integral lift pair simultaneously gives an
integral `m` and a new fifth square-`X` value outside `{18, 234, 514}`. -/
theorem squareTestLiftPairs_no_genuine_integral_fifth {u v : ℤ}
    (h : (u, v) ∈ squareTestLiftPairs) :
    ¬ ((∃ z : ℤ, movingLiftM u v = z) ∧ Int.natAbs v ∉ builtInFifthAbs) := by
  intro hbad
  have hdeg := squareTestLiftPairs_degenerate h
  rcases hdeg with hnonint | hv
  · exact hnonint hbad.1
  · exact hbad.2 hv
