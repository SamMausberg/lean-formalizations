import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.SquareDiscriminant

/-!
# Exact Descent Cores for E885 Obstruction Routes

This file formalizes three exact algebraic cores used in the recent obstruction
notes:

1. a one-step descent for same-anchor factor-difference problems;
2. the anchored three-shift reduction to a rigid three-square system;
3. the hidden affine parameter in the `3`-row transfer system.

The statements here are deliberately exact but lightweight: they isolate the
reusable algebraic equivalences without trying to encode the larger narrative
claims around packets, spectra, or global caps.
-/

/-! ## 1. Exact one-step descent for common factor differences -/

/--
If `x² = d² + 4n` and `t² = d² + 4M`, then asking whether `t` is a common
factor difference of `n` is equivalent to asking whether `x` is a factor
difference of `M`.

This is the pointwise core of the same-parity descent used to turn a
multi-support witness into a lower-level common-`D` intersection problem.
-/
theorem factorDiff_transfer_iff {d n M t x : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hM : 0 < M)
    (hx : x * x = d * d + 4 * n)
    (ht : t * t = d * d + 4 * M) :
    t ∈ factorDiffSet n ↔ x ∈ factorDiffSet M := by
  have hx_pos : 0 < x := by
    nlinarith [hx, hd, hn]
  have ht_pos : 0 < t := by
    nlinarith [ht, hd, hM]
  constructor
  · intro ht_mem
    rcases (square_discriminant_iff ht_pos hn).mp ht_mem with ⟨y, hty, hy⟩
    refine (square_discriminant_iff hx_pos hM).mpr ?_
    refine ⟨y, ?_, ?_⟩
    · nlinarith [hy, hx, hM]
    · nlinarith [hy, hx, ht]
  · intro hx_mem
    rcases (square_discriminant_iff hx_pos hM).mp hx_mem with ⟨y, hxy, hy⟩
    refine (square_discriminant_iff ht_pos hn).mpr ?_
    refine ⟨y, ?_, ?_⟩
    · nlinarith [hy, hx, hn]
    · nlinarith [hy, hx, ht]

/--
Matrix form of `factorDiff_transfer_iff`: once every support `Nᵢ` and every
target difference `tⱼ` is measured from the same anchor `d`, the full
incidence matrix of common factor-difference memberships is transported
exactly to the lower-level matrix `xᵢ ∈ D(Mⱼ)`.
-/
theorem common_factorDiff_matrix_iff {ι κ : Sort*} {d : ℕ}
    {N : ι → ℕ} {M : κ → ℕ} {x : ι → ℕ} {t : κ → ℕ}
    (hd : 0 < d)
    (hN : ∀ i, 0 < N i)
    (hM : ∀ j, 0 < M j)
    (hx : ∀ i, x i * x i = d * d + 4 * N i)
    (ht : ∀ j, t j * t j = d * d + 4 * M j) :
    (∀ i j, t j ∈ factorDiffSet (N i)) ↔ ∀ i j, x i ∈ factorDiffSet (M j) := by
  constructor <;> intro h i j
  · exact (factorDiff_transfer_iff hd (hN i) (hM j) (hx i) (ht j)).mp (h i j)
  · exact (factorDiff_transfer_iff hd (hN i) (hM j) (hx i) (ht j)).mpr (h i j)

/-! ## 2. Anchored three-shift reduction -/

/-- The anchored three-shift square condition at a fixed positive `z`. -/
def AnchoredTriple (a b c z : ℕ) : Prop :=
  ∃ x y w : ℕ,
    x * x = z * z + a ∧
    y * y = z * z + b ∧
    w * w = z * z + c

/- 
Exact reduction of the anchored three-shift square problem at a fixed positive
`z` to a rigid three-square system with center parameter `M`.

This is the formal core behind the divisor/Pell reformulation: the middle
square root determines `M = 2y`, and conversely the center equation forces all
roots to have the required parity.
-/
set_option maxHeartbeats 800000 in
-- The backward direction uses several nonlinear arithmetic/parity steps on `ℕ`.
theorem anchoredTriple_iff_three_square_system {a b c z : ℕ}
    (_hz : 0 < z) (hab : a < b) (hbc : b < c) :
    AnchoredTriple a b c z ↔
      ∃ M u v : ℕ,
        M * M = u * u + 4 * (b - a) ∧
        M * M = (2 * z) * (2 * z) + 4 * b ∧
        v * v = M * M + 4 * (c - b) := by
  constructor
  · rintro ⟨x, y, w, hx, hy, hw⟩
    refine ⟨2 * y, 2 * x, 2 * w, ?_, ?_, ?_⟩
    · have hab' : a + (b - a) = b := Nat.add_sub_of_le hab.le
      have hx2 : (2 * x) * (2 * x) = 4 * (z * z + a) := by
        nlinarith [hx]
      have hy2 : (2 * y) * (2 * y) = 4 * (z * z + b) := by
        nlinarith [hy]
      have hgap : 4 * (z * z + b) = 4 * (z * z + a) + 4 * (b - a) := by
        nlinarith [hab']
      nlinarith [hx2, hy2, hgap]
    · have hy2 : (2 * y) * (2 * y) = 4 * (z * z + b) := by
        nlinarith [hy]
      nlinarith [hy2]
    · have hbc' : b + (c - b) = c := Nat.add_sub_of_le hbc.le
      have hy2 : (2 * y) * (2 * y) = 4 * (z * z + b) := by
        nlinarith [hy]
      have hw2 : (2 * w) * (2 * w) = 4 * (z * z + c) := by
        nlinarith [hw]
      have hgap : 4 * (z * z + c) = 4 * (z * z + b) + 4 * (c - b) := by
        nlinarith [hbc']
      nlinarith [hy2, hw2, hgap]
  · rintro ⟨M, u, v, hMu, hMz, hv⟩
    have hMM_even : Even (M * M) := by
      refine ⟨2 * (z * z + b), ?_⟩
      nlinarith [hMz]
    have hM_even : Even M := by
      simpa [Nat.even_mul] using hMM_even
    have huu : u * u = 4 * (z * z + a) := by
      have hab' : a + (b - a) = b := Nat.add_sub_of_le hab.le
      nlinarith [hMu, hMz, hab']
    have hvv : v * v = 4 * (z * z + c) := by
      have hbc' : b + (c - b) = c := Nat.add_sub_of_le hbc.le
      nlinarith [hv, hMz, hbc']
    have huu_even : Even (u * u) := by
      refine ⟨2 * (z * z + a), ?_⟩
      nlinarith [huu]
    have hvv_even : Even (v * v) := by
      refine ⟨2 * (z * z + c), ?_⟩
      nlinarith [hvv]
    have hu_even : Even u := by
      simpa [Nat.even_mul] using huu_even
    have hv_even : Even v := by
      simpa [Nat.even_mul] using hvv_even
    refine ⟨u / 2, M / 2, v / 2, ?_, ?_, ?_⟩
    · have hu2 : 2 * (u / 2) = u := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel hu_even.two_dvd)
      have hu_sq_div : u * u = 4 * ((u / 2) * (u / 2)) := by
        calc
          u * u = (2 * (u / 2)) * (2 * (u / 2)) := by rw [hu2]
          _ = 4 * ((u / 2) * (u / 2)) := by ring
      nlinarith [hu2, huu, hu_sq_div]
    · have hM2 : 2 * (M / 2) = M := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel hM_even.two_dvd)
      have hM_sq_div : M * M = 4 * ((M / 2) * (M / 2)) := by
        calc
          M * M = (2 * (M / 2)) * (2 * (M / 2)) := by rw [hM2]
          _ = 4 * ((M / 2) * (M / 2)) := by ring
      nlinarith [hM2, hMz, hM_sq_div]
    · have hv2 : 2 * (v / 2) = v := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel hv_even.two_dvd)
      have hv_sq_div : v * v = 4 * ((v / 2) * (v / 2)) := by
        calc
          v * v = (2 * (v / 2)) * (2 * (v / 2)) := by rw [hv2]
          _ = 4 * ((v / 2) * (v / 2)) := by ring
      nlinarith [hv2, hvv, hv_sq_div]

/-! ## 3. Hidden affine parameter in the transfer system -/

/--
The `3`-row transfer system is equivalent to the existence of a single affine
parameter `λ` fitting the cumulative gaps.

This is the exact invariant behind the cumulative-gap reformulation from the
notes. The proof is over `ℚ`, since the parameter is naturally rational.
-/
theorem transfer_system_iff_common_parameter {A B C u v w : ℚ}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (A * u - B * v = u * v * (u + v) ∧
      C * v - A * w = v * w * (v + w)) ↔
      ∃ lam : ℚ,
        B = u * (u + lam) ∧
        B + A = (u + v) * (u + v + lam) ∧
        B + A + C = (u + v + w) * (u + v + w + lam) := by
  constructor
  · rintro ⟨hAB, hCA⟩
    refine ⟨B / u - u, ?_, ?_, ?_⟩
    · field_simp [hu]
      ring
    · have hA : A = v * (B / u + u + v) := by
        apply (mul_right_cancel₀ hu)
        calc
          A * u = B * v + u * v * (u + v) := by nlinarith [hAB]
          _ = (v * (B / u + u + v)) * u := by
            field_simp [hu]
            ring
      calc
        B + A = B + v * (B / u + u + v) := by rw [hA]
        _ = (u + v) * (u + v + (B / u - u)) := by
          field_simp [hu]
          ring
    · have hA : A = v * (B / u + u + v) := by
        apply (mul_right_cancel₀ hu)
        calc
          A * u = B * v + u * v * (u + v) := by nlinarith [hAB]
          _ = (v * (B / u + u + v)) * u := by
            field_simp [hu]
            ring
      have hC : C = w * (A / v + v + w) := by
        apply (mul_right_cancel₀ hv)
        calc
          C * v = A * w + v * w * (v + w) := by nlinarith [hCA]
          _ = (w * (A / v + v + w)) * v := by
            field_simp [hv]
            ring
      calc
        B + A + C = (B + A) + w * (A / v + v + w) := by rw [hC]
        _ = (u + v + w) * (u + v + w + (B / u - u)) := by
          rw [hA]
          field_simp [hu, hv]
          ring
  · rintro ⟨lam, h1, h2, h3⟩
    have hA : A = v * (lam + 2 * u + v) := by
      nlinarith [h1, h2]
    have hC : C = w * (lam + 2 * u + 2 * v + w) := by
      nlinarith [h2, h3]
    constructor
    · calc
        A * u - B * v = (v * (lam + 2 * u + v)) * u - (u * (u + lam)) * v := by
          rw [h1, hA]
        _ = u * v * (u + v) := by ring
    · calc
        C * v - A * w =
            (w * (lam + 2 * u + 2 * v + w)) * v - (v * (lam + 2 * u + v)) * w := by
              rw [hA, hC]
        _ = v * w * (v + w) := by ring
