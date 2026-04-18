import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# B-set Identity and Pairwise Finiteness

This file formalizes the basic `BSet` identities from Section 5 together with a
finiteness consequence for pairwise intersections. It does not formalize the
full iff parametrization theorem for `B(a) ∩ B(b)`.
-/

set_option maxHeartbeats 800000

/-- **Definition** (erdos885_notes.tex, §5.1).
`B(δ)` is the set of even positive integers `2z` such that `z² + δ` is a
perfect square. Equivalently, `2z ∈ B(δ)` iff `δ = x(x + 2z)` for some `x > 0`. -/
def BSet (δ : ℕ) : Set ℕ :=
  {c : ℕ | ∃ z : ℕ, 0 < z ∧ c = 2 * z ∧ ∃ r : ℕ, r * r = z * z + δ}

/-
**Lemma 5.1** (erdos885_notes.tex, §5.1, "exact B-set identity").
For `δ, z > 0`, `2z ∈ B(δ)` iff `z² + δ` is a perfect square, iff
`δ = x(x + 2z)` for some `x > 0`.
-/
theorem BSet_iff {δ z : ℕ} (hδ : 0 < δ) (hz : 0 < z) :
    2 * z ∈ BSet δ ↔ ∃ r : ℕ, r * r = z * z + δ := by
  exact ⟨ fun ⟨ w, hw₁, hw₂, hw₃ ⟩ => by aesop, fun ⟨ r, hr ⟩ => ⟨ z, hz, rfl, ⟨ r, hr ⟩ ⟩ ⟩

/-
**Lemma 5.1** (continued). The equivalent formulation: `2z ∈ B(δ)` iff
`δ = x * (x + 2 * z)` for some `x > 0`.
-/
theorem BSet_iff' {δ z : ℕ} (hδ : 0 < δ) (hz : 0 < z) :
    2 * z ∈ BSet δ ↔ ∃ x : ℕ, 0 < x ∧ δ = x * (x + 2 * z) := by
  refine' ⟨ fun ⟨ w, hw₁, hw₂, r, hr ⟩ => _, _ ⟩;
  · exact ⟨ r - z, Nat.sub_pos_of_lt ( by nlinarith ), by nlinarith [ Nat.sub_add_cancel ( by nlinarith : z ≤ r ) ] ⟩;
  · rintro ⟨ x, hx, rfl ⟩;
    exact ⟨ z, hz, rfl, x + z, by ring ⟩

/-
Weakened consequence of Theorem 5.2 from the notes: for fixed `0 < a < b`, the
intersection `B(a) ∩ B(b)` is finite. The full iff parametrization by
factorizations of `b - a` is not encoded here.
-/
theorem BSet_inter_finite {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Set.Finite (BSet a ∩ BSet b) := by
  -- By Lemma 5.1, elements of BSet a ∩ BSet b are values 2z where z² + a = m² and z² + b = n² for some m, n. Then n² - m² = b - a, so (n-m)(n+m) = b - a.
  have h_eq : ∀ z : ℕ, z > 0 → (2 * z ∈ BSet a ∧ 2 * z ∈ BSet b) → ∃ m n : ℕ, n^2 - m^2 = b - a ∧ m^2 = z^2 + a ∧ n^2 = z^2 + b := by
    simp +zetaDelta at *;
    rintro z hz ⟨ m, hm₁, hm₂, n, hn ⟩ ⟨ p, hp₁, hp₂, q, hq ⟩;
    exact ⟨ n, q, Nat.sub_eq_of_eq_add <| by nlinarith only [ hn, hq, Nat.sub_add_cancel hab.le, show z = m by linarith, show z = p by linarith ], by nlinarith only [ hn, hq, Nat.sub_add_cancel hab.le, show z = m by linarith, show z = p by linarith ], by nlinarith only [ hn, hq, Nat.sub_add_cancel hab.le, show z = m by linarith, show z = p by linarith ] ⟩;
  -- Since $b - a$ is fixed, there are finitely many factorizations, and each determines $n$, $m$, hence $z$.
  have h_finite : ∃ M : ℕ, ∀ z : ℕ, z > 0 → (2 * z ∈ BSet a ∧ 2 * z ∈ BSet b) → z ≤ M := by
    use b - a + a + b + 1;
    intro z hz h; obtain ⟨ m, n, hmn, hm, hn ⟩ := h_eq z hz h; rw [ Nat.sq_sub_sq ] at hmn;
    -- Since $n - m \geq 1$, we have $n + m \leq b - a$.
    have hnm_le : n + m ≤ b - a := by
      exact Nat.le_of_dvd ( Nat.sub_pos_of_lt hab ) ( hmn ▸ dvd_mul_right _ _ );
    nlinarith only [ hm, hn, hnm_le ];
  obtain ⟨ M, hM ⟩ := h_finite;
  exact Set.finite_iff_bddAbove.mpr ⟨ 2 * M, fun x hx => by obtain ⟨ z, hz₁, rfl, hz₂ ⟩ := hx.1; linarith [ hM z hz₁ ⟨ hx.1, hx.2 ⟩ ] ⟩

/-- **Corollary 5.3** (erdos885_notes.tex, §5.2).
For fixed `a < b`, the set `B(a) ∩ B(b)` is finite, with a divisor-type bound
controlled by the factorizations of `b - a`. -/
theorem BSet_inter_finite_corollary {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Set.Finite (BSet a ∩ BSet b) := BSet_inter_finite ha hab
