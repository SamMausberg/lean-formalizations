import Mathlib
import FormalConjectures.Problems.Erdos.E885.Findings.Defs

/-!
# Fixed Finite Fibers and Pairwise Algebra

This file records finiteness results extracted from Section 2 of
`erdos885_notes.tex`. It does not formalize the full pair-fiber
parametrization or the same-parity counting formula from the notes.
-/

open Set Finset

set_option maxHeartbeats 800000

/-
**Corollary 2.2** (erdos885_notes.tex, §2.1, "finite-fiber lemma").
If `S ⊂ ℤ_{>0}` has at least two distinct elements, then `F(S)` is finite.

This follows from Theorem 2.1: for distinct `d, e ∈ S`, `F(S) ⊆ F({d, e})`,
and the latter is finite because each element corresponds to a same-parity
factorization of `e² - d²`.
-/
theorem fiberSet_finite_of_two_elements {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hne : d ≠ e) :
    Set.Finite (fiberSet {d, e}) := by
  -- Assume $n \in F(S)$, then $d, e \in D(n)$. By the square-discriminant reformulation, there exist $x, y$ with $x^2 = d^2 + 4n$ and $y^2 = e^2 + 4n$.
  have h_squares : ∀ n, n ∈ fiberSet {d, e} → ∃ x y : ℕ, x^2 = d^2 + 4 * n ∧ y^2 = e^2 + 4 * n := by
    intros n hn; obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a * b = n ∧ (b - a = d ∨ a - b = d) := by
      exact hn.2 ( Set.mem_insert _ _ ) |> fun ⟨ a, b, ha, hb, hab, h ⟩ => ⟨ a, b, ha, hb, hab, h ⟩
    obtain ⟨c, d', hcd⟩ : ∃ c d' : ℕ, 0 < c ∧ 0 < d' ∧ c * d' = n ∧ (d' - c = e ∨ c - d' = e) := by
      exact hn.2 ( Or.inr rfl ) |> fun ⟨ a, b, ha, hb, hab, h ⟩ => ⟨ a, b, ha, hb, hab, h ⟩ ;
    generalize_proofs at *; (
    rcases hab.2.2.2 with ( h | h ) <;> rcases hcd.2.2.2 with ( j | j ) <;> use b + a, d' + c <;> simp_all +decide [ Nat.sq_sub_sq ] <;> ring;
    · exact ⟨ by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : b - a ≠ 0 ) ) ), h, hab.2.2 ], by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : d' - c ≠ 0 ) ) ), j, hcd.2.2 ] ⟩ ;
    · exact ⟨ by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : b - a ≠ 0 ) ) ), h, hab.2.2 ], by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : c - d' ≠ 0 ) ) ), j, hcd.2.2 ] ⟩;
    · exact ⟨ by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : a - b ≠ 0 ) ) ), h, hab.2.2 ], by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : d' - c ≠ 0 ) ) ), j, hcd.2.2 ] ⟩;
    · exact ⟨ by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : a - b ≠ 0 ) ) ), h, hab.2.2 ], by nlinarith only [ Nat.sub_add_cancel ( le_of_lt ( Nat.lt_of_sub_ne_zero ( by linarith : c - d' ≠ 0 ) ) ), j, hcd.2.2 ] ⟩);
  -- Since $y^2 - x^2 = e^2 - d^2$, we have $(y - x)(y + x) = e^2 - d^2$. The number of factorizations of $e^2 - d^2$ is finite.
  have h_factorizations : ∃ M : ℕ, ∀ n ∈ fiberSet {d, e}, ∀ x y : ℕ, x^2 = d^2 + 4 * n → y^2 = e^2 + 4 * n → x ≤ M := by
    -- Since $y^2 - x^2 = e^2 - d^2$, we have $(y - x)(y + x) = e^2 - d^2$. The number of factorizations of $e^2 - d^2$ is finite, so $x$ and $y$ are bounded.
    have h_factorizations : ∃ M : ℕ, ∀ n ∈ fiberSet {d, e}, ∀ x y : ℕ, x^2 = d^2 + 4 * n → y^2 = e^2 + 4 * n → y - x ≤ M ∧ y + x ≤ M := by
      use e^2 - d^2 + e^2 + d^2;
      intro n hn x y hx hy; rcases le_total d e with h | h <;> simp_all +decide [ Nat.sq_sub_sq ] ;
      · constructor <;> nlinarith only [ Nat.sub_add_cancel h, hx, hy, show x < y from by nlinarith only [ hx, hy, h, show d < e from lt_of_le_of_ne h hne ] ];
      · constructor <;> nlinarith only [ h, hx, hy, show x > y from by nlinarith only [ h, hx, hy, show d > e from lt_of_le_of_ne h ( Ne.symm hne ) ] ];
    exact ⟨ h_factorizations.choose, fun n hn x y hx hy => by linarith [ h_factorizations.choose_spec n hn x y hx hy ] ⟩;
  obtain ⟨ M, hM ⟩ := h_factorizations; exact Set.finite_iff_bddAbove.mpr ⟨ M ^ 2, fun n hn => by obtain ⟨ x, y, hx, hy ⟩ := h_squares n hn; nlinarith [ hM n hn x y hx hy ] ⟩ ;

/-
Weakened consequence of Theorem 2.1 from the notes: for `d < e`, the pair-fiber
`F({d, e})` is finite. This declaration does not encode the full
parametrization-by-factorizations stated in the TeX.
-/
theorem pairFiber_finite {d e : ℕ} (hd : 0 < d) (hde : d < e) :
    Set.Finite (fiberSet {d, e}) := by
  apply fiberSet_finite_of_two_elements hd ( by linarith ) hde.ne

/-
Weakened same-parity consequence. Under the parity hypothesis from
Proposition 2.4, this file still only proves finiteness of the pair-fiber,
not the exact counting formula from the notes.
-/
theorem sameParity_fiber_finite {d e : ℕ} (hd : 0 < d) (hde : d < e)
    (hpar : d % 2 = e % 2) :
    Set.Finite (fiberSet {d, e}) := by
  exact?
