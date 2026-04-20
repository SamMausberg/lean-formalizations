import FormalConjectures.Problems.Erdos.E20.Families.ExplicitKernels

namespace FormalConjectures.Problems.Erdos.E20

open scoped BigOperators

/-!
# Terminal-Kernel Reduction Bounds

This file packages the honest part of the user's terminal-kernel note in a form that matches the
current E20 library.

The key point is that the current development formalizes one-round leaf stripping via
`strippedSupportFamily`, together with explicit terminal examples such as block products and
transversal kernels. What is *not* yet formalized here is the global theorem that every
`k`-sunflower-free `n`-uniform family loses at most a factor `(k - 1)^n` when reduced to its exact
terminal kernel.

Accordingly, this file isolates that reduction as an explicit hypothesis
`HasTerminalKernelReductionAt k n H` and proves the consequences that really do follow from it:

* an abstract reduction lemma for any class of terminal kernels carrying an `A^m` size bound;
* concrete corollaries for terminal transversal kernels and terminal block products.
-/

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The explicit reduction hypothesis used in the terminal-kernel note:
the original family is at most `(k - 1)^n` times as large as its one-round stripped terminal
kernel.  Since iterated terminal reduction is not yet formalized in the library, we package that
factor as an assumption. -/
def HasTerminalKernelReductionAt (k n : ℕ) (H : Finset (Finset α)) : Prop :=
  (H.card : ℝ) ≤ ((k - 1 : ℝ) ^ n) * (strippedSupportFamily H).card

/-- A class of terminal kernels carries an exponential base `A` at order `k` if every
`k`-sunflower-free `m`-uniform member of the class has size at most `A^m`. -/
def HasTerminalKernelClassBound (C : Finset (Finset α) → Prop) (k : ℕ) (A : ℝ) : Prop :=
  ∀ ⦃m : ℕ⦄ ⦃K : Finset (Finset α)⦄,
    C K → IsRUniform K m → SunflowerFree K k → (K.card : ℝ) ≤ A ^ m

/-- Abstract terminal-kernel reduction lemma.

If an `n`-uniform family `H` satisfies the exact terminal-kernel reduction factor `(k - 1)^n`,
and its stripped terminal kernel has rank `m ≤ n` and size at most `A^m`, then `H` is bounded by
`((k - 1) A)^n`. -/
theorem terminalKernelReduction_bound
    {H : Finset (Finset α)} {n m k : ℕ} {A : ℝ}
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hmn : m ≤ n) (hA : 1 ≤ A)
    (hKbound : ((strippedSupportFamily H).card : ℝ) ≤ A ^ m) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * A) ^ n) := by
  unfold HasTerminalKernelReductionAt at hred
  have hk_real : (1 : ℝ) ≤ k := by
    exact_mod_cast hk
  have hk_nonneg : 0 ≤ (k - 1 : ℝ) := by
    exact sub_nonneg.mpr hk_real
  have hkpow_nonneg : 0 ≤ ((k - 1 : ℝ) ^ n) := pow_nonneg hk_nonneg n
  have hKbound' : ((strippedSupportFamily H).card : ℝ) ≤ A ^ n := by
    calc
      ((strippedSupportFamily H).card : ℝ) ≤ A ^ m := hKbound
      _ ≤ A ^ n := pow_le_pow_right₀ hA hmn
  calc
    (H.card : ℝ) ≤ ((k - 1 : ℝ) ^ n) * (strippedSupportFamily H).card := hred
    _ ≤ ((k - 1 : ℝ) ^ n) * A ^ n := mul_le_mul_of_nonneg_left hKbound' hkpow_nonneg
    _ = (((k - 1 : ℝ) * A) ^ n) := by rw [← mul_pow]

/-- Universal reduction lemma for any controlled class of exact terminal kernels. -/
theorem terminalKernelReduction_bound_of_class
    {H : Finset (Finset α)} {n m k : ℕ} {A : ℝ}
    {C : Finset (Finset α) → Prop}
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hclass : C (strippedSupportFamily H))
    (hKuniform : IsRUniform (strippedSupportFamily H) m)
    (hKfree : SunflowerFree (strippedSupportFamily H) k)
    (hmn : m ≤ n) (hA : 1 ≤ A)
    (hbound : HasTerminalKernelClassBound C k A) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * A) ^ n) :=
  terminalKernelReduction_bound hk hred hmn hA (hbound hclass hKuniform hKfree)

section Transversal

variable {G : Type*} [DecidableEq G] [Fintype G]

/-- Transversal-kernel corollary.

If the stripped terminal kernel is a transversal family coming from a code `C` of length `m`, and
`|C| ≤ A^m`, then the exact terminal-kernel reduction hypothesis yields the bound
`|H| ≤ ((k - 1) A)^n`. -/
theorem terminalKernelReduction_bound_of_transversalKernel
    {n m k : ℕ} {A : ℝ}
    (H : Finset (Finset (Fin m × G)))
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    {C : Finset (Fin m → G)}
    (hkernel : strippedSupportFamily H = transversalFamily (G := G) C)
    (hmn : m ≤ n) (hA : 1 ≤ A)
    (hCbound : (C.card : ℝ) ≤ A ^ m) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * A) ^ n) := by
  refine terminalKernelReduction_bound hk hred hmn hA ?_
  simpa [hkernel] using hCbound

end Transversal

section BlockProducts

/-- Fixed-width block-product corollary.

If the stripped terminal kernel is the full block-product family on `m` blocks of width `q`, then
the exact terminal-kernel reduction hypothesis yields `|H| ≤ ((k - 1) q)^n`. -/
theorem terminalKernelReduction_bound_of_blockProductKernel
    {n m q k : ℕ}
    (H : Finset (Finset (Fin m × Fin q)))
    (hk : 1 ≤ k) (hred : HasTerminalKernelReductionAt k n H)
    (hkernel : strippedSupportFamily H = blockProductFamily m q)
    (hmn : m ≤ n) (hq : 1 ≤ q) :
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * q) ^ n) := by
  refine terminalKernelReduction_bound (H := H) (n := n) (m := m) (k := k)
    (A := q) hk hred hmn (by exact_mod_cast hq) ?_
  rw [hkernel, card_blockProductFamily]
  exact_mod_cast (le_rfl : q ^ m ≤ q ^ m)

/-- Specialization of the fixed-width block-product corollary to the maximal allowed width
`q = k - 1`, giving the base `(k - 1)^2`. -/
theorem terminalKernelReduction_bound_of_maxWidthBlockProductKernel
    {n m k : ℕ}
    (H : Finset (Finset (Fin m × Fin (k - 1))))
    (hk : 2 ≤ k)
    (hred : HasTerminalKernelReductionAt k n H)
    (hkernel : strippedSupportFamily H = blockProductFamily m (k - 1))
    (hmn : m ≤ n) :
    (H.card : ℝ) ≤ (k - 1 : ℝ) ^ (2 * n) := by
  have hk1 : 1 ≤ k - 1 := by omega
  have hk' : 1 ≤ k := by omega
  have hbase :
      (H.card : ℝ) ≤ (((k - 1 : ℝ) * ((k - 1 : ℕ) : ℝ)) ^ n) :=
    terminalKernelReduction_bound_of_blockProductKernel
      (H := H) (k := k) hk' hred hkernel hmn hk1
  have hcast : ((k - 1 : ℕ) : ℝ) = (k - 1 : ℝ) := by
    rw [Nat.cast_sub hk']
    norm_num
  calc
    (H.card : ℝ) ≤ (((k - 1 : ℝ) * ((k - 1 : ℕ) : ℝ)) ^ n) := hbase
    _ = (((k - 1 : ℝ) * (k - 1 : ℝ)) ^ n) := by
      simp [hcast]
    _ = (((k - 1 : ℝ) ^ 2) ^ n) := by
      rw [pow_two]
    _ = (k - 1 : ℝ) ^ (2 * n) := by
      symm
      simpa [pow_two] using (pow_mul (k - 1 : ℝ) 2 n)

end BlockProducts

end FormalConjectures.Problems.Erdos.E20
