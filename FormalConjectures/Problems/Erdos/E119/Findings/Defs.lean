import Mathlib

/-!
# Erdős 119 Findings: Tail-Sum Definitions

This file packages the additive multiscale bookkeeping that appears throughout the
user-supplied source note indexed in `UserSource.md`.
-/

open scoped BigOperators

namespace Erdos119
namespace Findings

/--
Formalizes the cumulative tail quantity that appears in
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 1 ("Dyadic affine-rank rigidity theorem"), equation `(2)`,
and again in Section 2 ("Explicit error propagation across scales"), equation `(9)`.

It is written in zero-based form:
`tailSum top w j = ∑_{offset < top - j} w (j + offset)`.
-/
def tailSum {α : Type*} [AddCommMonoid α] (top : ℕ) (w : ℕ → α) (j : ℕ) : α :=
  Finset.sum (Finset.range (top - j)) fun offset => w (j + offset)

/--
Formalizes the same cumulative defect quantity as `tailSum`, but keeps the source note's
terminology `D_j` / `Δ_j` visible in Lean names; see
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 1, equation `(2)`, and Section 2, equation `(9)`.
-/
abbrev cumulativeDefect {α : Type*} [AddCommMonoid α] (top : ℕ) (w : ℕ → α) (j : ℕ) : α :=
  tailSum top w j

/--
Formalizes the terminal relation `D_{J₁} = 0` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 1, equation `(2)`, and Section 2, equation `(9)`.
-/
theorem tailSum_top {α : Type*} [AddCommMonoid α] (top : ℕ) (w : ℕ → α) :
    tailSum top w top = 0 := by
  simp [tailSum]

/--
Formalizes the vanishing of the cumulative defect beyond the top index, implicit in
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 1, equation `(2)`.
-/
theorem tailSum_eq_zero_of_le {α : Type*} [AddCommMonoid α] {top j : ℕ} (w : ℕ → α)
    (hj : top ≤ j) : tailSum top w j = 0 := by
  simp [tailSum, hj]

/--
Formalizes the one-step recursion `D_j = κ_j + D_{j+1}` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 2, equation `(9)`, in zero-based indexing.
-/
theorem tailSum_step {α : Type*} [AddCommMonoid α] {top j : ℕ} (w : ℕ → α)
    (hj : j < top) : tailSum top w j = w j + tailSum top w (j + 1) := by
  unfold tailSum
  have hsub : top - j = (top - (j + 1)) + 1 := by
    omega
  rw [hsub, Finset.sum_range_succ']
  simp [add_comm, add_left_comm]

/--
Formalizes the identity that extending the dyadic interval by one top scale adds exactly one
new local defect term to every earlier cumulative defect; compare
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 2, equation `(9)`.
-/
theorem tailSum_succ_of_lt {α : Type*} [AddCommMonoid α] {m j : ℕ} (w : ℕ → α)
    (hj : j < m) : tailSum (m + 1) w j = tailSum m w j + w m := by
  unfold tailSum
  have hsub : m + 1 - j = (m - j) + 1 := by
    omega
  rw [hsub, Finset.sum_range_succ]
  have hjm : j + (m - j) = m := by
    omega
  simp [hjm]

/--
Formalizes the zero-based version of the weighted identity
`∑_j Δ_j = ∑_k k δ_k` from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 7 ("Fixed-center coherence"), equation `(2)`.

The source is indexed from `1`, while this theorem is indexed from `0`, so the right-hand side
appears as `(k + 1) • w k`.
-/
theorem sum_tailSum_eq_sum_nsmul {α : Type*} [AddCommMonoid α] (w : ℕ → α) :
    ∀ m : ℕ,
      Finset.sum (Finset.range m) (fun j => tailSum m w j) =
        Finset.sum (Finset.range m) (fun k => (k + 1) • w k)
  | 0 => by simp [tailSum]
  | m + 1 => by
      have hshift :
          ∀ j ∈ Finset.range m, tailSum (m + 1) w j = tailSum m w j + w m := by
        intro j hj
        exact tailSum_succ_of_lt w (Finset.mem_range.mp hj)
      have hlast : tailSum (m + 1) w m = w m := by
        rw [tailSum_step w (Nat.lt_succ_self m), tailSum_top]
        simp
      calc
        Finset.sum (Finset.range (m + 1)) (fun j => tailSum (m + 1) w j)
            =
              Finset.sum (Finset.range m) (fun j => tailSum (m + 1) w j) + tailSum (m + 1) w m := by
                rw [Finset.sum_range_succ]
        _ =
              Finset.sum (Finset.range m) (fun j => tailSum m w j + w m) + tailSum (m + 1) w m := by
              congr 1
              exact Finset.sum_congr rfl hshift
        _ = Finset.sum (Finset.range m) (fun j => tailSum m w j) +
              Finset.sum (Finset.range m) (fun _j => w m) +
              tailSum (m + 1) w m := by
              rw [Finset.sum_add_distrib, add_assoc]
        _ = Finset.sum (Finset.range m) (fun k => (k + 1) • w k) + (m • w m) +
              tailSum (m + 1) w m := by
              rw [sum_tailSum_eq_sum_nsmul w m]
              simp
        _ = Finset.sum (Finset.range m) (fun k => (k + 1) • w k) + (m • w m) + w m := by
              rw [hlast]
        _ = Finset.sum (Finset.range m) (fun k => (k + 1) • w k) + ((m + 1) • w m) := by
              simp [succ_nsmul, add_assoc]
        _ = Finset.sum (Finset.range (m + 1)) (fun k => (k + 1) • w k) := by
              rw [Finset.sum_range_succ]

/--
Formalizes the linear accumulation bound from
`FormalConjectures/Problems/Erdos/E119/Findings/UserSource.md`,
Section 2, equation `(10)`, in the special case of natural-number local defects.
-/
theorem cumulativeDefect_le_of_bound {top j η : ℕ} {κ : ℕ → ℕ}
    (hκ : ∀ ℓ, j ≤ ℓ → ℓ < top → κ ℓ ≤ η) :
    cumulativeDefect top κ j ≤ (top - j) * η := by
  unfold cumulativeDefect tailSum
  calc
    Finset.sum (Finset.range (top - j)) (fun offset => κ (j + offset))
        ≤ Finset.sum (Finset.range (top - j)) (fun _offset => η) := by
            refine Finset.sum_le_sum ?_
            intro offset hoff
            have hoff' : offset < top - j := Finset.mem_range.mp hoff
            have hjtop : j ≤ top := by
              omega
            exact hκ (j + offset) (by omega) (by omega)
    _ = (top - j) * η := by simp

end Findings
end Erdos119
