import Mathlib

set_option linter.style.openClassical false

namespace FormalConjectures.Problems.Erdos.E20

open scoped Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# One-Counter Holonomy

This file packages the finite directed-graph core from the pasted E20 notes:

* a finite quiver with an integer drift on every arrow;
* a concrete profitable-split witness package;
* conditional lemmas showing that an explicit potential telescopes path drift and bounds it.

The file stays on the proved side of the boundary: there are no global holonomy predicates, no
statement-only targets, and no unproved collapse claims.
-/

section Core

variable {V : Type*} [Quiver V] [Fintype V] [DecidableEq V]

/-- A finite directed graph with an integer drift attached to each arrow. -/
structure DriftQuiver (V : Type*) [Quiver V] where
  drift : ∀ {u v : V}, (u ⟶ v) → ℤ

namespace DriftQuiver

variable {V : Type*} [Quiver V] [Fintype V] [DecidableEq V]
variable (G : DriftQuiver V)

/-- The integer drift accumulated along a directed path. -/
def pathDrift : ∀ {u v : V}, Quiver.Path u v → ℤ :=
  Quiver.Path.addWeight (fun {u v : V} (e : u ⟶ v) => G.drift e)

@[simp] theorem pathDrift_nil {u : V} :
    G.pathDrift (Quiver.Path.nil : Quiver.Path u u) = 0 := by
  simp [pathDrift]

@[simp] theorem pathDrift_cons {u v w : V} (p : Quiver.Path u v) (e : v ⟶ w) :
    G.pathDrift (p.cons e) = G.pathDrift p + G.drift e := by
  simp [pathDrift]

/-- A profitable-split witness. The `witnessBound` tag records the bounded-scale part of the note
without committing to a particular normalization. -/
structure ProfitableSplitWitness where
  base : V
  cycle : Quiver.Path base base
  cycle_length_pos : 0 < cycle.length
  cycle_drift_pos : 0 < G.pathDrift cycle
  witnessBound : ℕ

theorem profitableSplitWitness_length_pos (w : G.ProfitableSplitWitness) :
    0 < w.cycle.length :=
  w.cycle_length_pos

theorem profitableSplitWitness_drift_pos (w : G.ProfitableSplitWitness) :
    0 < G.pathDrift w.cycle :=
  w.cycle_drift_pos

/-- If the edge drift is given by an explicit potential, then every path drift is the endpoint
potential difference. -/
lemma pathDrift_eq_endpointDiff (φ : V → ℤ)
    (hφ : ∀ ⦃u v : V⦄ (e : u ⟶ v), G.drift e = φ v - φ u) :
    ∀ ⦃u v : V⦄ (p : Quiver.Path u v), G.pathDrift p = φ v - φ u := by
  intro u v p
  induction p with
  | nil =>
      simp [pathDrift]
  | @cons b c q e ih =>
      calc
        G.pathDrift (q.cons e) = G.pathDrift q + G.drift e := by
          simp [pathDrift]
        _ = (φ b - φ u) + (φ c - φ b) := by
          rw [ih, hφ e]
        _ = φ c - φ u := by
          ring

/-- An explicit potential kills closed path drift. -/
theorem noCycleDrift_of_potential (φ : V → ℤ)
    (hφ : ∀ ⦃u v : V⦄ (e : u ⟶ v), G.drift e = φ v - φ u) :
    ∀ {u : V} (p : Quiver.Path u u), G.pathDrift p = 0 := by
  intro u p
  have hEq := G.pathDrift_eq_endpointDiff φ hφ p
  simpa using hEq

/-- An explicit potential forces a finite bound on the drift of every path. -/
theorem pathDrift_bounded_of_potential (φ : V → ℤ)
    (hφ : ∀ ⦃u v : V⦄ (e : u ⟶ v), G.drift e = φ v - φ u) :
    ∃ B : ℕ, ∀ ⦃u v : V⦄ (p : Quiver.Path u v), (G.pathDrift p).natAbs ≤ B := by
  let M : ℕ := Finset.univ.sup fun x : V => (φ x).natAbs
  refine ⟨2 * M, ?_⟩
  intro u v p
  have hEq : G.pathDrift p = φ v - φ u := by
    exact G.pathDrift_eq_endpointDiff φ hφ p
  rw [hEq]
  have hu : (φ u).natAbs ≤ M := by
    simpa [M] using
      (Finset.le_sup (s := (Finset.univ : Finset V)) (f := fun x : V => (φ x).natAbs)
        (b := u) (by simp))
  have hv : (φ v).natAbs ≤ M := by
    simpa [M] using
      (Finset.le_sup (s := (Finset.univ : Finset V)) (f := fun x : V => (φ x).natAbs)
        (b := v) (by simp))
  have hsum : (φ v).natAbs + (φ u).natAbs ≤ M + M := by
    omega
  calc
    (φ v - φ u).natAbs ≤ (φ v).natAbs + (φ u).natAbs := Int.natAbs_sub_le _ _
    _ ≤ M + M := hsum
    _ = 2 * M := by
      omega

end DriftQuiver

end Core

end FormalConjectures.Problems.Erdos.E20
