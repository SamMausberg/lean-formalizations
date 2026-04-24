import FormalConjectures.Problems.Erdos.E61.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Exact affine cells over `F₂`

This file supplies the finite linear-algebra package behind `thm:affine-cell`.
An exact affine cell is represented as the coset `η + W` of a finite-dimensional
subspace.  The statements are phrased for linear functionals, with the `F₂`
cardinality specialization used by the paper.
-/

namespace Erdos61

open Finset

/-- The field with two elements used for the affine-cell statements. -/
abbrev F₂ := ZMod 2

/-- The exact affine cell `η + W`, represented as a finite set. -/
noncomputable def affineCell {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [DecidableEq M] (η : M) (W : Submodule K M) [Fintype W] : Finset M :=
  Finset.image (fun w : W => η + (w : M)) (Finset.univ : Finset W)

theorem mem_affineCell_iff {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [DecidableEq M] {η x : M} {W : Submodule K M} [Fintype W] :
    x ∈ affineCell η W ↔ x - η ∈ W := by
  classical
  constructor
  · intro hx
    rw [affineCell] at hx
    rcases mem_image.mp hx with ⟨w, _hw, rfl⟩
    have h : η + (w : M) - η = (w : M) := by module
    rw [h]
    exact w.2
  · intro hx
    rw [affineCell]
    refine mem_image.mpr ⟨⟨x - η, hx⟩, mem_univ _, ?_⟩
    module

/-- The cardinality of an exact affine cell is the cardinality of its direction. -/
theorem affineCell_card {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [DecidableEq M] (η : M) (W : Submodule K M) [Fintype W] :
    (affineCell η W).card = Fintype.card W := by
  classical
  rw [affineCell, card_image_of_injOn]
  · simp
  · intro x _hx y _hy hxy
    exact Subtype.ext (add_left_cancel hxy)

/-- Over `F₂`, an exact affine cell has size `2^dim W`. -/
theorem affineCell_card_eq_pow_finrank {M : Type*} [AddCommGroup M] [Module F₂ M]
    [DecidableEq M] (η : M) (W : Submodule F₂ M) [Fintype W] :
    (affineCell η W).card = 2 ^ Module.finrank F₂ W := by
  classical
  calc
    (affineCell η W).card = Fintype.card W := affineCell_card η W
    _ = Fintype.card F₂ ^ Module.finrank F₂ W := Module.card_eq_pow_finrank
    _ = 2 ^ Module.finrank F₂ W := by rw [ZMod.card]

/--
Trace-image bound from `thm:affine-cell(iii)`: any map out of an exact affine
cell has image size at most `2^dim W`.  The paper's trace map is one such map.
-/
theorem affineCell_image_card_le_pow_finrank {M γ : Type*}
    [AddCommGroup M] [Module F₂ M] [DecidableEq M] [DecidableEq γ]
    (η : M) (W : Submodule F₂ M) [Fintype W] (f : M → γ) :
    ((affineCell η W).image f).card ≤ 2 ^ Module.finrank F₂ W := by
  classical
  calc
    ((affineCell η W).image f).card ≤ (affineCell η W).card := card_image_le
    _ = 2 ^ Module.finrank F₂ W := affineCell_card_eq_pow_finrank η W

/--
Coordinate/fiber form of `thm:affine-cell(i)`: a nonempty fiber of two linear
functionals inside `η + W` is itself an exact affine cell, with direction
`W ∩ ker L₁ ∩ ker L₂`.
-/
theorem affineCell_pairFiber_eq {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [DecidableEq M] [DecidableEq K]
    (η x₀ : M) (W : Submodule K M) [Fintype W]
    (L₁ L₂ : M →ₗ[K] K)
    [Fintype ↥(W ⊓ LinearMap.ker L₁ ⊓ LinearMap.ker L₂)]
    (hx₀ : x₀ ∈ affineCell η W) :
    (affineCell η W).filter (fun x => L₁ x = L₁ x₀ ∧ L₂ x = L₂ x₀) =
      affineCell x₀ (W ⊓ LinearMap.ker L₁ ⊓ LinearMap.ker L₂) := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_filter] at hx
    rw [mem_affineCell_iff]
    have hxW : x - η ∈ W := mem_affineCell_iff.mp hx.1
    have hx₀W : x₀ - η ∈ W := mem_affineCell_iff.mp hx₀
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hsub : (x - η) - (x₀ - η) ∈ W := W.sub_mem hxW hx₀W
      convert hsub using 1
      abel
    · change L₁ (x - x₀) = 0
      rw [map_sub, hx.2.1, sub_self]
    · change L₂ (x - x₀) = 0
      rw [map_sub, hx.2.2, sub_self]
  · intro hx
    rw [mem_filter]
    have hdir : x - x₀ ∈ W ⊓ LinearMap.ker L₁ ⊓ LinearMap.ker L₂ :=
      mem_affineCell_iff.mp hx
    have hx₀W : x₀ - η ∈ W := mem_affineCell_iff.mp hx₀
    constructor
    · rw [mem_affineCell_iff]
      have hW : x - x₀ ∈ W := hdir.1.1
      have hsum : (x - x₀) + (x₀ - η) ∈ W := W.add_mem hW hx₀W
      convert hsum using 1
      abel
    · constructor
      · have hker : x - x₀ ∈ LinearMap.ker L₁ := hdir.1.2
        rw [LinearMap.mem_ker, map_sub] at hker
        exact sub_eq_zero.mp hker
      · have hker : x - x₀ ∈ LinearMap.ker L₂ := hdir.2
        rw [LinearMap.mem_ker, map_sub] at hker
        exact sub_eq_zero.mp hker

/-- If the fiber direction is a proper subspace, its dimension drops. -/
theorem affineCell_pairFiber_finrank_lt_of_direction_lt
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (W : Submodule K M) [Module.Finite K W] (L₁ L₂ : M →ₗ[K] K)
    (hdir : W ⊓ LinearMap.ker L₁ ⊓ LinearMap.ker L₂ < W) :
    Module.finrank K ↥(W ⊓ LinearMap.ker L₁ ⊓ LinearMap.ker L₂ : Submodule K M) <
      Module.finrank K W :=
  Submodule.finrank_lt_finrank_of_lt hdir

/--
Among the four fibers of any two-bit map on an affine cell, one has size at
least one quarter of the cell.
-/
theorem affineCell_four_fiber_large {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] [DecidableEq M] (η : M) (W : Submodule K M) [Fintype W]
    (c : M → Bool × Bool) :
    ∃ b : Bool × Bool,
      (affineCell η W).card ≤ 4 * ((affineCell η W).filter fun x => c x = b).card := by
  classical
  have hcell_nonempty : (affineCell η W).Nonempty := by
    refine ⟨η + (0 : W), ?_⟩
    rw [affineCell]
    exact mem_image.mpr ⟨0, mem_univ _, rfl⟩
  rcases exists_large_fiber (affineCell η W) c hcell_nonempty with ⟨b, _hb, hlarge⟩
  have himage : ((affineCell η W).image c).card ≤ 4 := by
    calc
      ((affineCell η W).image c).card ≤ Fintype.card (Bool × Bool) :=
        card_le_univ _
      _ = 4 := by decide
  refine ⟨b, ?_⟩
  calc
    (affineCell η W).card ≤ ((affineCell η W).image c).card *
        (fiberOver (affineCell η W) c b).card := hlarge
    _ ≤ 4 * (fiberOver (affineCell η W) c b).card :=
      Nat.mul_le_mul_right _ himage
    _ = 4 * ((affineCell η W).filter fun x => c x = b).card := rfl

/-- Dual delta criterion used in the affine-cell ladder proof. -/
theorem linearIndependent_of_dual_delta {K M ι : Type*}
    [Field K] [AddCommGroup M] [Module K M] [Finite ι] [DecidableEq ι]
    (d : ι → M) (ell : ι → M →ₗ[K] K)
    (hdelta : ∀ i j, ell j (d i) = if i = j then 1 else 0) :
    LinearIndependent K d := by
  classical
  letI := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have happly := congrArg (fun v => ell i v) hsum
  simpa [map_sum, hdelta] using happly

/--
Linear-algebra ladder bound from `thm:affine-cell(iv)`.  A ladder of size
`n+1` in affine-linear rows produces `n` independent direction vectors in `W`,
so `n+1 ≤ dim(W)+1`.
-/
theorem affineCell_ladder_size_le_finrank_add_one
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (W : Submodule K M) [Module.Finite K W]
    (row : Fin (n + 1) → M) (L : Fin (n + 1) → M →ₗ[K] K)
    (hdiff : ∀ i : Fin n, row i.castSucc - row i.succ ∈ W)
    (hladder : ∀ i j : Fin (n + 1), L j (row i) = if i ≤ j then 1 else 0) :
    n + 1 ≤ Module.finrank K W + 1 := by
  classical
  let d : Fin n → W := fun i => ⟨row i.castSucc - row i.succ, hdiff i⟩
  let ell : Fin n → W →ₗ[K] K := fun j => (L j.castSucc).comp W.subtype
  have hdelta : ∀ i j, ell j (d i) = if i = j then 1 else 0 := by
    intro i j
    dsimp [ell, d]
    rw [map_sub, hladder, hladder]
    by_cases hij : i = j
    · subst j
      have hle2 : ¬ (i.succ : Fin (n + 1)) ≤ i.castSucc := by
        rw [Fin.succ_le_castSucc_iff]
        exact lt_irrefl i
      simp [hle2]
    · by_cases hleij : i ≤ j
      · have hltij : i < j := lt_of_le_of_ne hleij hij
        have hle1 : (i.castSucc : Fin (n + 1)) ≤ j.castSucc := by
          rw [Fin.castSucc_le_castSucc_iff]
          exact hleij
        have hle2 : (i.succ : Fin (n + 1)) ≤ j.castSucc := by
          rw [Fin.succ_le_castSucc_iff]
          exact hltij
        simp [hij, hle1, hle2]
      · have hnot1 : ¬ (i.castSucc : Fin (n + 1)) ≤ j.castSucc := by
          rw [Fin.castSucc_le_castSucc_iff]
          exact hleij
        have hnot2 : ¬ (i.succ : Fin (n + 1)) ≤ j.castSucc := by
          rw [Fin.succ_le_castSucc_iff]
          exact fun hlt => hleij (le_of_lt hlt)
        simp [hij, hnot1, hnot2]
  have hli : LinearIndependent K d := linearIndependent_of_dual_delta d ell hdelta
  have hcard : Fintype.card (Fin n) ≤ Module.finrank K W := hli.fintype_card_le_finrank
  simpa [Fintype.card_fin] using Nat.add_le_add_right hcard 1

end Erdos61
