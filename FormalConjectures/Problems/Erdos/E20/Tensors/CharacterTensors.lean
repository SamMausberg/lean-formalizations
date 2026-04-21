import Mathlib
import FormalConjectures.Problems.Erdos.E20.Families.TransversalCounterexample

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

set_option linter.unnecessarySimpa false

/-!
# Character Tensors on `F_2^2`

This file formalizes a small, fully explicit part of the user's Fourier/tensor note for
`V = F_2^2`, realized as `Fin 2 × Fin 2`.

The main points are:

* an explicit `10`-term local character tensor detecting exactly the constant-or-injective
  `4`-columns on `V`;
* the exact support statement for that local tensor;
* the global consequence that on any `4`-sunflower-free transversal code family, the product
  tensor is already diagonal on `4`-tuples from the family.

We deliberately keep the formalization concrete.  The local tensor is tiny, so its exact support is
proved by exhaustive finite checking after setting up the character decomposition honestly.
-/

section LocalTensor

/-- The local alphabet `V = F_2^2`. -/
abbrev V : Type := Fin 2 × Fin 2

/-- The three nonzero vectors of `F_2^2`. -/
inductive NonzeroV
  | v01
  | v10
  | v11
  deriving DecidableEq, Fintype

/-- The underlying vector in `V`. -/
def NonzeroV.toV : NonzeroV → V
  | .v01 => (0, 1)
  | .v10 => (1, 0)
  | .v11 => (1, 1)

/-- The unique nontrivial orthogonal character for the given nonzero direction. -/
def NonzeroV.orth : NonzeroV → V
  | .v01 => (1, 0)
  | .v10 => (0, 1)
  | .v11 => (1, 1)

/-- The ten local Fourier modes: four diagonal character modes and, for each nonzero direction,
one plain difference mode and one twisted difference mode. -/
abbrev LocalMode : Type := V ⊕ (NonzeroV × Bool)

@[simp] theorem card_V : Fintype.card V = 4 := by
  simp [V]

@[simp] theorem card_NonzeroV : Fintype.card NonzeroV = 3 := by
  decide

@[simp] theorem card_LocalMode : Fintype.card LocalMode = 10 := by
  simp [LocalMode, V]

/-- The sign character on one bit. -/
def bitSign (x : Fin 2) : ℚ :=
  if x = 0 then 1 else -1

/-- The Walsh character `χ_u(x) = (-1)^{u · x}` on `V`. -/
def char (u x : V) : ℚ :=
  bitSign (u.1 * x.1 + u.2 * x.2)

/-- The support predicate for the local tensor: a `4`-column is either constant or injective. -/
def localConstantOrInjective (a b c d : V) : Prop :=
  (a = b ∧ b = c ∧ c = d) ∨ Function.Injective ![a, b, c, d]

instance instDecidableLocalConstantOrInjective (a b c d : V) :
    Decidable (localConstantOrInjective a b c d) := by
  unfold localConstantOrInjective
  infer_instance

/-- The honest `0/1` indicator of the local support. -/
def localIndicator (a b c d : V) : ℚ :=
  if localConstantOrInjective a b c d then 1 else 0

/-- The bit value of an element of `Fin 2`, viewed in `ZMod 2`. -/
def bitVal (x : Fin 2) : ZMod 2 :=
  x.1

/-- The local Kronecker delta from the user's `(4,4)` diagonal-tensor note, written on
`V = F_2^2`. -/
def deltaF2 (u v : V) : ZMod 2 :=
  (1 + bitVal u.1 + bitVal v.1) * (1 + bitVal u.2 + bitVal v.2)

/-- The alternating bilinear form from the user's `(4,4)` diagonal-tensor note, written on
`V = F_2^2`. -/
def omegaF2 (u v : V) : ZMod 2 :=
  bitVal u.1 * bitVal v.2 + bitVal u.2 * bitVal v.1

/-- The explicit local `F_2`-valued tensor from the user's `(4,4)` note. -/
def explicitLocalTensor (a b c d : V) : ZMod 2 :=
  deltaF2 (0, 0) (a + b + c + d) * omegaF2 (a + b) (a + c) +
    deltaF2 a b * deltaF2 a c * deltaF2 a d

/-- The `ZMod 2` indicator of the constant-or-injective local support. -/
def localIndicatorF2 (a b c d : V) : ZMod 2 :=
  if localConstantOrInjective a b c d then 1 else 0

set_option linter.style.nativeDecide false in
theorem deltaF2_eq_iff (u v : V) :
    deltaF2 u v = 1 ↔ u = v := by
  rcases u with ⟨u₀, u₁⟩
  rcases v with ⟨v₀, v₁⟩
  fin_cases u₀ <;> fin_cases u₁ <;> fin_cases v₀ <;> fin_cases v₁ <;>
    decide

set_option linter.style.nativeDecide false in
theorem omegaF2_eq_one_iff (u v : V) :
    omegaF2 u v = 1 ↔ u ≠ (0, 0) ∧ v ≠ (0, 0) ∧ u ≠ v := by
  rcases u with ⟨u₀, u₁⟩
  rcases v with ⟨v₀, v₁⟩
  fin_cases u₀ <;> fin_cases u₁ <;> fin_cases v₀ <;> fin_cases v₁ <;>
    decide

set_option linter.style.nativeDecide false in
theorem explicitLocalTensor_eq_indicatorF2 (a b c d : V) :
    explicitLocalTensor a b c d = localIndicatorF2 a b c d := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  rcases c with ⟨c₀, c₁⟩
  rcases d with ⟨d₀, d₁⟩
  fin_cases a₀ <;> fin_cases a₁ <;>
    fin_cases b₀ <;> fin_cases b₁ <;>
    fin_cases c₀ <;> fin_cases c₁ <;>
    fin_cases d₀ <;> fin_cases d₁ <;>
    native_decide

theorem explicitLocalTensor_eq_one_iff_constantOrInjective (a b c d : V) :
    explicitLocalTensor a b c d = 1 ↔ localConstantOrInjective a b c d := by
  rw [explicitLocalTensor_eq_indicatorF2, localIndicatorF2]
  by_cases h : localConstantOrInjective a b c d <;> simp [h]

theorem explicitLocalTensor_eq_zero_iff_not_constantOrInjective (a b c d : V) :
    explicitLocalTensor a b c d = 0 ↔ ¬ localConstantOrInjective a b c d := by
  rw [explicitLocalTensor_eq_indicatorF2, localIndicatorF2]
  by_cases h : localConstantOrInjective a b c d <;> simp [h]

/-- Diagonal character mode on ordered pairs. -/
def eqModeFeature (u : V) (p : V × V) : ℚ :=
  if p.2 = p.1 then char u p.1 else 0

/-- Plain difference mode on ordered pairs. -/
def diffModeFeature (s : NonzeroV) (p : V × V) : ℚ :=
  if p.2 = p.1 + s.toV then 1 else 0

/-- Twisted difference mode on ordered pairs. -/
def twistModeFeature (s : NonzeroV) (p : V × V) : ℚ :=
  if p.2 = p.1 + s.toV then char s.orth p.1 else 0

/-- Left factor in the `10`-term local character decomposition. -/
def leftFeature : LocalMode → (V × V) → ℚ
  | Sum.inl u, p => (1 / 4 : ℚ) * eqModeFeature u p
  | Sum.inr (s, false), p => (1 / 2 : ℚ) * diffModeFeature s p
  | Sum.inr (s, true), p => (-1 / 2 : ℚ) * twistModeFeature s p

/-- Right factor in the `10`-term local character decomposition. -/
def rightFeature : LocalMode → (V × V) → ℚ
  | Sum.inl u, p => eqModeFeature u p
  | Sum.inr (s, false), p => diffModeFeature s p
  | Sum.inr (s, true), p => twistModeFeature s p

/-- The explicit local character tensor from the user's note, flattened as
`(a,b) | (c,d)`. -/
def localCharacterTensor (a b c d : V) : ℚ :=
  ∑ m : LocalMode, leftFeature m (a, b) * rightFeature m (c, d)

set_option linter.style.nativeDecide false in
theorem localCharacterTensor_eq_indicator (a b c d : V) :
    localCharacterTensor a b c d = localIndicator a b c d := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  rcases c with ⟨c₀, c₁⟩
  rcases d with ⟨d₀, d₁⟩
  fin_cases a₀ <;> fin_cases a₁ <;>
    fin_cases b₀ <;> fin_cases b₁ <;>
    fin_cases c₀ <;> fin_cases c₁ <;>
    fin_cases d₀ <;> fin_cases d₁ <;>
    native_decide

@[simp] theorem localCharacterTensor_eq_zero_or_one (a b c d : V) :
    localCharacterTensor a b c d = 0 ∨ localCharacterTensor a b c d = 1 := by
  rw [localCharacterTensor_eq_indicator]
  by_cases h : localConstantOrInjective a b c d
  · simp [localIndicator, h]
  · simp [localIndicator, h]

theorem localCharacterTensor_eq_one_iff_constantOrInjective (a b c d : V) :
    localCharacterTensor a b c d = 1 ↔ localConstantOrInjective a b c d := by
  rw [localCharacterTensor_eq_indicator, localIndicator]
  by_cases h : localConstantOrInjective a b c d <;> simp [h]

theorem localCharacterTensor_eq_zero_iff_not_constantOrInjective (a b c d : V) :
    localCharacterTensor a b c d = 0 ↔ ¬ localConstantOrInjective a b c d := by
  rw [localCharacterTensor_eq_indicator, localIndicator]
  by_cases h : localConstantOrInjective a b c d <;> simp [h]

/-- Constant-or-injective local columns give sunflower tuples of singleton fibers. -/
theorem singletonTuple_isSunflower_of_localConstantOrInjective
    {a b c d : V} (h : localConstantOrInjective a b c d) :
    IsSunflowerTuple (fun t : Fin 4 => ({(![a, b, c, d] t)} : Finset V)) := by
  rcases h with ⟨hab, hbc, hcd⟩ | hinj
  · intro u v u' v' huv hu'v'
    ext x
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;>
      simp [hab, hbc, hcd]
  · intro u v u' v' huv hu'v'
    have huv' : (![a, b, c, d] u) ≠ (![a, b, c, d] v) := hinj.ne huv
    have hu'v'' : (![a, b, c, d] u') ≠ (![a, b, c, d] v') := hinj.ne hu'v'
    ext x
    simp [huv', hu'v'']

end LocalTensor

section GlobalTensor

abbrev TensorWord (n : ℕ) : Type := Fin n → V

/-- The global product tensor obtained from the explicit `F_2`-valued local formula in the user's
`(4,4)` note. -/
def explicitGlobalTensorTuple {n : ℕ} (x : Fin 4 → TensorWord n) : ZMod 2 :=
  ∏ i : Fin n, explicitLocalTensor (x 0 i) (x 1 i) (x 2 i) (x 3 i)

/-- The global product tensor: multiply the local character tensor over all coordinates. -/
def globalTensorTuple {n : ℕ} (x : Fin 4 → TensorWord n) : ℚ :=
  ∏ i : Fin n, localCharacterTensor (x 0 i) (x 1 i) (x 2 i) (x 3 i)

/-- Coordinatewise local support for a `4`-tuple of words. -/
def ColumnwiseConstantOrInjective {n : ℕ} (x : Fin 4 → TensorWord n) : Prop :=
  ∀ i : Fin n, localConstantOrInjective (x 0 i) (x 1 i) (x 2 i) (x 3 i)

theorem columnwiseConstantOrInjective_of_explicitGlobalTensor_ne_zero
    {n : ℕ} {x : Fin 4 → TensorWord n} (h : explicitGlobalTensorTuple x ≠ 0) :
    ColumnwiseConstantOrInjective x := by
  intro i
  by_contra hi
  have hzero :
      explicitLocalTensor (x 0 i) (x 1 i) (x 2 i) (x 3 i) = 0 := by
    rw [explicitLocalTensor_eq_zero_iff_not_constantOrInjective]
    exact hi
  have hprod : explicitGlobalTensorTuple x = 0 := by
    unfold explicitGlobalTensorTuple
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨i, by simp, hzero⟩
  exact h hprod

theorem columnwiseConstantOrInjective_of_globalTensor_ne_zero
    {n : ℕ} {x : Fin 4 → TensorWord n} (h : globalTensorTuple x ≠ 0) :
    ColumnwiseConstantOrInjective x := by
  intro i
  by_contra hi
  have hzero :
      localCharacterTensor (x 0 i) (x 1 i) (x 2 i) (x 3 i) = 0 := by
    rw [localCharacterTensor_eq_zero_iff_not_constantOrInjective]
    exact hi
  have hprod : globalTensorTuple x = 0 := by
    unfold globalTensorTuple
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨i, by simp, hzero⟩
  exact h hprod

/-- If every coordinate column is constant-or-injective, then the corresponding transversal tuple
is a sunflower. -/
theorem ColumnwiseConstantOrInjective.isSunflowerTuple_transversal
    {n : ℕ} {x : Fin 4 → TensorWord n} (hcol : ColumnwiseConstantOrInjective x) :
    IsSunflowerTuple (fun t => transversalEdge (x t)) := by
  intro u v u' v' huv hu'v'
  ext p
  rcases p with ⟨i, a⟩
  let col : Fin 4 → V := fun t => x t i
  have hlocal :
      ({col u} : Finset V) ∩ {col v} = ({col u'} : Finset V) ∩ {col v'} := by
    have hraw := (singletonTuple_isSunflower_of_localConstantOrInjective (hcol i)) huv hu'v'
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;>
      simpa [col] using hraw
  exact by
    simpa [mem_transversalEdge_iff, eq_comm, and_left_comm, and_assoc] using
      congrArg (fun s : Finset V => a ∈ s) hlocal

/-- If every coordinate column is constant-or-injective and the tuple is not completely constant,
then the four words are distinct. -/
theorem injective_of_columnwiseConstantOrInjective_of_not_allEqual
    {n : ℕ} {x : Fin 4 → TensorWord n} (hcol : ColumnwiseConstantOrInjective x)
    (hall : ¬ ∀ t : Fin 4, x t = x 0) :
    Function.Injective x := by
  intro u v huvEq
  by_contra huv
  have hnotAllU : ¬ ∀ t : Fin 4, x t = x u := by
    intro hU
    apply hall
    intro t
    calc
      x t = x u := hU t
      _ = x 0 := by simpa using (hU 0).symm
  push Not at hnotAllU
  rcases hnotAllU with ⟨w, hw⟩
  have hcoord : ∃ i : Fin n, x w i ≠ x u i := by
    by_contra hcoord
    push Not at hcoord
    exact hw (funext hcoord)
  rcases hcoord with ⟨i, hwi⟩
  let col : Fin 4 → V := fun t => x t i
  have huvi : col u = col v := by
    simpa [col] using congrArg (fun f : TensorWord n => f i) huvEq
  have hwi' : col w ≠ col u := by
    simpa [col] using hwi
  have hci : localConstantOrInjective (col 0) (col 1) (col 2) (col 3) := by
    simpa [col] using hcol i
  rcases hci with ⟨h01, h12, h23⟩ | hinj
  · have hAll : ∀ t : Fin 4, col t = col 0 := by
      intro t
      fin_cases t <;> simp [col, h01, h12, h23]
    have : col w = col u := by
      calc
        col w = col 0 := hAll w
        _ = col u := (hAll u).symm
    exact hwi' this
  · have hinjCol : Function.Injective col := by
      intro s t hst
      have hraw : (![col 0, col 1, col 2, col 3] s) = (![col 0, col 1, col 2, col 3] t) := by
        fin_cases s <;> fin_cases t <;> simpa [col] using hst
      exact hinj hraw
    exact huv (hinjCol huvi)

/-- On an injective `4`-tuple from a `4`-sunflower-free family, the explicit `F_2` tensor
vanishes. -/
theorem explicitGlobalTensorTuple_eq_zero_of_sunflowerFree
    {n : ℕ} {C : Finset (TensorWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V) C) 4)
    {x : Fin 4 → TensorWord n} (hxC : ∀ t, x t ∈ C) (hxinj : Function.Injective x) :
    explicitGlobalTensorTuple x = 0 := by
  by_contra hne
  have hcol : ColumnwiseConstantOrInjective x :=
    columnwiseConstantOrInjective_of_explicitGlobalTensor_ne_zero hne
  have hSun : IsSunflowerTuple (fun t => transversalEdge (x t)) :=
    hcol.isSunflowerTuple_transversal
  have hEdgeInj : Function.Injective (fun t => transversalEdge (x t)) := by
    intro u v huv
    exact hxinj (transversalEdge_injective huv)
  have hmem : ∀ t, transversalEdge (x t) ∈ transversalFamily (G := V) C := by
    intro t
    exact Finset.mem_image.mpr ⟨x t, hxC t, rfl⟩
  exact hfree (fun t => transversalEdge (x t)) hmem hEdgeInj hSun

theorem explicitGlobalTensorTuple_eq_one_of_allEqual
    {n : ℕ} {x : Fin 4 → TensorWord n} (hall : ∀ t : Fin 4, x t = x 0) :
    explicitGlobalTensorTuple x = 1 := by
  unfold explicitGlobalTensorTuple
  refine Finset.prod_eq_one ?_
  intro i hi
  have h01 : x 0 i = x 1 i := by
    simpa using congrArg (fun f : TensorWord n => f i) (hall 1).symm
  have h12 : x 1 i = x 2 i := by
    calc
      x 1 i = x 0 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 1)
      _ = x 2 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 2).symm
  have h23 : x 2 i = x 3 i := by
    calc
      x 2 i = x 0 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 2)
      _ = x 3 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 3).symm
  rw [explicitLocalTensor_eq_one_iff_constantOrInjective]
  exact Or.inl ⟨h01, h12, h23⟩

/-- On a `4`-sunflower-free code over `V = F_2^2`, the explicit `F_2` tensor is diagonal: among
tuples from the family it survives exactly on the all-equal tuples. -/
theorem explicitGlobalTensorTuple_eq_ite_allEqual_of_sunflowerFree
    {n : ℕ} {C : Finset (TensorWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V) C) 4)
    {x : Fin 4 → TensorWord n} (hxC : ∀ t, x t ∈ C) :
    explicitGlobalTensorTuple x = if ∀ t : Fin 4, x t = x 0 then 1 else 0 := by
  by_cases hall : ∀ t : Fin 4, x t = x 0
  · simp [hall, explicitGlobalTensorTuple_eq_one_of_allEqual hall]
  · have hzero : explicitGlobalTensorTuple x = 0 := by
      by_contra hne
      have hcol : ColumnwiseConstantOrInjective x :=
        columnwiseConstantOrInjective_of_explicitGlobalTensor_ne_zero hne
      have hxinj : Function.Injective x :=
        injective_of_columnwiseConstantOrInjective_of_not_allEqual hcol hall
      exact hne (explicitGlobalTensorTuple_eq_zero_of_sunflowerFree hfree hxC hxinj)
    simp [hall, hzero]

/-- On an injective `4`-tuple from a `4`-sunflower-free family, the global tensor vanishes. -/
theorem globalTensorTuple_eq_zero_of_sunflowerFree
    {n : ℕ} {C : Finset (TensorWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V) C) 4)
    {x : Fin 4 → TensorWord n} (hxC : ∀ t, x t ∈ C) (hxinj : Function.Injective x) :
    globalTensorTuple x = 0 := by
  by_contra hne
  have hcol : ColumnwiseConstantOrInjective x :=
    columnwiseConstantOrInjective_of_globalTensor_ne_zero hne
  have hSun : IsSunflowerTuple (fun t => transversalEdge (x t)) :=
    hcol.isSunflowerTuple_transversal
  have hEdgeInj : Function.Injective (fun t => transversalEdge (x t)) := by
    intro u v huv
    exact hxinj (transversalEdge_injective huv)
  have hmem : ∀ t, transversalEdge (x t) ∈ transversalFamily (G := V) C := by
    intro t
    exact Finset.mem_image.mpr ⟨x t, hxC t, rfl⟩
  exact hfree (fun t => transversalEdge (x t)) hmem hEdgeInj hSun

theorem globalTensorTuple_eq_one_of_allEqual
    {n : ℕ} {x : Fin 4 → TensorWord n} (hall : ∀ t : Fin 4, x t = x 0) :
    globalTensorTuple x = 1 := by
  unfold globalTensorTuple
  refine Finset.prod_eq_one ?_
  intro i hi
  have h01 : x 0 i = x 1 i := by
    simpa using congrArg (fun f : TensorWord n => f i) (hall 1).symm
  have h12 : x 1 i = x 2 i := by
    calc
      x 1 i = x 0 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 1)
      _ = x 2 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 2).symm
  have h23 : x 2 i = x 3 i := by
    calc
      x 2 i = x 0 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 2)
      _ = x 3 i := by simpa using congrArg (fun f : TensorWord n => f i) (hall 3).symm
  rw [localCharacterTensor_eq_one_iff_constantOrInjective]
  exact Or.inl ⟨h01, h12, h23⟩

/-- On a `4`-sunflower-free code over `V = F_2^2`, the global tensor is diagonal: among tuples from
the family it survives exactly on the all-equal tuples. -/
theorem globalTensorTuple_eq_ite_allEqual_of_sunflowerFree
    {n : ℕ} {C : Finset (TensorWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V) C) 4)
    {x : Fin 4 → TensorWord n} (hxC : ∀ t, x t ∈ C) :
    globalTensorTuple x = if ∀ t : Fin 4, x t = x 0 then 1 else 0 := by
  by_cases hall : ∀ t : Fin 4, x t = x 0
  · simp [hall, globalTensorTuple_eq_one_of_allEqual hall]
  · have hzero : globalTensorTuple x = 0 := by
      by_contra hne
      have hcol : ColumnwiseConstantOrInjective x :=
        columnwiseConstantOrInjective_of_globalTensor_ne_zero hne
      have hxinj : Function.Injective x :=
        injective_of_columnwiseConstantOrInjective_of_not_allEqual hcol hall
      exact hne (globalTensorTuple_eq_zero_of_sunflowerFree hfree hxC hxinj)
    simp [hall, hzero]

/-- Ordered word pairs for the `2+2` flattening. -/
abbrev TensorPairWord (n : ℕ) : Type := TensorWord n × TensorWord n

/-- One local mode per coordinate. -/
abbrev GlobalMode (n : ℕ) : Type := Fin n → LocalMode

@[simp] theorem card_GlobalMode (n : ℕ) : Fintype.card (GlobalMode n) = 10 ^ n := by
  simp [GlobalMode]

/-- The `2+2` flattening of the global tensor. -/
def globalCharacterMatrix (n : ℕ) : Matrix (TensorPairWord n) (TensorPairWord n) ℚ :=
  fun p q => ∏ i : Fin n, localCharacterTensor (p.1 i) (p.2 i) (q.1 i) (q.2 i)

/-- Left factor for the explicit `10^n`-term flattening decomposition. -/
def leftFactorMatrix (n : ℕ) : Matrix (TensorPairWord n) (GlobalMode n) ℚ :=
  fun p m => ∏ i : Fin n, leftFeature (m i) (p.1 i, p.2 i)

/-- Right factor for the explicit `10^n`-term flattening decomposition. -/
def rightFactorMatrix (n : ℕ) : Matrix (GlobalMode n) (TensorPairWord n) ℚ :=
  fun m q => ∏ i : Fin n, rightFeature (m i) (q.1 i, q.2 i)

/-- The global `2+2` flattening factors through the `10^n` local mode choices. -/
theorem globalCharacterMatrix_eq_mul_factors (n : ℕ) :
    globalCharacterMatrix n = leftFactorMatrix n * rightFactorMatrix n := by
  ext p q
  rw [Matrix.mul_apply]
  calc
    ∏ i : Fin n, localCharacterTensor (p.1 i) (p.2 i) (q.1 i) (q.2 i)
        = ∑ m ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset LocalMode)),
            ∏ i : Fin n, leftFeature (m i) (p.1 i, p.2 i) * rightFeature (m i) (q.1 i, q.2 i) := by
              simpa [localCharacterTensor] using
                (Finset.prod_univ_sum
                  (t := fun _ : Fin n => (Finset.univ : Finset LocalMode))
                  (f := fun i m =>
                    leftFeature m (p.1 i, p.2 i) * rightFeature m (q.1 i, q.2 i)))
    _ = ∑ m : GlobalMode n,
            ∏ i : Fin n, leftFeature (m i) (p.1 i, p.2 i) * rightFeature (m i) (q.1 i, q.2 i) := by
          simp only [Fintype.piFinset_univ]
    _ = ∑ m : GlobalMode n,
            (∏ i : Fin n, leftFeature (m i) (p.1 i, p.2 i)) *
              ∏ i : Fin n, rightFeature (m i) (q.1 i, q.2 i) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          simpa using
            (Finset.prod_mul_distrib :
              (∏ i : Fin n, leftFeature (m i) (p.1 i, p.2 i) *
                  rightFeature (m i) (q.1 i, q.2 i)) =
                (∏ i : Fin n, leftFeature (m i) (p.1 i, p.2 i)) *
                  ∏ i : Fin n, rightFeature (m i) (q.1 i, q.2 i))
    _ = (leftFactorMatrix n * rightFactorMatrix n) p q := by
          simp [leftFactorMatrix, rightFactorMatrix, Matrix.mul_apply]

/-- Consequently, the ordinary matrix rank of the global `2+2` flattening is at most `10^n`. -/
theorem rank_globalCharacterMatrix_le_ten_pow (n : ℕ) :
    (globalCharacterMatrix n).rank ≤ 10 ^ n := by
  calc
    (globalCharacterMatrix n).rank = (leftFactorMatrix n * rightFactorMatrix n).rank := by
      rw [globalCharacterMatrix_eq_mul_factors]
    _ ≤ (rightFactorMatrix n).rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card (GlobalMode n) := Matrix.rank_le_card_height _
    _ = 10 ^ n := by simp

end GlobalTensor

end FormalConjectures.Problems.Erdos.E20
