import Mathlib
import FormalConjectures.Problems.Erdos.E20.Families.TransversalCounterexample

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

set_option linter.unnecessarySimpa false

/-!
# Explicit `(5,5)` Local Tensor

This file formalizes the valid structural part of the user's `(q,k) = (5,5)` diagonal-tensor note.

We work over `F_5 = ZMod 5`.  The main points are:

* the explicit local polynomial tensor from the note detects exactly the constant-or-injective
  `5`-columns;
* the corresponding global product tensor is diagonal on tuples from a `5`-sunflower-free
  transversal code.

The final cardinality bound claimed in the note is not formalized here: the monomial-counting
estimate used there is not correct as stated, so the present file records only the proved tensor
support / diagonality statements.
-/

section LocalTensor

/-- The local alphabet `F_5`. -/
abbrev V5 : Type := ZMod 5

instance : Fact (Nat.Prime 5) := by
  decide

instance : Nontrivial V5 := by
  delta V5
  infer_instance

instance : NoZeroDivisors V5 := by
  delta V5
  infer_instance

/-- The four nonzero field elements, indexed as `1,2,3,4`. -/
def nonzeroV5 (i : Fin 4) : V5 :=
  (i : ℕ) + 1

/-- The local Kronecker delta `δ_t(z) = 1 - (z - t)^4` on `F_5`. -/
def delta5 (t z : V5) : V5 :=
  1 - (z - t) ^ 4

/-- The support predicate for the local `(5,5)` tensor: a `5`-column is constant or injective. -/
def localConstantOrInjective5 (a b c d e : V5) : Prop :=
  (a = b ∧ b = c ∧ c = d ∧ d = e) ∨ Function.Injective ![a, b, c, d, e]

instance instDecidableLocalConstantOrInjective5 (a b c d e : V5) :
    Decidable (localConstantOrInjective5 a b c d e) := by
  unfold localConstantOrInjective5
  infer_instance

/-- The `0/1` indicator of the constant-or-injective local support. -/
def localIndicator5 (a b c d e : V5) : V5 :=
  if localConstantOrInjective5 a b c d e then 1 else 0

/-- The explicit local tensor from the user's `(5,5)` note. -/
def explicitLocalTensor5 (a b c d e : V5) : V5 :=
  (∏ i : Fin 4, delta5 0 (![a, b, c, d] i - e)) +
    ∑ σ : Equiv.Perm (Fin 4),
      ∏ i : Fin 4, delta5 (nonzeroV5 (σ i)) (![a, b, c, d] i - e)

set_option linter.style.nativeDecide false in
theorem explicitLocalTensor5_eq_indicator5 :
    ∀ a b c d e : V5, explicitLocalTensor5 a b c d e = localIndicator5 a b c d e := by
  native_decide

theorem explicitLocalTensor5_eq_one_iff_constantOrInjective
    (a b c d e : V5) :
    explicitLocalTensor5 a b c d e = 1 ↔ localConstantOrInjective5 a b c d e := by
  rw [explicitLocalTensor5_eq_indicator5, localIndicator5]
  by_cases h : localConstantOrInjective5 a b c d e
  · simp [h]
  · simp [h, zero_ne_one]

theorem explicitLocalTensor5_eq_zero_iff_not_constantOrInjective
    (a b c d e : V5) :
    explicitLocalTensor5 a b c d e = 0 ↔ ¬ localConstantOrInjective5 a b c d e := by
  rw [explicitLocalTensor5_eq_indicator5, localIndicator5]
  by_cases h : localConstantOrInjective5 a b c d e
  · simp [h, one_ne_zero]
  · simp [h]

/-- Restatement of the pasted `(5,5)` local-support claim: the explicit tensor is supported
exactly on constant-or-injective columns. -/
theorem pasted_quinary_local_tensor_support
    (a b c d e : V5) :
    explicitLocalTensor5 a b c d e ≠ 0 ↔ localConstantOrInjective5 a b c d e := by
  constructor
  · intro hne
    by_contra hlocal
    exact hne ((explicitLocalTensor5_eq_zero_iff_not_constantOrInjective a b c d e).2 hlocal)
  · intro hlocal
    have hone :
        explicitLocalTensor5 a b c d e = 1 :=
      (explicitLocalTensor5_eq_one_iff_constantOrInjective a b c d e).2 hlocal
    rw [hone]
    exact one_ne_zero

/-- Constant-or-injective local columns give sunflower tuples of singleton fibers. -/
theorem singletonTuple_isSunflower_of_localConstantOrInjective5
    {a b c d e : V5} (h : localConstantOrInjective5 a b c d e) :
    IsSunflowerTuple (fun t : Fin 5 => ({(![a, b, c, d, e] t)} : Finset V5)) := by
  rcases h with ⟨hab, hbc, hcd, hde⟩ | hinj
  · intro u v u' v' huv hu'v'
    ext x
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;>
      simp [hab, hbc, hcd, hde]
  · intro u v u' v' huv hu'v'
    have huv' : (![a, b, c, d, e] u) ≠ (![a, b, c, d, e] v) := hinj.ne huv
    have hu'v'' : (![a, b, c, d, e] u') ≠ (![a, b, c, d, e] v') := hinj.ne hu'v'
    ext x
    simp [huv', hu'v'']

end LocalTensor

section GlobalTensor

abbrev QuinaryWord (n : ℕ) : Type := Fin n → V5

/-- The global product tensor obtained from the explicit `(5,5)` local formula. -/
def explicitGlobalTensor5Tuple {n : ℕ} (x : Fin 5 → QuinaryWord n) : V5 :=
  ∏ i : Fin n, explicitLocalTensor5 (x 0 i) (x 1 i) (x 2 i) (x 3 i) (x 4 i)

/-- Coordinatewise local support for a `5`-tuple of words. -/
def ColumnwiseConstantOrInjective5 {n : ℕ} (x : Fin 5 → QuinaryWord n) : Prop :=
  ∀ i : Fin n, localConstantOrInjective5 (x 0 i) (x 1 i) (x 2 i) (x 3 i) (x 4 i)

theorem columnwiseConstantOrInjective5_of_explicitGlobalTensor5_ne_zero
    {n : ℕ} {x : Fin 5 → QuinaryWord n} (h : explicitGlobalTensor5Tuple x ≠ 0) :
    ColumnwiseConstantOrInjective5 x := by
  intro i
  by_contra hi
  have hzero :
      explicitLocalTensor5 (x 0 i) (x 1 i) (x 2 i) (x 3 i) (x 4 i) = 0 := by
    rw [explicitLocalTensor5_eq_zero_iff_not_constantOrInjective]
    exact hi
  have hprod : explicitGlobalTensor5Tuple x = 0 := by
    unfold explicitGlobalTensor5Tuple
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨i, by simp, hzero⟩
  exact h hprod

/-- If every coordinate column is constant-or-injective, then the corresponding transversal tuple
is a sunflower. -/
theorem ColumnwiseConstantOrInjective5.isSunflowerTuple_transversal
    {n : ℕ} {x : Fin 5 → QuinaryWord n} (hcol : ColumnwiseConstantOrInjective5 x) :
    IsSunflowerTuple (fun t => transversalEdge (x t)) := by
  intro u v u' v' huv hu'v'
  ext p
  rcases p with ⟨i, a⟩
  let col : Fin 5 → V5 := ![x 0 i, x 1 i, x 2 i, x 3 i, x 4 i]
  have hcol_eval : ∀ t : Fin 5, col t = x t i := by
    intro t
    fin_cases t <;> rfl
  have hlocal :
      ({col u} : Finset V5) ∩ {col v} = ({col u'} : Finset V5) ∩ {col v'} := by
    simpa [col] using
      (singletonTuple_isSunflower_of_localConstantOrInjective5 (hcol i)) huv hu'v'
  constructor
  · intro hp
    have hxy : a = x u i ∧ a = x v i := by
      simpa [mem_transversalEdge_iff, eq_comm] using hp
    have ha' : a ∈ ({col u} : Finset V5) ∩ {col v} := by
      rcases hxy with ⟨hau, hav⟩
      have hcu : a = col u := hau.trans (hcol_eval u).symm
      have hcv : a = col v := hav.trans (hcol_eval v).symm
      have huvcol : col u = col v := hcu.symm.trans hcv
      exact Finset.mem_inter.mpr (by simp [hcu, huvcol])
    have ha'' : a ∈ ({col u'} : Finset V5) ∩ {col v'} := by
      simpa [hlocal] using ha'
    rcases Finset.mem_inter.mp ha'' with ⟨hau', hav'⟩
    have hau'' : a = x u' i := by
      simpa [hcol_eval u', eq_comm] using hau'
    have hav'' : a = x v' i := by
      simpa [hcol_eval v', eq_comm] using hav'
    simpa [mem_transversalEdge_iff, eq_comm] using And.intro hau'' hav''
  · intro hp
    have hxy : a = x u' i ∧ a = x v' i := by
      simpa [mem_transversalEdge_iff, eq_comm] using hp
    have ha' : a ∈ ({col u'} : Finset V5) ∩ {col v'} := by
      rcases hxy with ⟨hau, hav⟩
      have hcu : a = col u' := hau.trans (hcol_eval u').symm
      have hcv : a = col v' := hav.trans (hcol_eval v').symm
      have huvcol : col u' = col v' := hcu.symm.trans hcv
      exact Finset.mem_inter.mpr (by simp [hcu, huvcol])
    have ha'' : a ∈ ({col u} : Finset V5) ∩ {col v} := by
      simpa [hlocal] using ha'
    rcases Finset.mem_inter.mp ha'' with ⟨hau', hav'⟩
    have hau'' : a = x u i := by
      simpa [hcol_eval u, eq_comm] using hau'
    have hav'' : a = x v i := by
      simpa [hcol_eval v, eq_comm] using hav'
    simpa [mem_transversalEdge_iff, eq_comm] using And.intro hau'' hav''

lemma allEqual_of_columnwiseConstantOrInjective5_of_eq
    {n : ℕ} {x : Fin 5 → QuinaryWord n} (hcol : ColumnwiseConstantOrInjective5 x)
    {u v : Fin 5} (huv : u ≠ v) (huvEq : x u = x v) :
    ∀ t : Fin 5, x t = x u := by
  intro t
  by_contra htu
  have hcoord : ∃ i : Fin n, x t i ≠ x u i := by
    by_contra hcoord
    push Not at hcoord
    exact htu (funext hcoord)
  rcases hcoord with ⟨i, hti⟩
  have huvi : x u i = x v i := by
    simpa using congrArg (fun f : QuinaryWord n => f i) huvEq
  have hci : localConstantOrInjective5 (x 0 i) (x 1 i) (x 2 i) (x 3 i) (x 4 i) := hcol i
  rcases hci with ⟨h01, h12, h23, h34⟩ | hinj
  · have hAll : ∀ s : Fin 5, x s i = x 0 i := by
      intro s
      fin_cases s <;> simp [h01, h12, h23, h34]
    have : x t i = x u i := by
      calc
        x t i = x 0 i := hAll t
        _ = x u i := (hAll u).symm
    exact hti this
  · have hvec : (![x 0 i, x 1 i, x 2 i, x 3 i, x 4 i] u) =
      (![x 0 i, x 1 i, x 2 i, x 3 i, x 4 i] v) := by
        fin_cases u <;> fin_cases v <;> simpa using huvi
    exact huv (hinj hvec)

/-- If every coordinate column is constant-or-injective and the tuple is not completely constant,
then the five words are distinct. -/
theorem injective_of_columnwiseConstantOrInjective5_of_not_allEqual
    {n : ℕ} {x : Fin 5 → QuinaryWord n} (hcol : ColumnwiseConstantOrInjective5 x)
    (hall : ¬ ∀ t : Fin 5, x t = x 0) :
    Function.Injective x := by
  intro u v huvEq
  by_contra huv
  have hAllU : ∀ t : Fin 5, x t = x u :=
    allEqual_of_columnwiseConstantOrInjective5_of_eq hcol huv huvEq
  apply hall
  intro t
  calc
    x t = x u := hAllU t
    _ = x 0 := by simpa using (hAllU 0).symm

/-- On an injective `5`-tuple from a `5`-sunflower-free family, the explicit tensor vanishes. -/
theorem explicitGlobalTensor5Tuple_eq_zero_of_sunflowerFree
    {n : ℕ} {C : Finset (QuinaryWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V5) C) 5)
    {x : Fin 5 → QuinaryWord n} (hxC : ∀ t, x t ∈ C) (hxinj : Function.Injective x) :
    explicitGlobalTensor5Tuple x = 0 := by
  by_contra hne
  have hcol : ColumnwiseConstantOrInjective5 x :=
    columnwiseConstantOrInjective5_of_explicitGlobalTensor5_ne_zero hne
  have hSun : IsSunflowerTuple (fun t => transversalEdge (x t)) :=
    hcol.isSunflowerTuple_transversal
  have hEdgeInj : Function.Injective (fun t => transversalEdge (x t)) := by
    intro u v huv
    exact hxinj (transversalEdge_injective huv)
  have hmem : ∀ t, transversalEdge (x t) ∈ transversalFamily (G := V5) C := by
    intro t
    exact Finset.mem_image.mpr ⟨x t, hxC t, rfl⟩
  exact hfree (fun t => transversalEdge (x t)) hmem hEdgeInj hSun

theorem explicitGlobalTensor5Tuple_eq_one_of_allEqual
    {n : ℕ} {x : Fin 5 → QuinaryWord n} (hall : ∀ t : Fin 5, x t = x 0) :
    explicitGlobalTensor5Tuple x = 1 := by
  unfold explicitGlobalTensor5Tuple
  refine Finset.prod_eq_one ?_
  intro i hi
  rw [explicitLocalTensor5_eq_one_iff_constantOrInjective]
  refine Or.inl ?_
  constructor
  · simpa using congrArg (fun f : QuinaryWord n => f i) (hall 1).symm
  constructor
  · calc
      x 1 i = x 0 i := by simpa using congrArg (fun f : QuinaryWord n => f i) (hall 1)
      _ = x 2 i := by simpa using congrArg (fun f : QuinaryWord n => f i) (hall 2).symm
  constructor
  · calc
      x 2 i = x 0 i := by simpa using congrArg (fun f : QuinaryWord n => f i) (hall 2)
      _ = x 3 i := by simpa using congrArg (fun f : QuinaryWord n => f i) (hall 3).symm
  · calc
      x 3 i = x 0 i := by simpa using congrArg (fun f : QuinaryWord n => f i) (hall 3)
      _ = x 4 i := by simpa using congrArg (fun f : QuinaryWord n => f i) (hall 4).symm

/-- On a `5`-sunflower-free code over `F_5`, the explicit global tensor is diagonal: among tuples
from the family it survives exactly on the all-equal tuples. -/
theorem explicitGlobalTensor5Tuple_eq_ite_allEqual_of_sunflowerFree
    {n : ℕ} {C : Finset (QuinaryWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V5) C) 5)
    {x : Fin 5 → QuinaryWord n} (hxC : ∀ t, x t ∈ C) :
    explicitGlobalTensor5Tuple x = if ∀ t : Fin 5, x t = x 0 then 1 else 0 := by
  by_cases hall : ∀ t : Fin 5, x t = x 0
  · simp [hall, explicitGlobalTensor5Tuple_eq_one_of_allEqual hall]
  · have hzero : explicitGlobalTensor5Tuple x = 0 := by
      by_contra hne
      have hcol : ColumnwiseConstantOrInjective5 x :=
        columnwiseConstantOrInjective5_of_explicitGlobalTensor5_ne_zero hne
      have hxinj : Function.Injective x :=
        injective_of_columnwiseConstantOrInjective5_of_not_allEqual hcol hall
      exact hne (explicitGlobalTensor5Tuple_eq_zero_of_sunflowerFree hfree hxC hxinj)
    simp [hall, hzero]

/-- Restatement of the pasted global diagonalization claim: on a `5`-sunflower-free transversal
code, the global tensor survives exactly on all-equal `5`-tuples from the code. -/
theorem pasted_quinary_global_tensor_diagonalization
    {n : ℕ} {C : Finset (QuinaryWord n)}
    (hfree : SunflowerFree (transversalFamily (G := V5) C) 5)
    {x : Fin 5 → QuinaryWord n} (hxC : ∀ t, x t ∈ C) :
    explicitGlobalTensor5Tuple x = if ∀ t : Fin 5, x t = x 0 then 1 else 0 :=
  explicitGlobalTensor5Tuple_eq_ite_allEqual_of_sunflowerFree hfree hxC

end GlobalTensor

end FormalConjectures.Problems.Erdos.E20
