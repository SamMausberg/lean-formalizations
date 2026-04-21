import Mathlib

namespace FormalConjectures.Problems.Erdos.E20

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

/-!
# Finite-State Profitable Prefix Chains

This file formalizes the exact finite-state recursion behind the user's sliding-window note.
We work with a finite directed edge system.  The continuation count from a state satisfies the
transfer recursion, and any positive superharmonic weight produces a profitable chain of prefixes.

The development is intentionally stated in terms of edge paths and continuation counts.  This is
the exact combinatorial core of the finite-state / sliding-window argument.
-/

section Core

variable {Q E : Type*} [Fintype Q] [DecidableEq Q] [Fintype E] [DecidableEq E]

/-- A finite directed edge system.  Distinct edges are distinct one-step symbols. -/
structure EdgeShift where
  src : E → Q
  dst : E → Q

namespace EdgeShift

/-- The outgoing edges from a state. -/
def outEdges (A : EdgeShift (Q := Q) (E := E)) (q : Q) : Finset E :=
  Finset.univ.filter fun e => A.src e = q

@[simp] theorem mem_outEdges_iff {A : EdgeShift (Q := Q) (E := E)} {q : Q} {e : E} :
    e ∈ A.outEdges q ↔ A.src e = q := by
  simp [outEdges]

/-- The number of admissible length-`n` continuations from state `q`. -/
def continuationCount (A : EdgeShift (Q := Q) (E := E)) : ℕ → Q → ℕ
  | 0, _ => 1
  | n + 1, q => Finset.sum (A.outEdges q) fun e => continuationCount A n (A.dst e)

@[simp] theorem continuationCount_zero (A : EdgeShift (Q := Q) (E := E)) (q : Q) :
    A.continuationCount 0 q = 1 := rfl

@[simp] theorem continuationCount_succ (A : EdgeShift (Q := Q) (E := E)) (n : ℕ) (q : Q) :
    A.continuationCount (n + 1) q =
      Finset.sum (A.outEdges q) fun e => A.continuationCount n (A.dst e) := rfl

/-- A positive superharmonic weight for the transfer operator. -/
def IsSuperharmonic (A : EdgeShift (Q := Q) (E := E)) (h : Q → ℝ) (Λ : ℝ) : Prop :=
  ∀ q, Finset.sum (A.outEdges q) (fun e => h (A.dst e)) ≤ Λ * h q

/-- The transfer-root candidate: infimum of all superharmonic constants. -/
noncomputable def transferRoot (A : EdgeShift (Q := Q) (E := E)) : ℝ :=
  sInf {Λ : ℝ | ∃ h : Q → ℝ, (∀ q, 0 < h q) ∧ A.IsSuperharmonic h Λ}

/-- The transfer matrix recording how many edges run from each state to each next state. -/
noncomputable def transferMatrix (A : EdgeShift (Q := Q) (E := E)) : Matrix Q Q ℝ :=
  fun p q => Fintype.card {e : E // A.src e = p ∧ A.dst e = q}

/-- The normalized continuation count `Φ_m(q) = N_m(q) / (Λ^m h(q))`. -/
noncomputable def phi (A : EdgeShift (Q := Q) (E := E)) (h : Q → ℝ) (Λ : ℝ) (m : ℕ) (q : Q) : ℝ :=
  (A.continuationCount m q : ℝ) / (Λ ^ m * h q)

theorem outEdges_nonempty_of_continuationCount_pos
    {A : EdgeShift (Q := Q) (E := E)} {m : ℕ} {q : Q}
    (hcount : 0 < A.continuationCount (m + 1) q) :
    (A.outEdges q).Nonempty := by
  by_contra hEmpty
  have hEq : A.outEdges q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
  rw [A.continuationCount_succ, hEq, Finset.sum_empty] at hcount
  omega

theorem phi_nonneg
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q) (m : ℕ) (q : Q) :
    0 ≤ A.phi h Λ m q := by
  unfold phi
  have hnum : 0 ≤ (A.continuationCount m q : ℝ) := by positivity
  have hpow : 0 ≤ Λ ^ m := by positivity
  have hden : 0 ≤ Λ ^ m * h q := mul_nonneg hpow (le_of_lt (hh q))
  exact div_nonneg hnum hden

theorem phi_pos_of_continuationCount_pos
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q) {m : ℕ} {q : Q}
    (hcount : 0 < A.continuationCount m q) :
    0 < A.phi h Λ m q := by
  unfold phi
  have hnum : 0 < (A.continuationCount m q : ℝ) := by exact_mod_cast hcount
  have hpow : 0 < Λ ^ m := by positivity
  have hden : 0 < Λ ^ m * h q := mul_pos hpow (hh q)
  exact div_pos hnum hden

theorem mul_phi_succ_eq_sum
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q) (m : ℕ) (q : Q) :
    (Λ * h q) * A.phi h Λ (m + 1) q =
      Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ m (A.dst e)) := by
  have hterm :
      ∀ e : E,
        h (A.dst e) * A.phi h Λ m (A.dst e) =
          (A.continuationCount m (A.dst e) : ℝ) / Λ ^ m := by
    intro e
    unfold phi
    field_simp [hΛ.ne', (hh (A.dst e)).ne']
  calc
    (Λ * h q) * A.phi h Λ (m + 1) q
        = (Λ * h q) *
            ((A.continuationCount (m + 1) q : ℝ) / (Λ ^ (m + 1) * h q)) := by
              rfl
    _ = (A.continuationCount (m + 1) q : ℝ) / Λ ^ m := by
          field_simp [hΛ.ne', (hh q).ne']
          ring
    _ = Finset.sum (A.outEdges q) (fun e => (A.continuationCount m (A.dst e) : ℝ) / Λ ^ m) := by
          rw [A.continuationCount_succ, Nat.cast_sum]
          rw [Finset.sum_div]
    _ = Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ m (A.dst e)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [hterm e]

/-- One-step profitable move in the finite-state model. -/
theorem exists_outEdge_ge_phi
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hsuper : A.IsSuperharmonic h Λ) (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q)
    {m : ℕ} {q : Q} (hcount : 0 < A.continuationCount (m + 1) q) :
    ∃ e ∈ A.outEdges q, A.phi h Λ m (A.dst e) ≥ A.phi h Λ (m + 1) q := by
  have hOut : (A.outEdges q).Nonempty := A.outEdges_nonempty_of_continuationCount_pos hcount
  by_contra hNo
  have hlt :
      ∀ e ∈ A.outEdges q,
        h (A.dst e) * A.phi h Λ m (A.dst e) <
          h (A.dst e) * A.phi h Λ (m + 1) q := by
    intro e he
    have hphi :
        A.phi h Λ m (A.dst e) < A.phi h Λ (m + 1) q := by
      by_contra hge
      exact hNo ⟨e, he, le_of_not_gt hge⟩
    nlinarith [hh (A.dst e)]
  have hsumlt :
      Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ m (A.dst e)) <
        Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ (m + 1) q) := by
    exact Finset.sum_lt_sum_of_nonempty hOut hlt
  have hphi_nonneg : 0 ≤ A.phi h Λ (m + 1) q := A.phi_nonneg hΛ hh (m + 1) q
  have hsumle :
      Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ (m + 1) q) ≤
        Λ * h q * A.phi h Λ (m + 1) q := by
    calc
      Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ (m + 1) q)
          = A.phi h Λ (m + 1) q * Finset.sum (A.outEdges q) (fun e => h (A.dst e)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro e he
              ring
      _ ≤ A.phi h Λ (m + 1) q * (Λ * h q) := by
            gcongr
            exact hsuper q
      _ = Λ * h q * A.phi h Λ (m + 1) q := by ring
  have hEq := A.mul_phi_succ_eq_sum hΛ hh m q
  have : Λ * h q * A.phi h Λ (m + 1) q < Λ * h q * A.phi h Λ (m + 1) q := by
    calc
      Λ * h q * A.phi h Λ (m + 1) q
          = Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ m (A.dst e)) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hEq
      _ < Finset.sum (A.outEdges q) (fun e => h (A.dst e) * A.phi h Λ (m + 1) q) := hsumlt
      _ ≤ Λ * h q * A.phi h Λ (m + 1) q := hsumle
  exact lt_irrefl _ this

/-- A finite chain of states and edges. -/
abbrev StateChain (Q : Type*) (n : ℕ) := Fin (n + 1) → Q
abbrev EdgeChain (E : Type*) (n : ℕ) := Fin n → E

/-- Exact profitable-prefix chain in the finite-state model, stated for normalized counts. -/
theorem exists_phi_chain
    {A : EdgeShift (Q := Q) (E := E)} {h : Q → ℝ} {Λ : ℝ}
    (hsuper : A.IsSuperharmonic h Λ) (hΛ : 0 < Λ) (hh : ∀ q, 0 < h q)
    {n : ℕ} {s : Q} (hcount : 0 < A.continuationCount n s) :
    ∃ q : StateChain Q n, ∃ e : EdgeChain E n,
      q 0 = s ∧
      (∀ i : Fin n, e i ∈ A.outEdges (q i.castSucc) ∧ A.dst (e i) = q i.succ) ∧
      ∀ t : Fin (n + 1), A.phi h Λ (n - t) (q t) ≥ A.phi h Λ n s := by
  induction n generalizing s with
  | zero =>
      refine ⟨fun _ => s, fun i => Fin.elim0 i, rfl, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro t
        have : t = 0 := by fin_cases t <;> rfl
        subst this
        simp [phi]
  | succ n ih =>
      rcases A.exists_outEdge_ge_phi hsuper hΛ hh hcount with ⟨e0, he0, hphi0⟩
      have hnextCount : 0 < A.continuationCount n (A.dst e0) := by
        have hphi_pos : 0 < A.phi h Λ (n + 1) s := A.phi_pos_of_continuationCount_pos hΛ hh hcount
        have : 0 < A.phi h Λ n (A.dst e0) := lt_of_lt_of_le hphi_pos hphi0
        have hpow : 0 < Λ ^ n := by positivity
        have hden : 0 < Λ ^ n * h (A.dst e0) := mul_pos hpow (hh (A.dst e0))
        unfold phi at this
        have hnum : 0 < (A.continuationCount n (A.dst e0) : ℝ) := by
          have hmul : 0 < ((A.continuationCount n (A.dst e0) : ℝ) / (Λ ^ n * h (A.dst e0))) *
              (Λ ^ n * h (A.dst e0)) := mul_pos this hden
          have hEqMul :
              ((A.continuationCount n (A.dst e0) : ℝ) / (Λ ^ n * h (A.dst e0))) *
                  (Λ ^ n * h (A.dst e0)) =
                (A.continuationCount n (A.dst e0) : ℝ) := by
            field_simp [hden.ne', (hh (A.dst e0)).ne']
          rw [hEqMul] at hmul
          exact hmul
        exact_mod_cast hnum
      rcases ih (s := A.dst e0) hnextCount with ⟨qTail, eTail, hq0, hEdgesTail, hPhiTail⟩
      refine ⟨Fin.cons s qTail, Fin.cons e0 eTail, by simp, ?_, ?_⟩
      · rw [Fin.forall_fin_succ]
        constructor
        · exact ⟨by simpa using he0, by simpa [hq0]⟩
        · intro i
          simpa using hEdgesTail i
      · rw [Fin.forall_fin_succ]
        constructor
        · simpa using le_rfl
        · intro t
          have hTail := hPhiTail t
          have hStep := hphi0
          simpa using le_trans hStep hTail

end EdgeShift

end Core

section Examples

/-- The one-state `d`-regular system. -/
def regularOneState (d : ℕ) : EdgeShift (Q := Unit) (E := Fin d) where
  src := fun _ => ()
  dst := fun _ => ()

theorem continuationCount_regularOneState (d n : ℕ) :
    (regularOneState d).continuationCount n () = d ^ n := by
  induction n with
  | zero =>
      simp [regularOneState]
  | succ n ih =>
      rw [(regularOneState d).continuationCount_succ]
      simp [regularOneState, ih, pow_succ, EdgeShift.outEdges, Nat.mul_comm]

/-- In the one-state `d`-regular system, a positive superharmonic weight exists at level `Λ`
exactly when `d ≤ Λ`. -/
theorem isSuperharmonic_regularOneState_iff
    (d : ℕ) (h : Unit → ℝ) (Λ : ℝ) (hh : 0 < h ()) :
    (regularOneState d).IsSuperharmonic h Λ ↔ (d : ℝ) ≤ Λ := by
  constructor
  · intro hsuper
    have hineq := hsuper ()
    simp [regularOneState, EdgeShift.outEdges] at hineq
    nlinarith
  · intro hΛ q
    cases q
    simp [regularOneState, EdgeShift.outEdges]
    nlinarith

/-- The transfer root of the one-state `d`-regular system is exactly `d`.  This is the precise
finite-state sharpness statement behind the full block-product / de Bruijn obstruction. -/
theorem transferRoot_regularOneState (d : ℕ) :
    (regularOneState d).transferRoot = d := by
  let S : Set ℝ :=
    {Λ : ℝ | ∃ h : Unit → ℝ, (∀ q, 0 < h q) ∧ (regularOneState d).IsSuperharmonic h Λ}
  have hS : S = Set.Ici (d : ℝ) := by
    ext Λ
    constructor
    · rintro ⟨h, hh, hsuper⟩
      exact (isSuperharmonic_regularOneState_iff d h Λ (hh ())).1 hsuper
    · intro hΛ
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro q
        cases q
        norm_num
      · exact (isSuperharmonic_regularOneState_iff d (fun _ => 1) Λ (by norm_num)).2 hΛ
  unfold EdgeShift.transferRoot
  rw [show {Λ : ℝ | ∃ h : Unit → ℝ, (∀ q, 0 < h q) ∧ (regularOneState d).IsSuperharmonic h Λ} = S by
    rfl]
  rw [hS, csInf_Ici]

/-- The two-state, three-edge system `0 --a,b--> 1 --c--> 0`. -/
inductive TwoState
  | zero
  | one
  deriving DecidableEq, Fintype

inductive TwoEdge
  | a
  | b
  | c
  deriving DecidableEq, Fintype

def twoStateCounterexample : EdgeShift (Q := TwoState) (E := TwoEdge) where
  src
    | .a => .zero
    | .b => .zero
    | .c => .one
  dst
    | .a => .one
    | .b => .one
    | .c => .zero

set_option linter.style.nativeDecide false in
@[simp] theorem continuationCount_twoState_zero_one :
    twoStateCounterexample.continuationCount 1 TwoState.zero = 2 := by
  native_decide

set_option linter.style.nativeDecide false in
@[simp] theorem continuationCount_twoState_zero_two :
    twoStateCounterexample.continuationCount 2 TwoState.zero = 2 := by
  native_decide

set_option linter.style.nativeDecide false in
@[simp] theorem continuationCount_twoState_one_one :
    twoStateCounterexample.continuationCount 1 TwoState.one = 1 := by
  native_decide

/-- Every one-edge prefix from state `0` has exactly half the total length-`2`
continuation count. -/
theorem twoState_firstPrefix_is_half :
    (twoStateCounterexample.continuationCount 1 TwoState.one : ℝ) =
      (1 / 2 : ℝ) * twoStateCounterexample.continuationCount 2 TwoState.zero := by
  rw [continuationCount_twoState_one_one, continuationCount_twoState_zero_two]
  norm_num

/-- The naive unweighted `ρ^{-1}` lower bound fails in the two-state counterexample at
`ρ = √2`, since `1 / 2 < 1 / √2`. -/
theorem one_half_lt_inv_sqrt_two : (1 / 2 : ℝ) < 1 / Real.sqrt 2 := by
  have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt_lt_two : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  exact (one_div_lt_one_div (by positivity) hsqrt_pos).2 hsqrt_lt_two

/-- The weighted superharmonic vector `(√2, 1)` is exact for the two-state counterexample. -/
theorem twoStateCounterexample_isSuperharmonic :
    twoStateCounterexample.IsSuperharmonic
      (fun q => match q with | .zero => Real.sqrt 2 | .one => 1)
      (Real.sqrt 2) := by
  intro q
  cases q
  · have hOut :
        twoStateCounterexample.outEdges TwoState.zero = {TwoEdge.a, TwoEdge.b} := by
        ext e
        cases e <;> simp [EdgeShift.outEdges, twoStateCounterexample]
    rw [hOut]
    simp [twoStateCounterexample]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  · have hOut :
        twoStateCounterexample.outEdges TwoState.one = {TwoEdge.c} := by
        ext e
        cases e <;> simp [EdgeShift.outEdges, twoStateCounterexample]
    rw [hOut]
    simp [twoStateCounterexample]

end Examples

end FormalConjectures.Problems.Erdos.E20
