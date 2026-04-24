import FormalConjectures.Problems.Erdos.E61.PathInfrastructure

/-!
# Terminal profile obstructions

This file formalizes the induced-path core of `prop:terminal-rigid`: if the two
terminal profile classes are not complete to each other, the displayed witness
path exists.  The concrete graph below is the path `Q`, one vertex with profile
`{q_{k-2},q_{k-1}}`, and one vertex with profile
`{q_{k-3},q_{k-2},q_{k-1}}`, with no edge between the two outside vertices.
-/

namespace Erdos61

/-- Profile `{q_{k-2}, q_{k-1}}` in zero-based coordinates. -/
def terminalProfileA {n : ℕ} (i : Fin (n + 4)) : Prop :=
  i.val = n + 2 ∨ i.val = n + 3

/-- Profile `{q_{k-3}, q_{k-2}, q_{k-1}}` in zero-based coordinates. -/
def terminalProfileB {n : ℕ} (i : Fin (n + 4)) : Prop :=
  i.val = n + 1 ∨ i.val = n + 2 ∨ i.val = n + 3

/-- Raw directed relation for the terminal rigid obstruction graph. -/
def terminalRigidRel (n : ℕ) :
    Sum (Fin (n + 4)) Bool → Sum (Fin (n + 4)) Bool → Prop
  | Sum.inl i, Sum.inl j => (SimpleGraph.pathGraph (n + 4)).Adj i j
  | Sum.inl i, Sum.inr false => terminalProfileA i
  | Sum.inl i, Sum.inr true => terminalProfileB i
  | _, _ => False

/--
The terminal rigid obstruction graph.  `false` is the `A` vertex and `true` is
the `B` vertex.
-/
def terminalRigidGraph (n : ℕ) : SimpleGraph (Sum (Fin (n + 4)) Bool) :=
  SimpleGraph.fromRel (terminalRigidRel n)

@[simp] theorem terminalRigid_adj_path_path (n : ℕ) (i j : Fin (n + 4)) :
    (terminalRigidGraph n).Adj (Sum.inl i) (Sum.inl j) ↔
      (SimpleGraph.pathGraph (n + 4)).Adj i j := by
  constructor
  · intro h
    rcases (SimpleGraph.fromRel_adj (terminalRigidRel n) (Sum.inl i) (Sum.inl j)).mp h with
      ⟨_hne, hrel | hrel⟩
    · exact hrel
    · exact hrel.symm
  · intro h
    exact (SimpleGraph.fromRel_adj (terminalRigidRel n) (Sum.inl i) (Sum.inl j)).mpr
      ⟨by simp [h.ne], Or.inl h⟩

@[simp] theorem terminalRigid_adj_path_A (n : ℕ) (i : Fin (n + 4)) :
    (terminalRigidGraph n).Adj (Sum.inl i) (Sum.inr false) ↔ terminalProfileA i := by
  simp [terminalRigidGraph, terminalRigidRel, SimpleGraph.fromRel_adj]

@[simp] theorem terminalRigid_adj_A_path (n : ℕ) (i : Fin (n + 4)) :
    (terminalRigidGraph n).Adj (Sum.inr false) (Sum.inl i) ↔ terminalProfileA i := by
  rw [(terminalRigidGraph n).adj_comm]
  simp

@[simp] theorem terminalRigid_adj_path_B (n : ℕ) (i : Fin (n + 4)) :
    (terminalRigidGraph n).Adj (Sum.inl i) (Sum.inr true) ↔ terminalProfileB i := by
  simp [terminalRigidGraph, terminalRigidRel, SimpleGraph.fromRel_adj]

@[simp] theorem terminalRigid_adj_B_path (n : ℕ) (i : Fin (n + 4)) :
    (terminalRigidGraph n).Adj (Sum.inr true) (Sum.inl i) ↔ terminalProfileB i := by
  rw [(terminalRigidGraph n).adj_comm]
  simp

@[simp] theorem terminalRigid_not_adj_outside_outside (n : ℕ) (a b : Bool) :
    ¬ (terminalRigidGraph n).Adj (Sum.inr a : Sum (Fin (n + 4)) Bool) (Sum.inr b) := by
  simp [terminalRigidGraph, terminalRigidRel, SimpleGraph.fromRel_adj]

/--
The witness path:
`q_1-...-q_{k-3}-B-q_{k-1}-A`, with `q_{k-2}` skipped.
-/
def terminalRigidWitnessVertex (n : ℕ) (i : Fin (n + 5)) :
    Sum (Fin (n + 4)) Bool :=
  if h₁ : i.val ≤ n + 1 then
    Sum.inl ⟨i.val, by omega⟩
  else if h₂ : i.val = n + 2 then
    Sum.inr true
  else if h₃ : i.val = n + 3 then
    Sum.inl ⟨n + 3, by omega⟩
  else
    Sum.inr false

/-- Numeric position of a witness vertex in the displayed path. -/
def terminalRigidWitnessCode (n : ℕ) : Sum (Fin (n + 4)) Bool → ℕ
  | Sum.inl i => i.val
  | Sum.inr true => n + 2
  | Sum.inr false => n + 4

set_option linter.unusedSimpArgs false in
@[simp] theorem terminalRigidWitnessCode_vertex (n : ℕ) (i : Fin (n + 5)) :
    terminalRigidWitnessCode n (terminalRigidWitnessVertex n i) = i.val := by
  rw [terminalRigidWitnessVertex]
  by_cases h₁ : i.val ≤ n + 1
  · simp [h₁, terminalRigidWitnessCode]
  · by_cases h₂ : i.val = n + 2
    · simp [h₁, h₂, terminalRigidWitnessCode]
    · by_cases h₃ : i.val = n + 3
      · simp [h₁, h₂, h₃, terminalRigidWitnessCode]
      · have hlast : i.val = n + 4 := by omega
        simp [h₁, h₂, h₃, hlast, terminalRigidWitnessCode]

set_option linter.flexible false in
theorem terminalRigidWitnessVertex_injective (n : ℕ) :
    Function.Injective (terminalRigidWitnessVertex n) := by
  intro i j hij
  have hval := congrArg (terminalRigidWitnessCode n) hij
  simp at hval
  exact Fin.ext hval

set_option linter.unusedSimpArgs false in
theorem terminalRigidWitness_adj_iff (n : ℕ) (i j : Fin (n + 5)) :
    (terminalRigidGraph n).Adj (terminalRigidWitnessVertex n i)
        (terminalRigidWitnessVertex n j) ↔
      (SimpleGraph.pathGraph (n + 5)).Adj i j := by
  rw [SimpleGraph.pathGraph_adj]
  rw [terminalRigidWitnessVertex, terminalRigidWitnessVertex]
  by_cases hi₁ : i.val ≤ n + 1
  · by_cases hj₁ : j.val ≤ n + 1
    · simp [hi₁, hj₁, SimpleGraph.pathGraph_adj]
    · by_cases hj₂ : j.val = n + 2
      · simp [hi₁, hj₁, hj₂, terminalProfileB]
        omega
      · by_cases hj₃ : j.val = n + 3
        · simp [hi₁, hj₁, hj₂, hj₃, SimpleGraph.pathGraph_adj]
        · have hj₄ : j.val = n + 4 := by omega
          simp [hi₁, hj₁, hj₂, hj₃, hj₄, terminalProfileA]
          omega
  · by_cases hi₂ : i.val = n + 2
    · by_cases hj₁ : j.val ≤ n + 1
      · simp [hi₁, hi₂, hj₁, terminalProfileB]
        omega
      · by_cases hj₂ : j.val = n + 2
        · simp [hi₁, hi₂, hj₁, hj₂]
        · by_cases hj₃ : j.val = n + 3
          · simp [hi₁, hi₂, hj₁, hj₂, hj₃, terminalProfileB]
          · have hj₄ : j.val = n + 4 := by omega
            simp [hi₁, hi₂, hj₁, hj₂, hj₃, hj₄]
    · by_cases hi₃ : i.val = n + 3
      · by_cases hj₁ : j.val ≤ n + 1
        · simp [hi₁, hi₂, hi₃, hj₁, SimpleGraph.pathGraph_adj]
        · by_cases hj₂ : j.val = n + 2
          · simp [hi₁, hi₂, hi₃, hj₁, hj₂, terminalProfileB]
          · by_cases hj₃ : j.val = n + 3
            · simp [hi₁, hi₂, hi₃, hj₁, hj₂, hj₃, SimpleGraph.pathGraph_adj]
            · have hj₄ : j.val = n + 4 := by omega
              simp [hi₁, hi₂, hi₃, hj₁, hj₂, hj₃, hj₄, terminalProfileA]
      · have hi₄ : i.val = n + 4 := by omega
        by_cases hj₁ : j.val ≤ n + 1
        · simp [hi₁, hi₂, hi₃, hi₄, hj₁, terminalProfileA]
          omega
        · by_cases hj₂ : j.val = n + 2
          · simp [hi₁, hi₂, hi₃, hi₄, hj₁, hj₂]
          · by_cases hj₃ : j.val = n + 3
            · simp [hi₁, hi₂, hi₃, hi₄, hj₁, hj₂, hj₃, terminalProfileA]
            · have hj₄ : j.val = n + 4 := by omega
              simp [hi₁, hi₂, hi₃, hi₄, hj₁, hj₂, hj₃, hj₄]

/-- Concrete induced-path witness behind `prop:terminal-rigid`. -/
noncomputable def terminalRigidObstructionEmbedding (n : ℕ) :
    SimpleGraph.pathGraph (n + 5) ↪g terminalRigidGraph n where
  toFun := terminalRigidWitnessVertex n
  inj' := terminalRigidWitnessVertex_injective n
  map_rel_iff' := by
    intro i j
    exact terminalRigidWitness_adj_iff n i j

theorem terminal_rigid_nonedge_contains_path (n : ℕ) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 5)) (terminalRigidGraph n) :=
  ⟨terminalRigidObstructionEmbedding n⟩

/-- Map the concrete terminal-rigid obstruction into an ambient graph. -/
def terminalRigidAmbientMap {V : Type*} {n : ℕ} (q : Fin (n + 4) → V) (a b : V) :
    Sum (Fin (n + 4)) Bool → V
  | Sum.inl i => q i
  | Sum.inr false => a
  | Sum.inr true => b

theorem terminalRigidAmbientMap_injective {V : Type*} {n : ℕ}
    {q : Fin (n + 4) → V} {a b : V}
    (hq : Function.Injective q)
    (haq : ∀ i, a ≠ q i) (hbq : ∀ i, b ≠ q i) (hab : a ≠ b) :
    Function.Injective (terminalRigidAmbientMap q a b) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          exact congrArg Sum.inl (hq hxy)
      | inr s =>
          cases s
          · exact False.elim ((haq i) hxy.symm)
          · exact False.elim ((hbq i) hxy.symm)
  | inr s =>
      cases s
      · cases y with
        | inl j => exact False.elim ((haq j) hxy)
        | inr t =>
            cases t
            · rfl
            · exact False.elim (hab hxy)
      · cases y with
        | inl j => exact False.elim ((hbq j) hxy)
        | inr t =>
            cases t
            · exact False.elim (hab hxy.symm)
            · rfl

/--
Embedding of the concrete terminal obstruction into any ambient graph with an
induced path `q`, outside vertices `a` and `b` having terminal profiles `A` and
`B`, and a missing `ab` edge.
-/
noncomputable def terminalRigidAmbientEmbedding {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (q : Fin (n + 4) → V) (a b : V)
    (hq : Function.Injective q)
    (haq : ∀ i, a ≠ q i) (hbq : ∀ i, b ≠ q i) (hab : a ≠ b)
    (hpath : ∀ i j, G.Adj (q i) (q j) ↔ (SimpleGraph.pathGraph (n + 4)).Adj i j)
    (hA : ∀ i, G.Adj (q i) a ↔ terminalProfileA i)
    (hB : ∀ i, G.Adj (q i) b ↔ terminalProfileB i)
    (hnab : ¬ G.Adj a b) :
    terminalRigidGraph n ↪g G where
  toFun := terminalRigidAmbientMap q a b
  inj' := terminalRigidAmbientMap_injective hq haq hbq hab
  map_rel_iff' := by
    intro x y
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            change G.Adj (q i) (q j) ↔ (terminalRigidGraph n).Adj (Sum.inl i) (Sum.inl j)
            simpa using hpath i j
        | inr s =>
            cases s
            · change G.Adj (q i) a ↔
                (terminalRigidGraph n).Adj (Sum.inl i) (Sum.inr false)
              simpa using hA i
            · change G.Adj (q i) b ↔
                (terminalRigidGraph n).Adj (Sum.inl i) (Sum.inr true)
              simpa using hB i
    | inr s =>
        cases s
        · cases y with
          | inl j =>
              change G.Adj a (q j) ↔ (terminalRigidGraph n).Adj (Sum.inr false) (Sum.inl j)
              rw [G.adj_comm]
              simpa using hA j
          | inr t =>
              cases t
              · simp
              · constructor
                · intro h
                  exact False.elim (hnab h)
                · intro h
                  simp [terminalRigid_not_adj_outside_outside] at h
        · cases y with
          | inl j =>
              change G.Adj b (q j) ↔ (terminalRigidGraph n).Adj (Sum.inr true) (Sum.inl j)
              rw [G.adj_comm]
              simpa using hB j
          | inr t =>
              cases t
              · constructor
                · intro h
                  exact False.elim (hnab h.symm)
                · intro h
                  simp [terminalRigid_not_adj_outside_outside] at h
              · simp

/--
Ambient form of `prop:terminal-rigid`: a nonedge between the terminal `B` and
`A` profile classes produces the displayed induced path.
-/
theorem terminal_rigid_ambient_nonedge_contains_path {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (q : Fin (n + 4) → V) (a b : V)
    (hq : Function.Injective q)
    (haq : ∀ i, a ≠ q i) (hbq : ∀ i, b ≠ q i) (hab : a ≠ b)
    (hpath : ∀ i j, G.Adj (q i) (q j) ↔ (SimpleGraph.pathGraph (n + 4)).Adj i j)
    (hA : ∀ i, G.Adj (q i) a ↔ terminalProfileA i)
    (hB : ∀ i, G.Adj (q i) b ↔ terminalProfileB i)
    (hnab : ¬ G.Adj a b) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 5)) G := by
  exact ⟨(terminalRigidAmbientEmbedding q a b hq haq hbq hab hpath hA hB hnab).comp
    (terminalRigidObstructionEmbedding n)⟩

end Erdos61
