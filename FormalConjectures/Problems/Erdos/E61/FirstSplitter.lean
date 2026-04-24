import FormalConjectures.Problems.Erdos.E61.TerminalBlowup
import FormalConjectures.Problems.Erdos.E61.SafeProfileFamily

/-!
# First-splitter graph package

This file defines the exact graph model used in `thm:first-splitter` and proves
the interface is induced exactly as prescribed.  It also proves the formal
`only if` direction of the path-freeness equivalence: any forbidden path in the
interface is a forbidden path in the first-splitter graph.
-/

namespace Erdos61

open Finset

variable {A B : Type*}

/-- The terminal two-vertex profile `S={q_{k-2},q_{k-1}}` in local indexing. -/
def firstSplitterS (n : ℕ) : Finset (Fin (n + 1)) :=
  terminalBlowupProfile n

/-- The first-splitter profile `T={q_{k-4},q_{k-2},q_{k-1}}` in local indexing. -/
def firstSplitterT (n : ℕ) : Finset (Fin (n + 1)) :=
  {⟨n - 3, by omega⟩, ⟨n - 1, by omega⟩, ⟨n, by omega⟩}

/-- The bipartite interface graph with edge relation `R` between the two sides. -/
def firstSplitterInterfaceRel (R : A → B → Prop) : Sum A B → Sum A B → Prop
  | Sum.inl a, Sum.inr b => R a b
  | _, _ => False

/-- The interface graph used as the outside part of the first splitter. -/
def firstSplitterInterfaceGraph (R : A → B → Prop) : SimpleGraph (Sum A B) :=
  SimpleGraph.fromRel (firstSplitterInterfaceRel R)

@[simp] theorem firstSplitterInterface_adj_left_right (R : A → B → Prop) (a : A) (b : B) :
    (firstSplitterInterfaceGraph R).Adj (Sum.inl a) (Sum.inr b) ↔ R a b := by
  simp [firstSplitterInterfaceGraph, firstSplitterInterfaceRel, SimpleGraph.fromRel_adj]

@[simp] theorem firstSplitterInterface_adj_right_left (R : A → B → Prop) (a : A) (b : B) :
    (firstSplitterInterfaceGraph R).Adj (Sum.inr b) (Sum.inl a) ↔ R a b := by
  rw [(firstSplitterInterfaceGraph R).adj_comm]
  simp

@[simp] theorem firstSplitterInterface_not_adj_left_left (R : A → B → Prop) (a a' : A) :
    ¬ (firstSplitterInterfaceGraph R).Adj (Sum.inl a) (Sum.inl a') := by
  simp [firstSplitterInterfaceGraph, firstSplitterInterfaceRel, SimpleGraph.fromRel_adj]

@[simp] theorem firstSplitterInterface_not_adj_right_right (R : A → B → Prop) (b b' : B) :
    ¬ (firstSplitterInterfaceGraph R).Adj (Sum.inr b) (Sum.inr b') := by
  simp [firstSplitterInterfaceGraph, firstSplitterInterfaceRel, SimpleGraph.fromRel_adj]

/-- Outside vertices on the `A` side receive profile `S`; `B` side vertices receive `T`. -/
def firstSplitterProfile (n : ℕ) : Sum A B → Finset (Fin (n + 1))
  | Sum.inl _ => firstSplitterS n
  | Sum.inr _ => firstSplitterT n

/-- The first-splitter graph: a path on `n+1` vertices plus the bipartite interface. -/
def firstSplitterGraph (n : ℕ) (R : A → B → Prop) :
    SimpleGraph (Sum (Fin (n + 1)) (Sum A B)) :=
  profileBlowup (firstSplitterInterfaceGraph R) (firstSplitterProfile n)

@[simp] theorem firstSplitterGraph_interface_adj (n : ℕ) (R : A → B → Prop)
    (u v : Sum A B) :
    (firstSplitterGraph n R).Adj (Sum.inr u) (Sum.inr v) ↔
      (firstSplitterInterfaceGraph R).Adj u v := by
  simp [firstSplitterGraph]

@[simp] theorem firstSplitterGraph_adj_A_B (n : ℕ) (R : A → B → Prop) (a : A) (b : B) :
    (firstSplitterGraph n R).Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b)) ↔ R a b := by
  simp [firstSplitterGraph]

@[simp] theorem firstSplitterGraph_not_adj_A_A (n : ℕ) (R : A → B → Prop) (a a' : A) :
    ¬ (firstSplitterGraph n R).Adj (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl a')) := by
  simp [firstSplitterGraph]

@[simp] theorem firstSplitterGraph_not_adj_B_B (n : ℕ) (R : A → B → Prop) (b b' : B) :
    ¬ (firstSplitterGraph n R).Adj (Sum.inr (Sum.inr b)) (Sum.inr (Sum.inr b')) := by
  simp [firstSplitterGraph]

/-- The interface is an induced subgraph of the first-splitter graph. -/
noncomputable def firstSplitterInterfaceEmbedding (n : ℕ) (R : A → B → Prop) :
    firstSplitterInterfaceGraph R ↪g firstSplitterGraph n R where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := by
    intro u v
    simp [firstSplitterGraph]

theorem firstSplitter_interface_isIndContained (n : ℕ) (R : A → B → Prop) :
    SimpleGraph.IsIndContained (firstSplitterInterfaceGraph R) (firstSplitterGraph n R) :=
  ⟨firstSplitterInterfaceEmbedding n R⟩

/--
Checked `only if` direction of `thm:first-splitter`: if the first-splitter graph
is `P_{n+2}`-free, then its interface is `P_{n+2}`-free.
-/
theorem firstSplitter_interface_pathFree_of_graph_pathFree
    (n : ℕ) (R : A → B → Prop)
    (hG : InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterGraph n R)) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterInterfaceGraph R) := by
  intro hcopy
  exact hG (SimpleGraph.IsIndContained.trans hcopy (firstSplitter_interface_isIndContained n R))

/--
Equivalently, an induced path in the interface gives an induced path in the
first-splitter graph.
-/
theorem firstSplitter_graph_contains_path_of_interface_contains_path
    (n : ℕ) (R : A → B → Prop)
    (hcopy : SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
      (firstSplitterInterfaceGraph R)) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2)) (firstSplitterGraph n R) :=
  SimpleGraph.IsIndContained.trans hcopy (firstSplitter_interface_isIndContained n R)

/-- The terminal path vertex `s=q_{k-2}` in local indexing. -/
def firstSplitter_s (n : ℕ) : Fin (n + 1) := ⟨n - 1, by omega⟩

/-- The terminal path vertex `t=q_{k-1}` in local indexing. -/
def firstSplitter_t (n : ℕ) : Fin (n + 1) := ⟨n, by omega⟩

/-- The left splitter anchor `p=q_{k-4}` in local indexing. -/
def firstSplitter_p (n : ℕ) : Fin (n + 1) := ⟨n - 3, by omega⟩

/-- The path vertex immediately to the left of `p`. -/
def firstSplitter_pPrev (n : ℕ) : Fin (n + 1) := ⟨n - 4, by omega⟩

/-- The intermediate path vertex `r=q_{k-3}` in local indexing. -/
def firstSplitter_r (n : ℕ) : Fin (n + 1) := ⟨n - 2, by omega⟩

@[simp] theorem firstSplitterS_mem_s {n : ℕ} (_hn : 1 ≤ n) :
    firstSplitter_s n ∈ firstSplitterS n := by
  simp [firstSplitter_s, firstSplitterS, terminalBlowupProfile]

@[simp] theorem firstSplitterS_mem_t {n : ℕ} (_hn : 1 ≤ n) :
    firstSplitter_t n ∈ firstSplitterS n := by
  simp [firstSplitter_t, firstSplitterS, terminalBlowupProfile]

@[simp] theorem firstSplitterT_mem_s {n : ℕ} (_hn : 3 ≤ n) :
    firstSplitter_s n ∈ firstSplitterT n := by
  simp [firstSplitter_s, firstSplitterT]

@[simp] theorem firstSplitterT_mem_t {n : ℕ} (_hn : 3 ≤ n) :
    firstSplitter_t n ∈ firstSplitterT n := by
  simp [firstSplitter_t, firstSplitterT]

@[simp] theorem firstSplitterT_mem_p {n : ℕ} (_hn : 3 ≤ n) :
    firstSplitter_p n ∈ firstSplitterT n := by
  simp [firstSplitter_p, firstSplitterT]

@[simp] theorem firstSplitterS_not_mem_p {n : ℕ} (hn : 4 ≤ n) :
    firstSplitter_p n ∉ firstSplitterS n := by
  simp [firstSplitter_p, firstSplitterS, terminalBlowupProfile]
  omega

@[simp] theorem firstSplitterS_not_mem_r {n : ℕ} (hn : 4 ≤ n) :
    firstSplitter_r n ∉ firstSplitterS n := by
  simp [firstSplitter_r, firstSplitterS, terminalBlowupProfile]
  omega

@[simp] theorem firstSplitterT_not_mem_r {n : ℕ} (hn : 4 ≤ n) :
    firstSplitter_r n ∉ firstSplitterT n := by
  simp [firstSplitter_r, firstSplitterT]
  omega

theorem firstSplitterS_eq_s_or_t {n : ℕ} {q : Fin (n + 1)}
    (hq : q ∈ firstSplitterS n) :
    q = firstSplitter_s n ∨ q = firstSplitter_t n := by
  simpa [firstSplitterS, terminalBlowupProfile, firstSplitter_s, firstSplitter_t] using hq

theorem firstSplitterT_eq_p_or_s_or_t {n : ℕ} {q : Fin (n + 1)}
    (hq : q ∈ firstSplitterT n) :
    q = firstSplitter_p n ∨ q = firstSplitter_s n ∨ q = firstSplitter_t n := by
  simpa [firstSplitterT, firstSplitter_p, firstSplitter_s, firstSplitter_t] using hq

theorem firstSplitter_outside_adj_s {n : ℕ} (hn : 3 ≤ n)
    (R : A → B → Prop) (u : Sum A B) :
    (firstSplitterGraph n R).Adj (Sum.inr u) (Sum.inl (firstSplitter_s n)) := by
  cases u with
  | inl a =>
      simpa [firstSplitterGraph, firstSplitterProfile] using
        (firstSplitterS_mem_s (n := n) (by omega))
  | inr b =>
      simp [firstSplitterGraph, firstSplitterProfile, firstSplitterT_mem_s hn]

theorem firstSplitter_outside_adj_t {n : ℕ} (hn : 3 ≤ n)
    (R : A → B → Prop) (u : Sum A B) :
    (firstSplitterGraph n R).Adj (Sum.inr u) (Sum.inl (firstSplitter_t n)) := by
  cases u with
  | inl a =>
      simpa [firstSplitterGraph, firstSplitterProfile] using
        (firstSplitterS_mem_t (n := n) (by omega))
  | inr b =>
      simp [firstSplitterGraph, firstSplitterProfile, firstSplitterT_mem_t hn]

theorem firstSplitter_B_adj_p {n : ℕ} (hn : 3 ≤ n)
    (R : A → B → Prop) (b : B) :
    (firstSplitterGraph n R).Adj
      (Sum.inr (Sum.inr b) : Sum (Fin (n + 1)) (Sum A B))
      (Sum.inl (firstSplitter_p n)) := by
  simp [firstSplitterGraph, firstSplitterProfile, firstSplitterT_mem_p hn]

theorem firstSplitter_A_not_adj_p {n : ℕ} (hn : 4 ≤ n)
    (R : A → B → Prop) (a : A) :
    ¬ (firstSplitterGraph n R).Adj
      (Sum.inr (Sum.inl a) : Sum (Fin (n + 1)) (Sum A B))
      (Sum.inl (firstSplitter_p n)) := by
  simp [firstSplitterGraph, firstSplitterProfile, firstSplitterS_not_mem_p hn]

theorem firstSplitter_outside_not_adj_r {n : ℕ} (hn : 4 ≤ n)
    (R : A → B → Prop) (u : Sum A B) :
    ¬ (firstSplitterGraph n R).Adj (Sum.inr u) (Sum.inl (firstSplitter_r n)) := by
  cases u with
  | inl a =>
      simp [firstSplitterGraph, firstSplitterProfile, firstSplitterS_not_mem_r hn]
  | inr b =>
      simp [firstSplitterGraph, firstSplitterProfile, firstSplitterT_not_mem_r hn]

theorem firstSplitter_s_adj_t {n : ℕ} (hn : 1 ≤ n) (R : A → B → Prop) :
    (firstSplitterGraph n R).Adj
      (Sum.inl (firstSplitter_s n) : Sum (Fin (n + 1)) (Sum A B))
      (Sum.inl (firstSplitter_t n)) := by
  rw [firstSplitterGraph, profileBlowup_adj_left_left, SimpleGraph.pathGraph_adj]
  left
  simp [firstSplitter_s, firstSplitter_t]
  omega

/-- A path graph has no triangle. -/
theorem pathGraph_no_triangle {N : ℕ} {i j k : Fin N}
    (hij : (SimpleGraph.pathGraph N).Adj i j)
    (hik : (SimpleGraph.pathGraph N).Adj i k)
    (hjk : (SimpleGraph.pathGraph N).Adj j k) : False := by
  rw [SimpleGraph.pathGraph_adj] at hij hik hjk
  omega

/--
Chord exclusion used in the first-splitter converse: an induced path in the
first-splitter graph cannot contain an outside vertex together with both terminal
path vertices `s` and `t`, since these three vertices form a triangle.
-/
theorem firstSplitter_inducedPath_no_outside_with_s_and_t
    {n : ℕ} (hn : 3 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io is it : Fin (n + 2)} {u : Sum A B}
    (ho : φ io = Sum.inr u)
    (hs : φ is = Sum.inl (firstSplitter_s n))
    (ht : φ it = Sum.inl (firstSplitter_t n)) : False := by
  have hosG : (firstSplitterGraph n R).Adj (φ io) (φ is) := by
    rw [ho, hs]
    exact firstSplitter_outside_adj_s hn R u
  have hotG : (firstSplitterGraph n R).Adj (φ io) (φ it) := by
    rw [ho, ht]
    exact firstSplitter_outside_adj_t hn R u
  have hstG : (firstSplitterGraph n R).Adj (φ is) (φ it) := by
    rw [hs, ht]
    exact firstSplitter_s_adj_t (by omega) R
  exact pathGraph_no_triangle
    ((φ.map_rel_iff.mp hosG))
    ((φ.map_rel_iff.mp hotG))
    ((φ.map_rel_iff.mp hstG))

/-- In an induced path, the preimage of the neighborhood of one selected vertex
has size at most two. -/
theorem inducedPath_neighbor_index_card_le_two {N : ℕ} {V : Type*} {G : SimpleGraph V}
    (φ : SimpleGraph.pathGraph N ↪g G) (y : Fin N) (X : Finset (Fin N))
    (hX : ∀ x ∈ X, G.Adj (φ y) (φ x)) :
    X.card ≤ 2 := by
  exact pathGraph_neighbor_finset_card_le_two y X (by
    intro x hx
    exact (φ.map_rel_iff.mp (hX x hx)))

/--
If a finite set injects into `Fin N` but misses at least one value, then its
size is at most `N - 1`.
-/
theorem card_le_pred_of_injOn_fin_missing {α : Type*} (S : Finset α) {N : ℕ}
    (f : α → Fin N) (hinj : Set.InjOn f (S : Set α))
    (hmiss : ∃ y : Fin N, y ∉ S.image f) :
    S.card ≤ N - 1 := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  rcases hmiss with ⟨y, hy⟩
  have hproper : S.image f ⊂ (Finset.univ : Finset (Fin N)) := by
    rw [Finset.ssubset_univ_iff]
    intro hEq
    exact hy (by rw [hEq]; simp)
  have hlt : (S.image f).card < N := by
    simpa [Fintype.card_fin] using Finset.card_lt_card hproper
  exact Nat.le_pred_of_lt hlt

theorem inducedPath_three_part_card_contradiction
    {N : ℕ} {V : Type*} {G : SimpleGraph V}
    (φ : SimpleGraph.pathGraph N ↪g G)
    (O L : Finset (Fin N)) (v : V)
    (hsmall : O.card + L.card + 1 < N)
    (hclass : ∀ i : Fin N, i ∉ O → i ∉ L → φ i = v) : False := by
  classical
  let Code : Type := Sum {i // i ∈ O} (Sum {i // i ∈ L} PUnit)
  let code : Fin N → Code := fun i =>
    if hiO : i ∈ O then
      Sum.inl ⟨i, hiO⟩
    else if hiL : i ∈ L then
      Sum.inr (Sum.inl ⟨i, hiL⟩)
    else
      Sum.inr (Sum.inr PUnit.unit)
  have hcode_inj : Function.Injective code := by
    intro i j hij
    by_cases hiO : i ∈ O
    · by_cases hjO : j ∈ O
      · simp [code, hiO, hjO] at hij
        injection hij with hsub
        exact congrArg Subtype.val hsub
      · by_cases hjL : j ∈ L
        · simp [code, hiO, hjO, hjL] at hij
        · simp [code, hiO, hjO, hjL] at hij
    · by_cases hiL : i ∈ L
      · by_cases hjO : j ∈ O
        · simp [code, hiO, hiL, hjO] at hij
        · by_cases hjL : j ∈ L
          · simp [code, hiO, hiL, hjO, hjL] at hij
            injection hij with hsub
            injection hsub with hsub'
            exact congrArg Subtype.val hsub'
          · simp [code, hiO, hiL, hjO, hjL] at hij
            cases hij
      · by_cases hjO : j ∈ O
        · simp [code, hiO, hiL, hjO] at hij
        · by_cases hjL : j ∈ L
          · simp [code, hiO, hiL, hjO, hjL] at hij
            cases hij
          · apply (RelEmbedding.inj φ).mp
            rw [hclass i hiO hiL, hclass j hjO hjL]
  have hcard_le := Fintype.card_le_of_injective code hcode_inj
  have hCodeCard : Fintype.card Code = O.card + (L.card + 1) := by
    simp [Code, Fintype.card_coe]
  have hdomain_le : N ≤ O.card + L.card + 1 := by
    simpa [Fintype.card_fin, hCodeCard, Nat.add_assoc] using hcard_le
  omega

theorem inducedPath_two_part_card_contradiction
    {N : ℕ} {V : Type*} {G : SimpleGraph V}
    (φ : SimpleGraph.pathGraph N ↪g G)
    (O L : Finset (Fin N))
    (hsmall : O.card + L.card < N)
    (hclass : ∀ i : Fin N, i ∈ O ∨ i ∈ L) : False := by
  classical
  let Code : Type := Sum {i // i ∈ O} {i // i ∈ L}
  let code : Fin N → Code := fun i =>
    if hiO : i ∈ O then
      Sum.inl ⟨i, hiO⟩
    else
      Sum.inr ⟨i, by
        rcases hclass i with hi | hi
        · exact False.elim (hiO hi)
        · exact hi⟩
  have hcode_inj : Function.Injective code := by
    intro i j hij
    by_cases hiO : i ∈ O
    · by_cases hjO : j ∈ O
      · simp [code, hiO, hjO] at hij
        injection hij with hsub
        exact congrArg Subtype.val hsub
      · simp [code, hiO, hjO] at hij
    · by_cases hjO : j ∈ O
      · simp [code, hiO, hjO] at hij
      · simp [code, hiO, hjO] at hij
        injection hij with hsub
        exact congrArg Subtype.val hsub
  have hcard_le := Fintype.card_le_of_injective code hcode_inj
  have hCodeCard : Fintype.card Code = O.card + L.card := by
    simp [Code, Fintype.card_coe]
  have hdomain_le : N ≤ O.card + L.card := by
    simpa [Fintype.card_fin, hCodeCard] using hcard_le
  omega

/-- Source indices whose images lie outside the base path. -/
noncomputable def firstSplitterOutsideIndices {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter fun i => ∃ u : Sum A B, φ i = Sum.inr u

/-- Source indices whose images lie in the left base-path segment through `r`. -/
noncomputable def firstSplitterLeftThroughRIndices {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter fun i =>
    ∃ q : Fin (n + 1), φ i = Sum.inl q ∧ q.val ≤ n - 2

/-- Source indices whose images lie in the left base-path segment through `p`. -/
noncomputable def firstSplitterLeftThroughPIndices {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter fun i =>
    ∃ q : Fin (n + 1), φ i = Sum.inl q ∧ q.val ≤ n - 3

/-- Source indices whose images lie on the `A` side of the interface. -/
noncomputable def firstSplitterAIndices {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter fun i => ∃ a : A, φ i = Sum.inr (Sum.inl a)

/-- Source indices whose images lie on the `B` side of the interface. -/
noncomputable def firstSplitterBIndices {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    Finset (Fin (n + 2)) := by
  classical
  exact Finset.univ.filter fun i => ∃ b : B, φ i = Sum.inr (Sum.inr b)

theorem firstSplitterOutsideIndices.mem_iff {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {i : Fin (n + 2)} :
    i ∈ firstSplitterOutsideIndices R φ ↔ ∃ u : Sum A B, φ i = Sum.inr u := by
  classical
  simp [firstSplitterOutsideIndices]

theorem firstSplitterLeftThroughRIndices.mem_iff {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {i : Fin (n + 2)} :
    i ∈ firstSplitterLeftThroughRIndices R φ ↔
      ∃ q : Fin (n + 1), φ i = Sum.inl q ∧ q.val ≤ n - 2 := by
  classical
  simp [firstSplitterLeftThroughRIndices]

theorem firstSplitterLeftThroughPIndices.mem_iff {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {i : Fin (n + 2)} :
    i ∈ firstSplitterLeftThroughPIndices R φ ↔
      ∃ q : Fin (n + 1), φ i = Sum.inl q ∧ q.val ≤ n - 3 := by
  classical
  simp [firstSplitterLeftThroughPIndices]

theorem firstSplitterAIndices.mem_iff {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {i : Fin (n + 2)} :
    i ∈ firstSplitterAIndices R φ ↔ ∃ a : A, φ i = Sum.inr (Sum.inl a) := by
  classical
  simp [firstSplitterAIndices]

theorem firstSplitterBIndices.mem_iff {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {i : Fin (n + 2)} :
    i ∈ firstSplitterBIndices R φ ↔ ∃ b : B, φ i = Sum.inr (Sum.inr b) := by
  classical
  simp [firstSplitterBIndices]

theorem firstSplitterOutside_card_eq_A_add_B
    {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    (firstSplitterOutsideIndices R φ).card =
      (firstSplitterAIndices R φ).card + (firstSplitterBIndices R φ).card := by
  classical
  let O := firstSplitterOutsideIndices R φ
  let IA := firstSplitterAIndices R φ
  let IB := firstSplitterBIndices R φ
  have hpart : O = IA ∪ IB := by
    ext i
    constructor
    · intro hi
      rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hi with ⟨u, hu⟩
      cases u with
      | inl a =>
          exact Finset.mem_union.mpr
            (Or.inl ((firstSplitterAIndices.mem_iff R φ).mpr ⟨a, hu⟩))
      | inr b =>
          exact Finset.mem_union.mpr
            (Or.inr ((firstSplitterBIndices.mem_iff R φ).mpr ⟨b, hu⟩))
    · intro hi
      rcases Finset.mem_union.mp hi with hiA | hiB
      · rcases (firstSplitterAIndices.mem_iff R φ).mp hiA with ⟨a, ha⟩
        exact (firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨Sum.inl a, ha⟩
      · rcases (firstSplitterBIndices.mem_iff R φ).mp hiB with ⟨b, hb⟩
        exact (firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨Sum.inr b, hb⟩
  have hdisj : Disjoint IA IB := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    rcases (firstSplitterAIndices.mem_iff R φ).mp hiA with ⟨a, ha⟩
    rcases (firstSplitterBIndices.mem_iff R φ).mp hiB with ⟨b, hb⟩
    rw [ha] at hb
    cases hb
  change O.card = IA.card + IB.card
  rw [hpart, Finset.card_union_of_disjoint hdisj]

theorem firstSplitter_BIndices_card_le_two_of_p
    {n : ℕ} (hn : 3 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {ip : Fin (n + 2)} (hp : φ ip = Sum.inl (firstSplitter_p n)) :
    (firstSplitterBIndices R φ).card ≤ 2 := by
  classical
  refine inducedPath_neighbor_index_card_le_two φ ip
    (firstSplitterBIndices R φ) ?_
  intro x hx
  rcases (firstSplitterBIndices.mem_iff R φ).mp hx with ⟨b, hb⟩
  rw [hp, hb]
  exact (firstSplitter_B_adj_p hn R b).symm

theorem firstSplitter_BIndices_card_le_one_of_p_and_r
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {ip ir : Fin (n + 2)}
    (hp : φ ip = Sum.inl (firstSplitter_p n))
    (hr : φ ir = Sum.inl (firstSplitter_r n)) :
    (firstSplitterBIndices R φ).card ≤ 1 := by
  classical
  let IB := firstSplitterBIndices R φ
  have hir_not_IB : ir ∉ IB := by
    intro hir
    rcases (firstSplitterBIndices.mem_iff R φ).mp hir with ⟨b, hb⟩
    rw [hr] at hb
    cases hb
  let X : Finset (Fin (n + 2)) := insert ir IB
  have hXle := inducedPath_neighbor_index_card_le_two φ ip X (by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxIB
    · rw [hp, hr, firstSplitterGraph, profileBlowup_adj_left_left,
        SimpleGraph.pathGraph_adj]
      left
      simp [firstSplitter_p, firstSplitter_r]
      omega
    · rcases (firstSplitterBIndices.mem_iff R φ).mp hxIB with ⟨b, hb⟩
      rw [hp, hb]
      exact (firstSplitter_B_adj_p (by omega) R b).symm)
  have hcardX : X.card = IB.card + 1 := by
    simp [X, hir_not_IB]
  change IB.card ≤ 1
  omega

theorem firstSplitter_A_index_has_B_neighbor_without_s_t
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n))
    (htnone : ¬ ∃ it : Fin (n + 2), φ it = Sum.inl (firstSplitter_t n))
    {ia : Fin (n + 2)} (hia : ia ∈ firstSplitterAIndices R φ) :
    ∃ ib : Fin (n + 2),
      ib ∈ firstSplitterBIndices R φ ∧
        (SimpleGraph.pathGraph (n + 2)).Adj ia ib := by
  classical
  rcases (firstSplitterAIndices.mem_iff R φ).mp hia with ⟨a, ha⟩
  rcases pathGraph_exists_neighbor (N := n + 2) (by omega) ia with ⟨j, hij⟩
  have hG : (firstSplitterGraph n R).Adj (φ ia) (φ j) :=
    φ.map_rel_iff.mpr hij
  cases hφj : φ j with
  | inl q =>
      have hqS : q ∈ firstSplitterS n := by
        have hG' := hG
        rw [ha, hφj] at hG'
        simpa [firstSplitterGraph, firstSplitterProfile] using hG'
      rcases firstSplitterS_eq_s_or_t hqS with hq | hq
      · exact False.elim (hsnone ⟨j, by rw [hφj, hq]⟩)
      · exact False.elim (htnone ⟨j, by rw [hφj, hq]⟩)
  | inr u =>
      cases u with
      | inl a' =>
          have hAA := firstSplitterGraph_not_adj_A_A n R a a'
          have hG' := hG
          rw [ha, hφj] at hG'
          exact False.elim (hAA hG')
      | inr b =>
          exact ⟨j, (firstSplitterBIndices.mem_iff R φ).mpr ⟨b, hφj⟩, hij⟩

theorem firstSplitter_AIndices_card_le_BIndices_without_s_t_of_p
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n))
    (htnone : ¬ ∃ it : Fin (n + 2), φ it = Sum.inl (firstSplitter_t n))
    {ip : Fin (n + 2)} (hp : φ ip = Sum.inl (firstSplitter_p n)) :
    (firstSplitterAIndices R φ).card ≤ (firstSplitterBIndices R φ).card := by
  classical
  let IA := firstSplitterAIndices R φ
  let IB := firstSplitterBIndices R φ
  have hneighbor : ∀ i : {i // i ∈ IA},
      ∃ j : {j // j ∈ IB}, (SimpleGraph.pathGraph (n + 2)).Adj i.1 j.1 := by
    intro i
    rcases firstSplitter_A_index_has_B_neighbor_without_s_t hn R φ hsnone htnone
        (ia := i.1) i.2 with ⟨j, hjIB, hij⟩
    exact ⟨⟨j, hjIB⟩, hij⟩
  let f : {i // i ∈ IA} → {j // j ∈ IB} := fun i => Classical.choose (hneighbor i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hiAdj : (SimpleGraph.pathGraph (n + 2)).Adj i.1 (f i).1 :=
      Classical.choose_spec (hneighbor i)
    have hjAdj : (SimpleGraph.pathGraph (n + 2)).Adj j.1 (f j).1 :=
      Classical.choose_spec (hneighbor j)
    rcases (firstSplitterBIndices.mem_iff R φ).mp (f i).2 with ⟨b, hb⟩
    rcases (firstSplitterAIndices.mem_iff R φ).mp i.2 with ⟨a, ha⟩
    rcases (firstSplitterAIndices.mem_iff R φ).mp j.2 with ⟨a', ha'⟩
    have hip_ne_i : ip ≠ i.1 := by
      intro h
      have hv := congrArg φ h
      rw [hp, ha] at hv
      cases hv
    have hip_ne_j : ip ≠ j.1 := by
      intro h
      have hv := congrArg φ h
      rw [hp, ha'] at hv
      cases hv
    have hi_ne_j : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h)
    let X : Finset (Fin (n + 2)) := {ip, i.1, j.1}
    have hXcard : X.card = 3 := by
      simp [X, hip_ne_i, hip_ne_j, hi_ne_j, hip_ne_i.symm,
        hip_ne_j.symm, hi_ne_j.symm]
    have hXle := inducedPath_neighbor_index_card_le_two φ (f i).1 X (by
      intro x hx
      simp [X] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hb, hp]
        exact firstSplitter_B_adj_p (by omega) R b
      · exact (φ.map_rel_iff.mpr hiAdj).symm
      · have hjG : (firstSplitterGraph n R).Adj (φ (f i).1) (φ j.1) := by
          simpa [hij] using (φ.map_rel_iff.mpr hjAdj).symm
        exact hjG)
    omega
  have hle := Fintype.card_le_of_injective f hf
  change IA.card ≤ IB.card
  simpa [Fintype.card_coe] using hle

theorem firstSplitter_outsideIndices_card_le_two_of_t
    {n : ℕ} (hn : 3 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {it : Fin (n + 2)} (ht : φ it = Sum.inl (firstSplitter_t n)) :
    (firstSplitterOutsideIndices R φ).card ≤ 2 := by
  classical
  refine inducedPath_neighbor_index_card_le_two φ it
    (firstSplitterOutsideIndices R φ) ?_
  intro x hx
  rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hx with ⟨u, hu⟩
  rw [ht, hu]
  exact (firstSplitter_outside_adj_t hn R u).symm

theorem firstSplitter_outsideIndices_card_le_two_of_s
    {n : ℕ} (hn : 3 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {is : Fin (n + 2)} (hs : φ is = Sum.inl (firstSplitter_s n)) :
    (firstSplitterOutsideIndices R φ).card ≤ 2 := by
  classical
  refine inducedPath_neighbor_index_card_le_two φ is
    (firstSplitterOutsideIndices R φ) ?_
  intro x hx
  rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hx with ⟨u, hu⟩
  rw [hs, hu]
  exact (firstSplitter_outside_adj_s hn R u).symm

theorem firstSplitter_outsideIndices_card_le_one_of_s_and_r
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {is ir : Fin (n + 2)}
    (hs : φ is = Sum.inl (firstSplitter_s n))
    (hr : φ ir = Sum.inl (firstSplitter_r n)) :
    (firstSplitterOutsideIndices R φ).card ≤ 1 := by
  classical
  let O := firstSplitterOutsideIndices R φ
  have hir_not_O : ir ∉ O := by
    intro hirO
    rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hirO with ⟨u, hu⟩
    rw [hr] at hu
    cases hu
  let X : Finset (Fin (n + 2)) := insert ir O
  have hXle := inducedPath_neighbor_index_card_le_two φ is X (by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxO
    · rw [hs, hr, firstSplitterGraph, profileBlowup_adj_left_left,
        SimpleGraph.pathGraph_adj]
      right
      simp [firstSplitter_r, firstSplitter_s]
      omega
    · rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hxO with ⟨u, hu⟩
      rw [hs, hu]
      exact (firstSplitter_outside_adj_s (by omega) R u).symm)
  have hcardX : X.card = O.card + 1 := by
    simp [X, hir_not_O]
  change O.card ≤ 1
  omega

theorem firstSplitter_no_s_index_of_t_and_outside
    {n : ℕ} (hn : 3 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io it : Fin (n + 2)} {u : Sum A B}
    (ho : φ io = Sum.inr u) (ht : φ it = Sum.inl (firstSplitter_t n)) :
    ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n) := by
  rintro ⟨is, hs⟩
  exact firstSplitter_inducedPath_no_outside_with_s_and_t hn R φ ho hs ht

theorem firstSplitter_left_boundary_forces_p_B
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n))
    (hLne : (firstSplitterLeftThroughRIndices R φ).Nonempty)
    {it : Fin (n + 2)} (ht : φ it = Sum.inl (firstSplitter_t n)) :
    ∃ ip ib : Fin (n + 2), ∃ b : B,
      ip ∈ firstSplitterLeftThroughRIndices R φ ∧
        φ ip = Sum.inl (firstSplitter_p n) ∧
          φ ib = Sum.inr (Sum.inr b) ∧
            (SimpleGraph.pathGraph (n + 2)).Adj ip ib := by
  classical
  have hit_not_L : it ∉ firstSplitterLeftThroughRIndices R φ := by
    intro hit
    rcases (firstSplitterLeftThroughRIndices.mem_iff R φ).mp hit with ⟨q, hq, hqle⟩
    have htq : q = firstSplitter_t n := by
      have htq' : firstSplitter_t n = q := by
        simpa [ht] using hq
      exact htq'.symm
    subst q
    simp [firstSplitter_t] at hqle
    omega
  rcases exists_boundary_adj_of_preconnected
      (SimpleGraph.pathGraph_preconnected (n + 2))
      ((firstSplitterLeftThroughRIndices R φ : Finset (Fin (n + 2))) : Set (Fin (n + 2)))
      (by simpa using hLne) ⟨it, hit_not_L⟩ with
    ⟨x, hxL, y, hyL, hxy⟩
  rcases (firstSplitterLeftThroughRIndices.mem_iff R φ).mp hxL with
    ⟨q, hxq, hqle⟩
  have hxyG : (firstSplitterGraph n R).Adj (φ x) (φ y) :=
    (φ.map_rel_iff.mpr hxy)
  cases hy : φ y with
  | inl qy =>
      have hqynot : ¬ qy.val ≤ n - 2 := by
        intro hqy
        exact hyL ((firstSplitterLeftThroughRIndices.mem_iff R φ).mpr ⟨qy, hy, hqy⟩)
      have hqqy : (SimpleGraph.pathGraph (n + 1)).Adj q qy := by
        have hxyG' := hxyG
        rw [hxq, hy] at hxyG'
        simpa [firstSplitterGraph] using hxyG'
      rw [SimpleGraph.pathGraph_adj] at hqqy
      have hqy_s : qy = firstSplitter_s n := by
        apply Fin.ext
        simp [firstSplitter_s]
        rcases hqqy with hright | hleft <;> omega
      exact False.elim (hsnone ⟨y, by rw [hy, hqy_s]⟩)
  | inr u =>
      cases u with
      | inl a =>
          have hqS : q ∈ firstSplitterS n := by
            have hxyG' := hxyG
            rw [hxq, hy] at hxyG'
            simpa [firstSplitterGraph, firstSplitterProfile] using hxyG'
          have hqS' := hqS
          simp [firstSplitterS, terminalBlowupProfile] at hqS'
          rcases hqS' with hqeq | hqeq
          · have hv := congrArg Fin.val hqeq
            simp at hv
            omega
          · have hv := congrArg Fin.val hqeq
            simp at hv
            omega
      | inr b =>
          have hqT : q ∈ firstSplitterT n := by
            have hxyG' := hxyG
            rw [hxq, hy] at hxyG'
            simpa [firstSplitterGraph, firstSplitterProfile] using hxyG'
          have hq_p : q = firstSplitter_p n := by
            have hqT' := hqT
            simp [firstSplitterT] at hqT'
            rcases hqT' with hqeq | hqeq | hqeq
            · exact hqeq
            · have hv := congrArg Fin.val hqeq
              simp [firstSplitter_s] at hv
              omega
            · have hv := congrArg Fin.val hqeq
              simp [firstSplitter_t] at hv
              omega
          exact ⟨x, y, b, hxL, by rw [hxq, hq_p], hy, hxy⟩

theorem firstSplitter_p_with_B_excludes_both_path_neighbors
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {ip ib : Fin (n + 2)} {b : B}
    (hp : φ ip = Sum.inl (firstSplitter_p n))
    (hb : φ ib = Sum.inr (Sum.inr b)) :
    ¬ ((∃ il : Fin (n + 2), φ il = Sum.inl (firstSplitter_pPrev n)) ∧
        ∃ ir : Fin (n + 2), φ ir = Sum.inl (firstSplitter_r n)) := by
  classical
  rintro ⟨⟨il, hil⟩, ⟨ir, hir⟩⟩
  let X : Finset (Fin (n + 2)) := {ib, il, ir}
  have hib_ne_il : ib ≠ il := by
    intro h
    have hv := congrArg φ h
    rw [hb, hil] at hv
    cases hv
  have hib_ne_ir : ib ≠ ir := by
    intro h
    have hv := congrArg φ h
    rw [hb, hir] at hv
    cases hv
  have hil_ne_ir : il ≠ ir := by
    intro h
    have hv := congrArg φ h
    rw [hil, hir] at hv
    injection hv with hq
    have hval := congrArg Fin.val hq
    simp [firstSplitter_pPrev, firstSplitter_r] at hval
    omega
  have hXcard : X.card = 3 := by
    simp [X, hib_ne_il, hib_ne_ir, hil_ne_ir, hib_ne_il.symm,
      hib_ne_ir.symm, hil_ne_ir.symm]
  have hXle := inducedPath_neighbor_index_card_le_two φ ip X (by
    intro x hx
    simp [X] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hp, hb]
      exact (firstSplitter_B_adj_p (by omega) R b).symm
    · rw [hp, hil, firstSplitterGraph, profileBlowup_adj_left_left,
        SimpleGraph.pathGraph_adj]
      right
      simp [firstSplitter_pPrev, firstSplitter_p]
      omega
    · rw [hp, hir, firstSplitterGraph, profileBlowup_adj_left_left,
        SimpleGraph.pathGraph_adj]
      left
      simp [firstSplitter_p, firstSplitter_r]
      omega)
  omega

theorem firstSplitter_leftThroughR_card_le_of_t_and_outside
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io it : Fin (n + 2)} {u : Sum A B}
    (ho : φ io = Sum.inr u) (ht : φ it = Sum.inl (firstSplitter_t n)) :
    (firstSplitterLeftThroughRIndices R φ).card ≤ n - 2 := by
  classical
  let L := firstSplitterLeftThroughRIndices R φ
  have hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n) :=
    firstSplitter_no_s_index_of_t_and_outside (by omega) R φ ho ht
  by_cases hLne : L.Nonempty
  · rcases firstSplitter_left_boundary_forces_p_B hn R φ hsnone hLne ht with
      ⟨ip, ib, b, _hipL, hp, hb, _hipib⟩
    have hnotboth :=
      firstSplitter_p_with_B_excludes_both_path_neighbors hn R φ hp hb
    let qOf : {i // i ∈ L} → Fin (n + 1) := fun i =>
      Classical.choose ((firstSplitterLeftThroughRIndices.mem_iff R φ).mp i.2)
    have qOf_spec : ∀ i : {i // i ∈ L},
        φ i.1 = Sum.inl (qOf i) ∧ (qOf i).val ≤ n - 2 := by
      intro i
      exact Classical.choose_spec ((firstSplitterLeftThroughRIndices.mem_iff R φ).mp i.2)
    let f : {i // i ∈ L} → Fin (n - 1) := fun i =>
      ⟨(qOf i).val, by
        have hle := (qOf_spec i).2
        omega⟩
    have hf_inj : Set.InjOn f ((Finset.univ : Finset {i // i ∈ L}) : Set {i // i ∈ L}) := by
      intro i _hi j _hj hij
      apply Subtype.ext
      apply (RelEmbedding.inj φ).mp
      have hval : (qOf i).val = (qOf j).val := by
        simpa [f] using congrArg Fin.val hij
      have hqeq : qOf i = qOf j := Fin.ext hval
      rw [(qOf_spec i).1, (qOf_spec j).1, hqeq]
    have hmiss :
        ∃ y : Fin (n - 1), y ∉ (Finset.univ : Finset {i // i ∈ L}).image f := by
      by_cases hprev : ∃ il : Fin (n + 2), φ il = Sum.inl (firstSplitter_pPrev n)
      · have hrnone : ¬ ∃ ir : Fin (n + 2), φ ir = Sum.inl (firstSplitter_r n) := by
          intro hr
          exact hnotboth ⟨hprev, hr⟩
        refine ⟨⟨n - 2, by omega⟩, ?_⟩
        intro hy
        rcases Finset.mem_image.mp hy with ⟨i, _hi, hfi⟩
        have hval : (qOf i).val = n - 2 := by
          simpa [f] using congrArg Fin.val hfi
        have hq_r : qOf i = firstSplitter_r n := by
          apply Fin.ext
          simp [firstSplitter_r]
          omega
        exact hrnone ⟨i.1, by rw [(qOf_spec i).1, hq_r]⟩
      · refine ⟨⟨n - 4, by omega⟩, ?_⟩
        intro hy
        rcases Finset.mem_image.mp hy with ⟨i, _hi, hfi⟩
        have hval : (qOf i).val = n - 4 := by
          simpa [f] using congrArg Fin.val hfi
        have hq_prev : qOf i = firstSplitter_pPrev n := by
          apply Fin.ext
          simp [firstSplitter_pPrev]
          omega
        exact hprev ⟨i.1, by rw [(qOf_spec i).1, hq_prev]⟩
    have hcard :=
      card_le_pred_of_injOn_fin_missing (Finset.univ : Finset {i // i ∈ L}) f hf_inj hmiss
    have hcard' : L.card ≤ (n - 1) - 1 := by
      simpa [Fintype.card_coe] using hcard
    omega
  · have hLempty : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLne
    change L.card ≤ n - 2
    rw [hLempty]
    simp

theorem firstSplitter_mixed_with_t_contradiction
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io it : Fin (n + 2)} {u : Sum A B}
    (ho : φ io = Sum.inr u) (ht : φ it = Sum.inl (firstSplitter_t n)) : False := by
  classical
  let O := firstSplitterOutsideIndices R φ
  let L := firstSplitterLeftThroughRIndices R φ
  have hOcard : O.card ≤ 2 := by
    change (firstSplitterOutsideIndices R φ).card ≤ 2
    exact firstSplitter_outsideIndices_card_le_two_of_t (by omega) R φ ht
  have hLcard : L.card ≤ n - 2 := by
    change (firstSplitterLeftThroughRIndices R φ).card ≤ n - 2
    exact firstSplitter_leftThroughR_card_le_of_t_and_outside hn R φ ho ht
  have hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n) :=
    firstSplitter_no_s_index_of_t_and_outside (by omega) R φ ho ht
  have image_t_of_not_mem (i : Fin (n + 2)) (hiO : i ∉ O) (hiL : i ∉ L) :
      φ i = Sum.inl (firstSplitter_t n) := by
    cases hφ : φ i with
    | inr u' =>
        exact False.elim (hiO ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u', hφ⟩))
    | inl q =>
        have hq_not_le : ¬ q.val ≤ n - 2 := by
          intro hqle
          exact hiL ((firstSplitterLeftThroughRIndices.mem_iff R φ).mpr ⟨q, hφ, hqle⟩)
        have hq_ne_s : q ≠ firstSplitter_s n := by
          intro hqs
          exact hsnone ⟨i, by rw [hφ, hqs]⟩
        have hqval : q.val = n := by
          have hge : n - 1 ≤ q.val := by omega
          have hle : q.val ≤ n := by omega
          by_cases hsval : q.val = n - 1
          · have hqs : q = firstSplitter_s n := by
              apply Fin.ext
              simp [firstSplitter_s]
              omega
            exact False.elim (hq_ne_s hqs)
          · omega
        have hqt : q = firstSplitter_t n := by
          apply Fin.ext
          simp [firstSplitter_t]
          exact hqval
        rw [hqt]
  let Code : Type := Sum {i // i ∈ O} (Sum {i // i ∈ L} PUnit)
  let code : Fin (n + 2) → Code := fun i =>
    if hiO : i ∈ O then
      Sum.inl ⟨i, hiO⟩
    else if hiL : i ∈ L then
      Sum.inr (Sum.inl ⟨i, hiL⟩)
    else
      Sum.inr (Sum.inr PUnit.unit)
  have hcode_inj : Function.Injective code := by
    intro i j hij
    by_cases hiO : i ∈ O
    · by_cases hjO : j ∈ O
      · simp [code, hiO, hjO] at hij
        injection hij with hsub
        exact congrArg Subtype.val hsub
      · by_cases hjL : j ∈ L
        · simp [code, hiO, hjO, hjL] at hij
        · simp [code, hiO, hjO, hjL] at hij
    · by_cases hiL : i ∈ L
      · by_cases hjO : j ∈ O
        · simp [code, hiO, hiL, hjO] at hij
        · by_cases hjL : j ∈ L
          · simp [code, hiO, hiL, hjO, hjL] at hij
            injection hij with hsub
            injection hsub with hsub'
            exact congrArg Subtype.val hsub'
          · simp [code, hiO, hiL, hjO, hjL] at hij
            cases hij
      · by_cases hjO : j ∈ O
        · simp [code, hiO, hiL, hjO] at hij
        · by_cases hjL : j ∈ L
          · simp [code, hiO, hiL, hjO, hjL] at hij
            cases hij
          · apply (RelEmbedding.inj φ).mp
            rw [image_t_of_not_mem i hiO hiL, image_t_of_not_mem j hjO hjL]
  have hcard_le := Fintype.card_le_of_injective code hcode_inj
  have hCodeCard : Fintype.card Code = O.card + (L.card + 1) := by
    simp [Code, Fintype.card_coe]
  have hdomain_le : n + 2 ≤ O.card + L.card + 1 := by
    simpa [Fintype.card_fin, hCodeCard, Nat.add_assoc] using hcard_le
  have hupper : O.card + L.card + 1 ≤ 2 + (n - 2) + 1 := by
    omega
  omega

theorem firstSplitter_leftThroughR_card_le
    {n : ℕ} (hn : 2 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    (firstSplitterLeftThroughRIndices R φ).card ≤ n - 1 := by
  classical
  let L := firstSplitterLeftThroughRIndices R φ
  let qOf : {i // i ∈ L} → Fin (n + 1) := fun i =>
    Classical.choose ((firstSplitterLeftThroughRIndices.mem_iff R φ).mp i.2)
  have qOf_spec : ∀ i : {i // i ∈ L},
      φ i.1 = Sum.inl (qOf i) ∧ (qOf i).val ≤ n - 2 := by
    intro i
    exact Classical.choose_spec ((firstSplitterLeftThroughRIndices.mem_iff R φ).mp i.2)
  let f : {i // i ∈ L} → Fin (n - 1) := fun i =>
    ⟨(qOf i).val, by
      have hle := (qOf_spec i).2
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply (RelEmbedding.inj φ).mp
    have hval : (qOf i).val = (qOf j).val := by
      simpa [f] using congrArg Fin.val hij
    have hq : qOf i = qOf j := Fin.ext hval
    rw [(qOf_spec i).1, (qOf_spec j).1, hq]
  have hle := Fintype.card_le_of_injective f hf
  change L.card ≤ n - 1
  simpa [Fintype.card_coe, Fintype.card_fin] using hle

theorem firstSplitter_leftThroughP_card_le
    {n : ℕ} (hn : 3 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R) :
    (firstSplitterLeftThroughPIndices R φ).card ≤ n - 2 := by
  classical
  let L := firstSplitterLeftThroughPIndices R φ
  let qOf : {i // i ∈ L} → Fin (n + 1) := fun i =>
    Classical.choose ((firstSplitterLeftThroughPIndices.mem_iff R φ).mp i.2)
  have qOf_spec : ∀ i : {i // i ∈ L},
      φ i.1 = Sum.inl (qOf i) ∧ (qOf i).val ≤ n - 3 := by
    intro i
    exact Classical.choose_spec ((firstSplitterLeftThroughPIndices.mem_iff R φ).mp i.2)
  let f : {i // i ∈ L} → Fin (n - 2) := fun i =>
    ⟨(qOf i).val, by
      have hle := (qOf_spec i).2
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply (RelEmbedding.inj φ).mp
    have hval : (qOf i).val = (qOf j).val := by
      simpa [f] using congrArg Fin.val hij
    have hq : qOf i = qOf j := Fin.ext hval
    rw [(qOf_spec i).1, (qOf_spec j).1, hq]
  have hle := Fintype.card_le_of_injective f hf
  change L.card ≤ n - 2
  simpa [Fintype.card_coe, Fintype.card_fin] using hle

theorem firstSplitter_leftThroughP_card_le_of_missing_pPrev
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hprevnone :
      ¬ ∃ iprev : Fin (n + 2), φ iprev = Sum.inl (firstSplitter_pPrev n)) :
    (firstSplitterLeftThroughPIndices R φ).card ≤ n - 3 := by
  classical
  let L := firstSplitterLeftThroughPIndices R φ
  let qOf : {i // i ∈ L} → Fin (n + 1) := fun i =>
    Classical.choose ((firstSplitterLeftThroughPIndices.mem_iff R φ).mp i.2)
  have qOf_spec : ∀ i : {i // i ∈ L},
      φ i.1 = Sum.inl (qOf i) ∧ (qOf i).val ≤ n - 3 := by
    intro i
    exact Classical.choose_spec ((firstSplitterLeftThroughPIndices.mem_iff R φ).mp i.2)
  let f : {i // i ∈ L} → Fin (n - 2) := fun i =>
    ⟨(qOf i).val, by
      have hle := (qOf_spec i).2
      omega⟩
  have hf_inj : Set.InjOn f ((Finset.univ : Finset {i // i ∈ L}) : Set {i // i ∈ L}) := by
    intro i _hi j _hj hij
    apply Subtype.ext
    apply (RelEmbedding.inj φ).mp
    have hval : (qOf i).val = (qOf j).val := by
      simpa [f] using congrArg Fin.val hij
    have hqeq : qOf i = qOf j := Fin.ext hval
    rw [(qOf_spec i).1, (qOf_spec j).1, hqeq]
  have hmiss :
      ∃ y : Fin (n - 2), y ∉ (Finset.univ : Finset {i // i ∈ L}).image f := by
    refine ⟨⟨n - 4, by omega⟩, ?_⟩
    intro hy
    rcases Finset.mem_image.mp hy with ⟨i, _hi, hfi⟩
    have hval : (qOf i).val = n - 4 := by
      simpa [f] using congrArg Fin.val hfi
    have hq_prev : qOf i = firstSplitter_pPrev n := by
      apply Fin.ext
      simp [firstSplitter_pPrev]
      omega
    exact hprevnone ⟨i.1, by rw [(qOf_spec i).1, hq_prev]⟩
  have hcard :=
    card_le_pred_of_injOn_fin_missing (Finset.univ : Finset {i // i ∈ L}) f hf_inj hmiss
  have hcard' : L.card ≤ (n - 2) - 1 := by
    simpa [Fintype.card_coe] using hcard
  omega

theorem firstSplitter_p_with_two_B_excludes_pPrev
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {ip : Fin (n + 2)}
    (hp : φ ip = Sum.inl (firstSplitter_p n))
    (hBcard : (firstSplitterBIndices R φ).card = 2) :
    ¬ ∃ iprev : Fin (n + 2), φ iprev = Sum.inl (firstSplitter_pPrev n) := by
  classical
  rintro ⟨iprev, hprev⟩
  let IB := firstSplitterBIndices R φ
  have hprev_not_IB : iprev ∉ IB := by
    intro hprevIB
    rcases (firstSplitterBIndices.mem_iff R φ).mp hprevIB with ⟨b, hb⟩
    rw [hprev] at hb
    cases hb
  let X : Finset (Fin (n + 2)) := insert iprev IB
  have hXle := inducedPath_neighbor_index_card_le_two φ ip X (by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxIB
    · rw [hp, hprev, firstSplitterGraph, profileBlowup_adj_left_left,
        SimpleGraph.pathGraph_adj]
      right
      simp [firstSplitter_pPrev, firstSplitter_p]
      omega
    · rcases (firstSplitterBIndices.mem_iff R φ).mp hxIB with ⟨b, hb⟩
      rw [hp, hb]
      exact (firstSplitter_B_adj_p (by omega) R b).symm)
  have hcardX : X.card = IB.card + 1 := by
    simp [X, hprev_not_IB]
  have hIBcard : IB.card = 2 := by
    simpa [IB] using hBcard
  omega

theorem firstSplitter_leftThroughP_card_le_of_p_and_two_B
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {ip : Fin (n + 2)}
    (hp : φ ip = Sum.inl (firstSplitter_p n))
    (hBcard : (firstSplitterBIndices R φ).card = 2) :
    (firstSplitterLeftThroughPIndices R φ).card ≤ n - 3 := by
  exact firstSplitter_leftThroughP_card_le_of_missing_pPrev hn R φ
    (firstSplitter_p_with_two_B_excludes_pPrev hn R φ hp hBcard)

theorem firstSplitter_mixed_with_s_no_t_contradiction
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io is : Fin (n + 2)} {u : Sum A B}
    (ho : φ io = Sum.inr u)
    (hs : φ is = Sum.inl (firstSplitter_s n))
    (htnone : ¬ ∃ it : Fin (n + 2), φ it = Sum.inl (firstSplitter_t n)) : False := by
  classical
  by_cases hrx : ∃ ir : Fin (n + 2), φ ir = Sum.inl (firstSplitter_r n)
  · rcases hrx with ⟨ir, hr⟩
    let O := firstSplitterOutsideIndices R φ
    let L := firstSplitterLeftThroughRIndices R φ
    have hOcard : O.card ≤ 1 := by
      change (firstSplitterOutsideIndices R φ).card ≤ 1
      exact firstSplitter_outsideIndices_card_le_one_of_s_and_r hn R φ hs hr
    have hLcard : L.card ≤ n - 1 := by
      change (firstSplitterLeftThroughRIndices R φ).card ≤ n - 1
      exact firstSplitter_leftThroughR_card_le (by omega) R φ
    have hsmall : O.card + L.card + 1 < n + 2 := by
      omega
    exact inducedPath_three_part_card_contradiction φ O L
      (Sum.inl (firstSplitter_s n)) hsmall (by
        intro i hiO hiL
        cases hφ : φ i with
        | inr u' =>
            exact False.elim
              (hiO ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u', hφ⟩))
        | inl q =>
            have hq_not_le : ¬ q.val ≤ n - 2 := by
              intro hqle
              exact hiL
                ((firstSplitterLeftThroughRIndices.mem_iff R φ).mpr ⟨q, hφ, hqle⟩)
            have hqval : q.val = n - 1 := by
              have hge : n - 1 ≤ q.val := by omega
              have hle : q.val ≤ n := by omega
              by_cases htval : q.val = n
              · have hqt : q = firstSplitter_t n := by
                  apply Fin.ext
                  simp [firstSplitter_t]
                  exact htval
                exact False.elim (htnone ⟨i, by rw [hφ, hqt]⟩)
              · omega
            have hqs : q = firstSplitter_s n := by
              apply Fin.ext
              simp [firstSplitter_s]
              exact hqval
            rw [hqs])
  · let O := firstSplitterOutsideIndices R φ
    let L := firstSplitterLeftThroughPIndices R φ
    have hOcard : O.card ≤ 2 := by
      change (firstSplitterOutsideIndices R φ).card ≤ 2
      exact firstSplitter_outsideIndices_card_le_two_of_s (by omega) R φ hs
    have hLcard : L.card ≤ n - 2 := by
      change (firstSplitterLeftThroughPIndices R φ).card ≤ n - 2
      exact firstSplitter_leftThroughP_card_le (by omega) R φ
    have hsmall : O.card + L.card + 1 < n + 2 := by
      omega
    exact inducedPath_three_part_card_contradiction φ O L
      (Sum.inl (firstSplitter_s n)) hsmall (by
        intro i hiO hiL
        cases hφ : φ i with
        | inr u' =>
            exact False.elim
              (hiO ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u', hφ⟩))
        | inl q =>
            have hq_not_le : ¬ q.val ≤ n - 3 := by
              intro hqle
              exact hiL
                ((firstSplitterLeftThroughPIndices.mem_iff R φ).mpr ⟨q, hφ, hqle⟩)
            have hq_ne_r : q ≠ firstSplitter_r n := by
              intro hqr
              exact hrx ⟨i, by rw [hφ, hqr]⟩
            have hqval : q.val = n - 1 := by
              have hge : n - 2 ≤ q.val := by omega
              have hle : q.val ≤ n := by omega
              by_cases hrval : q.val = n - 2
              · have hqr : q = firstSplitter_r n := by
                  apply Fin.ext
                  simp [firstSplitter_r]
                  exact hrval
                exact False.elim (hq_ne_r hqr)
              by_cases htval : q.val = n
              · have hqt : q = firstSplitter_t n := by
                  apply Fin.ext
                  simp [firstSplitter_t]
                  exact htval
                exact False.elim (htnone ⟨i, by rw [hφ, hqt]⟩)
              · omega
            have hqs : q = firstSplitter_s n := by
              apply Fin.ext
              simp [firstSplitter_s]
              exact hqval
            rw [hqs])

theorem firstSplitter_mixed_without_s_t_forces_p_B
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io iq : Fin (n + 2)} {u₀ : Sum A B} {q₀ : Fin (n + 1)}
    (ho : φ io = Sum.inr u₀) (hq : φ iq = Sum.inl q₀)
    (hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n))
    (htnone : ¬ ∃ it : Fin (n + 2), φ it = Sum.inl (firstSplitter_t n)) :
    ∃ ip ib : Fin (n + 2), ∃ b : B,
      φ ip = Sum.inl (firstSplitter_p n) ∧
        φ ib = Sum.inr (Sum.inr b) ∧
          (SimpleGraph.pathGraph (n + 2)).Adj ip ib := by
  classical
  let O := firstSplitterOutsideIndices R φ
  have hOne : O.Nonempty := by
    exact ⟨io, (firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u₀, ho⟩⟩
  have hiq_not_O : iq ∉ O := by
    intro hiqO
    rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hiqO with ⟨u, hu⟩
    rw [hq] at hu
    cases hu
  rcases exists_boundary_adj_of_preconnected
      (SimpleGraph.pathGraph_preconnected (n + 2))
      ((O : Finset (Fin (n + 2))) : Set (Fin (n + 2)))
      (by simpa using hOne) ⟨iq, hiq_not_O⟩ with
    ⟨x, hxO, y, hyO, hxy⟩
  rcases (firstSplitterOutsideIndices.mem_iff R φ).mp hxO with ⟨u, hx⟩
  have hxyG : (firstSplitterGraph n R).Adj (φ x) (φ y) :=
    φ.map_rel_iff.mpr hxy
  cases hy : φ y with
  | inr uy =>
      exact False.elim
        (hyO ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨uy, hy⟩))
  | inl q =>
      cases u with
      | inl a =>
          have hqS : q ∈ firstSplitterS n := by
            have hxyG' := hxyG
            rw [hx, hy] at hxyG'
            simpa [firstSplitterGraph, firstSplitterProfile] using hxyG'
          rcases firstSplitterS_eq_s_or_t hqS with hqs | hqt
          · exact False.elim (hsnone ⟨y, by rw [hy, hqs]⟩)
          · exact False.elim (htnone ⟨y, by rw [hy, hqt]⟩)
      | inr b =>
          have hqT : q ∈ firstSplitterT n := by
            have hxyG' := hxyG
            rw [hx, hy] at hxyG'
            simpa [firstSplitterGraph, firstSplitterProfile] using hxyG'
          rcases firstSplitterT_eq_p_or_s_or_t hqT with hqp | hqs | hqt
          · exact ⟨y, x, b, by rw [hy, hqp], hx, hxy.symm⟩
          · exact False.elim (hsnone ⟨y, by rw [hy, hqs]⟩)
          · exact False.elim (htnone ⟨y, by rw [hy, hqt]⟩)

theorem firstSplitter_mixed_without_s_t_contradiction
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    {io iq : Fin (n + 2)} {u : Sum A B} {q : Fin (n + 1)}
    (ho : φ io = Sum.inr u) (hq : φ iq = Sum.inl q)
    (hsnone : ¬ ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n))
    (htnone : ¬ ∃ it : Fin (n + 2), φ it = Sum.inl (firstSplitter_t n)) : False := by
  classical
  rcases firstSplitter_mixed_without_s_t_forces_p_B hn R φ ho hq hsnone htnone with
    ⟨ip, _ib, _b, hp, _hb, _hipib⟩
  let O := firstSplitterOutsideIndices R φ
  let IA := firstSplitterAIndices R φ
  let IB := firstSplitterBIndices R φ
  let L := firstSplitterLeftThroughPIndices R φ
  have hOeq : O.card = IA.card + IB.card := by
    simpa [O, IA, IB] using firstSplitterOutside_card_eq_A_add_B R φ
  have hAcard : IA.card ≤ IB.card := by
    simpa [IA, IB] using
      firstSplitter_AIndices_card_le_BIndices_without_s_t_of_p hn R φ hsnone htnone hp
  have hBcard_two : IB.card ≤ 2 := by
    simpa [IB] using firstSplitter_BIndices_card_le_two_of_p (by omega) R φ hp
  by_cases hrx : ∃ ir : Fin (n + 2), φ ir = Sum.inl (firstSplitter_r n)
  · rcases hrx with ⟨ir, hr⟩
    have hBcard_one : IB.card ≤ 1 := by
      simpa [IB] using firstSplitter_BIndices_card_le_one_of_p_and_r hn R φ hp hr
    have hOcard : O.card ≤ 2 := by omega
    have hLcard : L.card ≤ n - 2 := by
      simpa [L] using firstSplitter_leftThroughP_card_le (by omega) R φ
    have hsmall : O.card + L.card + 1 < n + 2 := by omega
    exact inducedPath_three_part_card_contradiction φ O L
      (Sum.inl (firstSplitter_r n)) hsmall (by
        intro i hiO hiL
        cases hφ : φ i with
        | inr u' =>
            exact False.elim
              (hiO ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u', hφ⟩))
        | inl q' =>
            have hq_not_le : ¬ q'.val ≤ n - 3 := by
              intro hqle
              exact hiL
                ((firstSplitterLeftThroughPIndices.mem_iff R φ).mpr ⟨q', hφ, hqle⟩)
            have hqval : q'.val = n - 2 := by
              have hge : n - 2 ≤ q'.val := by omega
              have hle : q'.val ≤ n := by omega
              by_cases hsval : q'.val = n - 1
              · have hqs : q' = firstSplitter_s n := by
                  apply Fin.ext
                  simp [firstSplitter_s]
                  exact hsval
                exact False.elim (hsnone ⟨i, by rw [hφ, hqs]⟩)
              by_cases htval : q'.val = n
              · have hqt : q' = firstSplitter_t n := by
                  apply Fin.ext
                  simp [firstSplitter_t]
                  exact htval
                exact False.elim (htnone ⟨i, by rw [hφ, hqt]⟩)
              · omega
            have hqr : q' = firstSplitter_r n := by
              apply Fin.ext
              simp [firstSplitter_r]
              exact hqval
            rw [hqr])
  · by_cases hIBle_one : IB.card ≤ 1
    · have hOcard : O.card ≤ 2 := by omega
      have hLcard : L.card ≤ n - 2 := by
        simpa [L] using firstSplitter_leftThroughP_card_le (by omega) R φ
      have hsmall : O.card + L.card < n + 2 := by omega
      exact inducedPath_two_part_card_contradiction φ O L hsmall (by
        intro i
        cases hφ : φ i with
        | inr u' =>
            exact Or.inl
              ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u', hφ⟩)
        | inl q' =>
            by_cases hqle : q'.val ≤ n - 3
            · exact Or.inr
                ((firstSplitterLeftThroughPIndices.mem_iff R φ).mpr ⟨q', hφ, hqle⟩)
            · exfalso
              have hge : n - 2 ≤ q'.val := by omega
              have hle : q'.val ≤ n := by omega
              by_cases hrval : q'.val = n - 2
              · have hqr : q' = firstSplitter_r n := by
                  apply Fin.ext
                  simp [firstSplitter_r]
                  exact hrval
                exact hrx ⟨i, by rw [hφ, hqr]⟩
              by_cases hsval : q'.val = n - 1
              · have hqs : q' = firstSplitter_s n := by
                  apply Fin.ext
                  simp [firstSplitter_s]
                  exact hsval
                exact hsnone ⟨i, by rw [hφ, hqs]⟩
              by_cases htval : q'.val = n
              · have hqt : q' = firstSplitter_t n := by
                  apply Fin.ext
                  simp [firstSplitter_t]
                  exact htval
                exact htnone ⟨i, by rw [hφ, hqt]⟩
              · omega)
    · have hIBcard : IB.card = 2 := by omega
      have hOcard : O.card ≤ 4 := by omega
      have hLcard : L.card ≤ n - 3 := by
        simpa [L, IB] using
          firstSplitter_leftThroughP_card_le_of_p_and_two_B hn R φ hp hIBcard
      have hsmall : O.card + L.card < n + 2 := by omega
      exact inducedPath_two_part_card_contradiction φ O L hsmall (by
        intro i
        cases hφ : φ i with
        | inr u' =>
            exact Or.inl
              ((firstSplitterOutsideIndices.mem_iff R φ).mpr ⟨u', hφ⟩)
        | inl q' =>
            by_cases hqle : q'.val ≤ n - 3
            · exact Or.inr
                ((firstSplitterLeftThroughPIndices.mem_iff R φ).mpr ⟨q', hφ, hqle⟩)
            · exfalso
              have hge : n - 2 ≤ q'.val := by omega
              have hle : q'.val ≤ n := by omega
              by_cases hrval : q'.val = n - 2
              · have hqr : q' = firstSplitter_r n := by
                  apply Fin.ext
                  simp [firstSplitter_r]
                  exact hrval
                exact hrx ⟨i, by rw [hφ, hqr]⟩
              by_cases hsval : q'.val = n - 1
              · have hqs : q' = firstSplitter_s n := by
                  apply Fin.ext
                  simp [firstSplitter_s]
                  exact hsval
                exact hsnone ⟨i, by rw [hφ, hqs]⟩
              by_cases htval : q'.val = n
              · have hqt : q' = firstSplitter_t n := by
                  apply Fin.ext
                  simp [firstSplitter_t]
                  exact htval
                exact htnone ⟨i, by rw [hφ, hqt]⟩
              · omega)

/--
If every vertex of an induced path in the first-splitter graph lies outside the
base path, projection gives the same induced path in the interface.
-/
noncomputable def firstSplitterAllOutsidePathEmbedding
    {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hout : ∀ i : Fin (n + 2), ∃ u : Sum A B, φ i = Sum.inr u) :
    SimpleGraph.pathGraph (n + 2) ↪g firstSplitterInterfaceGraph R where
  toFun i := Classical.choose (hout i)
  inj' := by
    intro i j hij
    apply (RelEmbedding.inj φ).mp
    calc
      φ i = Sum.inr (Classical.choose (hout i)) := Classical.choose_spec (hout i)
      _ = Sum.inr (Classical.choose (hout j)) := congrArg Sum.inr hij
      _ = φ j := (Classical.choose_spec (hout j)).symm
  map_rel_iff' := by
    intro i j
    have hi := Classical.choose_spec (hout i)
    have hj := Classical.choose_spec (hout j)
    have hiff := φ.map_rel_iff (a := i) (b := j)
    rw [hi, hj] at hiff
    simpa using hiff

theorem firstSplitter_allOutside_pathFree_contradiction
    {n : ℕ} (R : A → B → Prop)
    (hR : InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterInterfaceGraph R))
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hout : ∀ i : Fin (n + 2), ∃ u : Sum A B, φ i = Sum.inr u) : False := by
  exact hR ⟨firstSplitterAllOutsidePathEmbedding R φ hout⟩

/-- An induced `P_{n+2}` in the first-splitter graph cannot lie wholly in the shorter base path. -/
theorem firstSplitter_allPath_contradiction
    {n : ℕ} (R : A → B → Prop)
    (φ : SimpleGraph.pathGraph (n + 2) ↪g firstSplitterGraph n R)
    (hpath : ∀ i : Fin (n + 2), ∃ q : Fin (n + 1), φ i = Sum.inl q) : False := by
  let f : Fin (n + 2) → Fin (n + 1) := fun i => Classical.choose (hpath i)
  have hf : Function.Injective f := by
    intro i j hij
    apply (RelEmbedding.inj φ).mp
    calc
      φ i = Sum.inl (Classical.choose (hpath i)) := Classical.choose_spec (hpath i)
      _ = Sum.inl (Classical.choose (hpath j)) := congrArg Sum.inl hij
      _ = φ j := (Classical.choose_spec (hpath j)).symm
  have hle := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at hle

/--
Checked hard converse of `thm:first-splitter`: for `n ≥ 4`, if the bipartite
interface is `P_{n+2}`-free, then the whole first-splitter graph is
`P_{n+2}`-free.
-/
theorem firstSplitter_graph_pathFree_of_interface_pathFree
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop)
    (hR : InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterInterfaceGraph R)) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterGraph n R) := by
  classical
  intro hcopy
  rcases hcopy with ⟨φ⟩
  by_cases hout : ∀ i : Fin (n + 2), ∃ u : Sum A B, φ i = Sum.inr u
  · exact firstSplitter_allOutside_pathFree_contradiction R hR φ hout
  · have hpath_exists :
        ∃ iq : Fin (n + 2), ∃ q : Fin (n + 1), φ iq = Sum.inl q := by
      rcases not_forall.mp hout with ⟨iq, hiq⟩
      cases hφ : φ iq with
      | inl q =>
          exact ⟨iq, q, hφ⟩
      | inr u =>
          exact False.elim (hiq ⟨u, hφ⟩)
    by_cases hpath : ∀ i : Fin (n + 2), ∃ q : Fin (n + 1), φ i = Sum.inl q
    · exact firstSplitter_allPath_contradiction R φ hpath
    · have hout_exists :
          ∃ io : Fin (n + 2), ∃ u : Sum A B, φ io = Sum.inr u := by
        rcases not_forall.mp hpath with ⟨io, hio⟩
        cases hφ : φ io with
        | inr u =>
            exact ⟨io, u, hφ⟩
        | inl q =>
            exact False.elim (hio ⟨q, hφ⟩)
      rcases hout_exists with ⟨io, u, ho⟩
      rcases hpath_exists with ⟨iq, q, hq⟩
      by_cases htx : ∃ it : Fin (n + 2), φ it = Sum.inl (firstSplitter_t n)
      · rcases htx with ⟨it, ht⟩
        exact firstSplitter_mixed_with_t_contradiction hn R φ ho ht
      · by_cases hsx : ∃ is : Fin (n + 2), φ is = Sum.inl (firstSplitter_s n)
        · rcases hsx with ⟨is, hs⟩
          exact firstSplitter_mixed_with_s_no_t_contradiction hn R φ ho hs htx
        · exact firstSplitter_mixed_without_s_t_contradiction hn R φ ho hq hsx htx

theorem firstSplitter_pathFree_iff_interface_pathFree
    {n : ℕ} (hn : 4 ≤ n) (R : A → B → Prop) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterGraph n R) ↔
      InducedFree (SimpleGraph.pathGraph (n + 2)) (firstSplitterInterfaceGraph R) := by
  constructor
  · exact firstSplitter_interface_pathFree_of_graph_pathFree n R
  · exact firstSplitter_graph_pathFree_of_interface_pathFree hn R

end Erdos61
