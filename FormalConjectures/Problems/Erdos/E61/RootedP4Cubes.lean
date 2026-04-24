import FormalConjectures.Problems.Erdos.E61.RootedP4

/-!
# Graph-level rooted `P4` Boolean cubes

This file turns the rectangle-level Boolean obstruction constructions into
actual purified rooted-`P4` graph configurations.  It formalizes the
private-matching cube used in the matching half of `prop:boolean-obstructions`
and `thm:H-specific-cubes`.
-/

namespace Erdos61

open Finset

/-- The finite graph-side purification conditions from `def:purified`. -/
def IsPurifiedRootedP4 {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (B₁ B₂ B₃ B₄ Y : Finset V) : Prop :=
  Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₁ B₄ ∧ Disjoint B₁ Y ∧
  Disjoint B₂ B₃ ∧ Disjoint B₂ B₄ ∧ Disjoint B₂ Y ∧
  Disjoint B₃ B₄ ∧ Disjoint B₃ Y ∧ Disjoint B₄ Y ∧
  Anticomplete G.Adj B₁ (B₃ ∪ B₄) ∧
  Anticomplete G.Adj B₂ B₄ ∧
  Anticomplete G.Adj Y (B₂ ∪ B₃)

/-- Left endpoint witnesses for crossing traces. -/
def CrossingLeftWitness {V : Type*} (G : SimpleGraph V) (B₁ : Finset V)
    (b₂ y : V) : Prop :=
  ∃ a ∈ B₁, G.Adj y a ∧ G.Adj b₂ a

/-- Right endpoint witnesses for crossing traces. -/
def CrossingRightWitness {V : Type*} (G : SimpleGraph V) (B₄ : Finset V)
    (b₃ y : V) : Prop :=
  ∃ d ∈ B₄, G.Adj y d ∧ G.Adj b₃ d

/-- The crossing trace `C_y = E(B₂,B₃) ∩ (P_y × Q_y)`. -/
noncomputable def crossingTrace {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (B₁ B₂ B₃ B₄ : Finset V) (y : V) :
    Finset (V × V) := by
  classical
  exact (B₂ ×ˢ B₃).filter fun e =>
    G.Adj e.1 e.2 ∧
      CrossingLeftWitness G B₁ e.1 y ∧
      CrossingRightWitness G B₄ e.2 y

/-- Crossing traces indexed by the `Y` side. -/
noncomputable def crossingTraceFamily {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (B₁ B₂ B₃ B₄ Y : Finset V) :
    Finset (Finset (V × V)) :=
  Y.image fun y => crossingTrace G B₁ B₂ B₃ B₄ y

/-- Vertices of the private-matching cube `PM_m`. -/
inductive PMVertex (m : ℕ) where
  | x : Finset (Fin m) → PMVertex m
  | l : Fin m → PMVertex m
  | r : Fin m → PMVertex m
  | d : PMVertex m
  | y : Finset (Fin m) → PMVertex m
  deriving DecidableEq, Fintype

namespace PMVertex

variable {m : ℕ}

/-- Directed edge relation whose symmetrization is the private-matching cube. -/
def rel (m : ℕ) : PMVertex m → PMVertex m → Prop
  | x S, l i => i ∈ S
  | l i, r j => i = j
  | r _, d => True
  | d, y _ => True
  | y S, x T => S = T
  | _, _ => False

/-- The private-matching cube graph. -/
def graph (m : ℕ) : SimpleGraph (PMVertex m) :=
  SimpleGraph.fromRel (rel m)

def B₁ (m : ℕ) : Finset (PMVertex m) :=
  (univ : Finset (Finset (Fin m))).image x

def B₂ (m : ℕ) : Finset (PMVertex m) :=
  (univ : Finset (Fin m)).image l

def B₃ (m : ℕ) : Finset (PMVertex m) :=
  (univ : Finset (Fin m)).image r

def B₄ (m : ℕ) : Finset (PMVertex m) :=
  {d}

def Y (m : ℕ) : Finset (PMVertex m) :=
  (univ : Finset (Finset (Fin m))).image y

def middleEdges (m : ℕ) : Finset (PMVertex m × PMVertex m) :=
  (univ : Finset (Fin m)).image fun i => (l i, r i)

@[simp] theorem mem_B₁ {m : ℕ} {v : PMVertex m} :
    v ∈ B₁ m ↔ ∃ S : Finset (Fin m), v = x S := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨S, _hS, rfl⟩
    exact ⟨S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact mem_image.mpr ⟨S, mem_univ S, rfl⟩

@[simp] theorem mem_B₂ {m : ℕ} {v : PMVertex m} :
    v ∈ B₂ m ↔ ∃ i : Fin m, v = l i := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩

@[simp] theorem mem_B₃ {m : ℕ} {v : PMVertex m} :
    v ∈ B₃ m ↔ ∃ i : Fin m, v = r i := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩

@[simp] theorem mem_B₄ {m : ℕ} {v : PMVertex m} :
    v ∈ B₄ m ↔ v = d := by
  simp [B₄]

@[simp] theorem mem_Y {m : ℕ} {v : PMVertex m} :
    v ∈ Y m ↔ ∃ S : Finset (Fin m), v = y S := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨S, _hS, rfl⟩
    exact ⟨S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact mem_image.mpr ⟨S, mem_univ S, rfl⟩

@[simp] theorem graph_adj_x_l {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    (graph m).Adj (x S) (l i) ↔ i ∈ S := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_l_x {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    (graph m).Adj (l i) (x S) ↔ i ∈ S := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_l_r {m : ℕ} (i j : Fin m) :
    (graph m).Adj (l i) (r j) ↔ i = j := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_r_l {m : ℕ} (i j : Fin m) :
    (graph m).Adj (r j) (l i) ↔ i = j := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_r_d {m : ℕ} (i : Fin m) :
    (graph m).Adj (r i) d := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_d_r {m : ℕ} (i : Fin m) :
    (graph m).Adj d (r i) := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_d_y {m : ℕ} (S : Finset (Fin m)) :
    (graph m).Adj d (y S) := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_y_d {m : ℕ} (S : Finset (Fin m)) :
    (graph m).Adj (y S) d := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_y_x {m : ℕ} (S T : Finset (Fin m)) :
    (graph m).Adj (y S) (x T) ↔ S = T := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_x_y {m : ℕ} (S T : Finset (Fin m)) :
    (graph m).Adj (x T) (y S) ↔ S = T := by
  rw [(graph m).adj_comm]
  simp

set_option linter.unnecessarySimpa false in
set_option linter.flexible false in
theorem purified (m : ℕ) :
    IsPurifiedRootedP4 (graph m) (B₁ m) (B₂ m) (B₃ m) (B₄ m) (Y m) := by
  classical
  repeat' constructor
  all_goals
    try
      (rw [disjoint_iff_ne];
       intro a ha b hb;
       simp at ha hb;
       aesop)
  · intro a ha b hb hab
    simp at ha hb
    rcases ha with ⟨S, rfl⟩
    rcases hb with (⟨i, rfl⟩ | rfl)
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using hab
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using hab
  · intro a ha b hb hab
    simp at ha hb
    rcases ha with ⟨i, rfl⟩
    subst b
    simpa [graph, rel, SimpleGraph.fromRel_adj] using hab
  · intro a ha b hb hab
    simp at ha hb
    rcases ha with ⟨S, rfl⟩
    rcases hb with (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using hab
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using hab

theorem middleEdges_card (m : ℕ) :
    (middleEdges m).card = m := by
  classical
  rw [middleEdges, card_image_of_injOn]
  · simp
  · intro i _hi j _hj hij
    have hleft : l i = l j := congrArg Prod.fst hij
    injection hleft

@[simp] theorem mem_middleEdges {m : ℕ} {e : PMVertex m × PMVertex m} :
    e ∈ middleEdges m ↔ ∃ i : Fin m, e = (l i, r i) := by
  constructor
  · intro he
    rcases mem_image.mp he with ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩

/-- Exact crossing trace in the private-matching cube. -/
theorem crossingTrace_y {m : ℕ} (S : Finset (Fin m)) :
    crossingTrace (graph m) (B₁ m) (B₂ m) (B₃ m) (B₄ m) (y S) =
      S.image fun i => (l i, r i) := by
  classical
  ext e
  rcases e with ⟨u, v⟩
  constructor
  · intro he
    rw [crossingTrace] at he
    simp only [mem_filter, mem_product] at he
    rcases he with ⟨⟨heB₂, heB₃⟩, hmid, hleft, _hright⟩
    rcases mem_B₂.mp heB₂ with ⟨i, rfl⟩
    rcases mem_B₃.mp heB₃ with ⟨j, rfl⟩
    have hij : i = j := by simpa using hmid
    subst j
    rcases hleft with ⟨a, ha, hya, hia⟩
    rcases mem_B₁.mp ha with ⟨T, rfl⟩
    have hST : S = T := by simpa using hya
    have hiT : i ∈ T := by simpa using hia
    exact mem_image.mpr ⟨i, by simpa [hST] using hiT, rfl⟩
  · intro he
    rcases mem_image.mp he with ⟨i, hiS, hpair⟩
    cases hpair
    rw [crossingTrace]
    simp only [mem_filter, mem_product]
    refine ⟨⟨?_, ?_⟩, by simp, ?_, ?_⟩
    · exact mem_B₂.mpr ⟨i, rfl⟩
    · exact mem_B₃.mpr ⟨i, rfl⟩
    · exact ⟨x S, mem_B₁.mpr ⟨S, rfl⟩, by simp, by simpa using hiS⟩
    · exact ⟨d, by simp, by simp, by simp⟩

def indexSetOfMiddleSubset {m : ℕ} (T : Finset (PMVertex m × PMVertex m)) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun i => (l i, r i) ∈ T

theorem image_indexSetOfMiddleSubset {m : ℕ}
    {T : Finset (PMVertex m × PMVertex m)} (hT : T ⊆ middleEdges m) :
    (indexSetOfMiddleSubset T).image (fun i => (l i, r i)) = T := by
  classical
  ext e
  constructor
  · intro he
    rcases mem_image.mp he with ⟨i, hi, rfl⟩
    exact (mem_filter.mp hi).2
  · intro he
    rcases mem_middleEdges.mp (hT he) with ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, he⟩, rfl⟩

/--
Graph-level matching half of `prop:boolean-obstructions`: the actual crossing
traces in the private-matching cube shatter a matching with `m` edges.
-/
theorem privateMatching_crossingTraceFamily_shatters_matching (m : ℕ) :
    (crossingTraceFamily (graph m) (B₁ m) (B₂ m) (B₃ m) (B₄ m) (Y m)).Shatters
      (middleEdges m) := by
  classical
  refine Finset.shatters_of_forall_subset ?_
  intro T hT
  refine mem_image.mpr ?_
  let S := indexSetOfMiddleSubset T
  refine ⟨y S, ?_, ?_⟩
  · exact mem_Y.mpr ⟨S, rfl⟩
  · rw [crossingTrace_y, image_indexSetOfMiddleSubset hT]

end PMVertex

/-- Vertices of the Boolean-star cube `BS_m`. -/
inductive BSVertex (m : ℕ) where
  | a : BSVertex m
  | c : BSVertex m
  | r : Fin m → BSVertex m
  | z : Finset (Fin m) → BSVertex m
  | y : Finset (Fin m) → BSVertex m
  deriving DecidableEq, Fintype

namespace BSVertex

/-- Directed edge relation whose symmetrization is the Boolean-star cube. -/
def rel (m : ℕ) : BSVertex m → BSVertex m → Prop
  | a, c => True
  | c, r _ => True
  | r i, z S => i ∈ S
  | z S, y T => S = T
  | y _, a => True
  | _, _ => False

/-- The Boolean-star cube graph. -/
def graph (m : ℕ) : SimpleGraph (BSVertex m) :=
  SimpleGraph.fromRel (rel m)

def B₁ (m : ℕ) : Finset (BSVertex m) :=
  {a}

def B₂ (m : ℕ) : Finset (BSVertex m) :=
  {c}

def B₃ (m : ℕ) : Finset (BSVertex m) :=
  (univ : Finset (Fin m)).image r

def B₄ (m : ℕ) : Finset (BSVertex m) :=
  (univ : Finset (Finset (Fin m))).image z

def Y (m : ℕ) : Finset (BSVertex m) :=
  (univ : Finset (Finset (Fin m))).image y

def middleEdges (m : ℕ) : Finset (BSVertex m × BSVertex m) :=
  (univ : Finset (Fin m)).image fun i => (c, r i)

@[simp] theorem mem_B₁ {m : ℕ} {v : BSVertex m} :
    v ∈ B₁ m ↔ v = a := by
  simp [B₁]

@[simp] theorem mem_B₂ {m : ℕ} {v : BSVertex m} :
    v ∈ B₂ m ↔ v = c := by
  simp [B₂]

@[simp] theorem mem_B₃ {m : ℕ} {v : BSVertex m} :
    v ∈ B₃ m ↔ ∃ i : Fin m, v = r i := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩

@[simp] theorem mem_B₄ {m : ℕ} {v : BSVertex m} :
    v ∈ B₄ m ↔ ∃ S : Finset (Fin m), v = z S := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨S, _hS, rfl⟩
    exact ⟨S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact mem_image.mpr ⟨S, mem_univ S, rfl⟩

@[simp] theorem mem_Y {m : ℕ} {v : BSVertex m} :
    v ∈ Y m ↔ ∃ S : Finset (Fin m), v = y S := by
  constructor
  · intro hv
    rcases mem_image.mp hv with ⟨S, _hS, rfl⟩
    exact ⟨S, rfl⟩
  · rintro ⟨S, rfl⟩
    exact mem_image.mpr ⟨S, mem_univ S, rfl⟩

@[simp] theorem graph_adj_a_c {m : ℕ} :
    (graph m).Adj (a : BSVertex m) c := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_c_a {m : ℕ} :
    (graph m).Adj (c : BSVertex m) a := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_c_r {m : ℕ} (i : Fin m) :
    (graph m).Adj c (r i) := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_r_c {m : ℕ} (i : Fin m) :
    (graph m).Adj (r i) c := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_r_z {m : ℕ} (i : Fin m) (S : Finset (Fin m)) :
    (graph m).Adj (r i) (z S) ↔ i ∈ S := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_z_r {m : ℕ} (i : Fin m) (S : Finset (Fin m)) :
    (graph m).Adj (z S) (r i) ↔ i ∈ S := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_z_y {m : ℕ} (S T : Finset (Fin m)) :
    (graph m).Adj (z S) (y T) ↔ S = T := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_y_z {m : ℕ} (S T : Finset (Fin m)) :
    (graph m).Adj (y T) (z S) ↔ S = T := by
  rw [(graph m).adj_comm]
  simp

@[simp] theorem graph_adj_y_a {m : ℕ} (S : Finset (Fin m)) :
    (graph m).Adj (y S) a := by
  simp [graph, rel, SimpleGraph.fromRel_adj]

@[simp] theorem graph_adj_a_y {m : ℕ} (S : Finset (Fin m)) :
    (graph m).Adj a (y S) := by
  rw [(graph m).adj_comm]
  simp

set_option linter.unnecessarySimpa false in
set_option linter.flexible false in
theorem purified (m : ℕ) :
    IsPurifiedRootedP4 (graph m) (B₁ m) (B₂ m) (B₃ m) (B₄ m) (Y m) := by
  classical
  repeat' constructor
  all_goals
    try
      (rw [disjoint_iff_ne];
       intro u hu v hv;
       simp at hu hv;
       aesop)
  · intro u hu v hv huv
    simp at hu hv
    subst u
    rcases hv with (⟨i, rfl⟩ | ⟨S, rfl⟩)
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using huv
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using huv
  · intro u hu v hv huv
    simp at hu hv
    subst u
    rcases hv with ⟨S, rfl⟩
    simpa [graph, rel, SimpleGraph.fromRel_adj] using huv
  · intro u hu v hv huv
    simp at hu hv
    rcases hu with ⟨S, rfl⟩
    rcases hv with (rfl | ⟨i, rfl⟩)
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using huv
    · simpa [graph, rel, SimpleGraph.fromRel_adj] using huv

theorem middleEdges_card (m : ℕ) :
    (middleEdges m).card = m := by
  classical
  rw [middleEdges, card_image_of_injOn]
  · simp
  · intro i _hi j _hj hij
    have hright : r i = r j := congrArg Prod.snd hij
    injection hright

@[simp] theorem mem_middleEdges {m : ℕ} {e : BSVertex m × BSVertex m} :
    e ∈ middleEdges m ↔ ∃ i : Fin m, e = (c, r i) := by
  constructor
  · intro he
    rcases mem_image.mp he with ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_univ i, rfl⟩

/-- Exact crossing trace in the Boolean-star cube. -/
theorem crossingTrace_y {m : ℕ} (S : Finset (Fin m)) :
    crossingTrace (graph m) (B₁ m) (B₂ m) (B₃ m) (B₄ m) (y S) =
      S.image fun i => (c, r i) := by
  classical
  ext e
  rcases e with ⟨u, v⟩
  constructor
  · intro he
    rw [crossingTrace] at he
    simp only [mem_filter, mem_product] at he
    rcases he with ⟨⟨heB₂, heB₃⟩, _hmid, _hleft, hright⟩
    rw [mem_B₂] at heB₂
    subst u
    rcases mem_B₃.mp heB₃ with ⟨i, rfl⟩
    rcases hright with ⟨d, hd, hyd, hid⟩
    rcases mem_B₄.mp hd with ⟨T, rfl⟩
    have hST : T = S := by simpa using hyd
    have hiT : i ∈ T := by simpa using hid
    exact mem_image.mpr ⟨i, by simpa [hST] using hiT, rfl⟩
  · intro he
    rcases mem_image.mp he with ⟨i, hiS, hpair⟩
    cases hpair
    rw [crossingTrace]
    simp only [mem_filter, mem_product]
    refine ⟨⟨?_, ?_⟩, by simp, ?_, ?_⟩
    · exact mem_B₂.mpr rfl
    · exact mem_B₃.mpr ⟨i, rfl⟩
    · exact ⟨a, by simp, by simp, by simp⟩
    · exact ⟨z S, mem_B₄.mpr ⟨S, rfl⟩, by simp, by simpa using hiS⟩

def indexSetOfMiddleSubset {m : ℕ} (T : Finset (BSVertex m × BSVertex m)) :
    Finset (Fin m) :=
  (univ : Finset (Fin m)).filter fun i => (c, r i) ∈ T

theorem image_indexSetOfMiddleSubset {m : ℕ}
    {T : Finset (BSVertex m × BSVertex m)} (hT : T ⊆ middleEdges m) :
    (indexSetOfMiddleSubset T).image (fun i => (c, r i)) = T := by
  classical
  ext e
  constructor
  · intro he
    rcases mem_image.mp he with ⟨i, hi, rfl⟩
    exact (mem_filter.mp hi).2
  · intro he
    rcases mem_middleEdges.mp (hT he) with ⟨i, rfl⟩
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, he⟩, rfl⟩

/--
Graph-level star half of `prop:boolean-obstructions`: the actual crossing
traces in the Boolean-star cube shatter a star with `m` edges.
-/
theorem booleanStar_crossingTraceFamily_shatters_star (m : ℕ) :
    (crossingTraceFamily (graph m) (B₁ m) (B₂ m) (B₃ m) (B₄ m) (Y m)).Shatters
      (middleEdges m) := by
  classical
  refine Finset.shatters_of_forall_subset ?_
  intro T hT
  refine mem_image.mpr ?_
  let S := indexSetOfMiddleSubset T
  refine ⟨y S, ?_, ?_⟩
  · exact mem_Y.mpr ⟨S, rfl⟩
  · rw [crossingTrace_y, image_indexSetOfMiddleSubset hT]

end BSVertex

/--
Combined graph-level version of `prop:boolean-obstructions`: the Boolean-star
cube gives purified configurations shattering a star of size `m`, and the
private-matching cube gives purified configurations shattering a matching of
size `m`.
-/
theorem purified_rootedP4_boolean_obstructions_graph (m : ℕ) :
    IsPurifiedRootedP4 (BSVertex.graph m)
        (BSVertex.B₁ m) (BSVertex.B₂ m) (BSVertex.B₃ m) (BSVertex.B₄ m) (BSVertex.Y m) ∧
      (BSVertex.middleEdges m).card = m ∧
      (crossingTraceFamily (BSVertex.graph m)
        (BSVertex.B₁ m) (BSVertex.B₂ m) (BSVertex.B₃ m) (BSVertex.B₄ m)
        (BSVertex.Y m)).Shatters (BSVertex.middleEdges m) ∧
      IsPurifiedRootedP4 (PMVertex.graph m)
        (PMVertex.B₁ m) (PMVertex.B₂ m) (PMVertex.B₃ m) (PMVertex.B₄ m) (PMVertex.Y m) ∧
      (PMVertex.middleEdges m).card = m ∧
      (crossingTraceFamily (PMVertex.graph m)
        (PMVertex.B₁ m) (PMVertex.B₂ m) (PMVertex.B₃ m) (PMVertex.B₄ m)
        (PMVertex.Y m)).Shatters (PMVertex.middleEdges m) := by
  exact ⟨BSVertex.purified m, BSVertex.middleEdges_card m,
    BSVertex.booleanStar_crossingTraceFamily_shatters_star m,
    PMVertex.purified m, PMVertex.middleEdges_card m,
    PMVertex.privateMatching_crossingTraceFamily_shatters_matching m⟩

end Erdos61
