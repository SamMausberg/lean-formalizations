import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Singleton-cut Boolean shadow

This file formalizes the ladder-index part of the singleton-cut obstruction
from `thm:singleton-cut`.  Rows are `0` plus the singleton cuts of `K_m`;
columns are ordered non-loop edge coordinates.  The final theorem proves that
any ladder in this parity matrix has size at most two.
-/

open Finset

namespace Erdos61

/--
Boolean edge-parity cancellation: if two Boolean labelings have the same xor
on an edge, then their pointwise xor agrees at the two endpoints.
-/
theorem bool_rowXor_eq_of_edgeParity_eq {a₁ a₂ b₁ b₂ : Bool}
    (h : (a₁ != a₂) = (b₁ != b₂)) :
    (a₁ != b₁) = (a₂ != b₂) := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> simp at h ⊢

/--
Along a walk, equality of Boolean edge parities forces the pointwise xor of the
two rows to be constant between the endpoints.
-/
theorem bool_rowXor_eq_of_walk {V : Type*} {G : SimpleGraph V}
    (a b : V → Bool) {u v : V} (p : G.Walk u v)
    (hpar : ∀ x y, G.Adj x y → (a x != a y) = (b x != b y)) :
    (a u != b u) = (a v != b v) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      exact (bool_rowXor_eq_of_edgeParity_eq (hpar _ _ h)).trans ih

/--
Connected row-consistency core: on a preconnected graph, parity on every edge
determines a Boolean row up to global complement.
-/
theorem bool_rowXor_constant_of_preconnected {V : Type*} {G : SimpleGraph V}
    (hG : G.Preconnected) (a b : V → Bool)
    (hpar : ∀ x y, G.Adj x y → (a x != a y) = (b x != b y)) :
    ∀ u v, (a u != b u) = (a v != b v) := by
  intro u v
  rcases hG u v with ⟨p⟩
  exact bool_rowXor_eq_of_walk a b p hpar

/-- The rows `c₀,c₁,...,c_m`: `none` is `c₀`, `some i` is the singleton cut at `i`. -/
abbrev CutRow (m : ℕ) := Option (Fin m)

/-- Ordered non-loop edge coordinates of `K_m`. -/
abbrev KEdge (m : ℕ) := {e : Fin m × Fin m // e.1 ≠ e.2}

def KEdge.left {m : ℕ} (e : KEdge m) : Fin m := e.1.1
def KEdge.right {m : ℕ} (e : KEdge m) : Fin m := e.1.2

lemma KEdge.left_ne_right {m : ℕ} (e : KEdge m) : e.left ≠ e.right := e.2

def edgeOfDistinct {m : ℕ} (i j : Fin m) (hij : i ≠ j) : KEdge m :=
  ⟨(i, j), hij⟩

@[simp] lemma edgeOfDistinct_left {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    (edgeOfDistinct i j hij).left = i := rfl

@[simp] lemma edgeOfDistinct_right {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    (edgeOfDistinct i j hij).right = j := rfl

/-- The singleton supporting a nonzero cut row, or empty support for `0`. -/
def cutRowSupport {m : ℕ} : CutRow m → Finset (Fin m)
  | none => ∅
  | some i => {i}

@[simp] lemma mem_cutRowSupport_iff {m : ℕ} {r : CutRow m} {i : Fin m} :
    i ∈ cutRowSupport r ↔ r = some i := by
  cases r with
  | none => simp [cutRowSupport]
  | some j =>
      simp only [cutRowSupport, mem_singleton, Option.some.injEq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem card_cutRowSupport_le_one {m : ℕ} (r : CutRow m) :
    (cutRowSupport r).card ≤ 1 := by
  cases r <;> simp [cutRowSupport]

def cutRowsSupport4 {m : ℕ} (r₀ r₁ r₂ r₃ : CutRow m) : Finset (Fin m) :=
  cutRowSupport r₀ ∪ cutRowSupport r₁ ∪ cutRowSupport r₂ ∪ cutRowSupport r₃

theorem card_cutRowsSupport4_le_four {m : ℕ} (r₀ r₁ r₂ r₃ : CutRow m) :
    (cutRowsSupport4 r₀ r₁ r₂ r₃).card ≤ 4 := by
  let A := cutRowSupport r₀
  let B := cutRowSupport r₁
  let C := cutRowSupport r₂
  let D := cutRowSupport r₃
  change (A ∪ B ∪ C ∪ D).card ≤ 4
  have hABCD : (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B ∪ C).card + D.card :=
    card_union_le _ _
  have hABC : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card :=
    card_union_le _ _
  have hAB : (A ∪ B).card ≤ A.card + B.card := card_union_le _ _
  have hA : A.card ≤ 1 := card_cutRowSupport_le_one r₀
  have hB : B.card ≤ 1 := card_cutRowSupport_le_one r₁
  have hC : C.card ≤ 1 := card_cutRowSupport_le_one r₂
  have hD : D.card ≤ 1 := card_cutRowSupport_le_one r₃
  omega

theorem exists_not_mem_cutRowsSupport4 {m : ℕ} (hm : 4 < m)
    (r₀ r₁ r₂ r₃ : CutRow m) :
    ∃ z : Fin m, z ∉ cutRowsSupport4 r₀ r₁ r₂ r₃ := by
  classical
  have hcard : (cutRowsSupport4 r₀ r₁ r₂ r₃).card < (Finset.univ : Finset (Fin m)).card := by
    rw [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (card_cutRowsSupport4_le_four r₀ r₁ r₂ r₃) hm
  rcases exists_mem_notMem_of_card_lt_card hcard with ⟨z, _hzuniv, hz⟩
  exact ⟨z, hz⟩

/-- The parity value of a singleton cut on an edge coordinate. -/
def cutBit {m : ℕ} (r : CutRow m) (e : KEdge m) : Bool :=
  match r with
  | none => false
  | some i => decide (i = e.left ∨ i = e.right)

@[simp] lemma cutBit_none {m : ℕ} (e : KEdge m) :
    cutBit (none : CutRow m) e = false := rfl

lemma cutBit_some_eq_true {m : ℕ} (i : Fin m) (e : KEdge m) :
    cutBit (some i : CutRow m) e = true ↔ i = e.left ∨ i = e.right := by
  simp [cutBit]

lemma cutBit_eq_true_iff {m : ℕ} (r : CutRow m) (e : KEdge m) :
    cutBit r e = true ↔ r = some e.left ∨ r = some e.right := by
  cases r with
  | none => simp [cutBit]
  | some i =>
      constructor
      · intro h
        rcases (cutBit_some_eq_true i e).mp h with hi | hi
        · left
          rw [hi]
        · right
          rw [hi]
      · intro h
        rcases h with h | h
        · rw [h]
          exact (cutBit_some_eq_true e.left e).mpr (Or.inl rfl)
        · rw [h]
          exact (cutBit_some_eq_true e.right e).mpr (Or.inr rfl)

lemma cutBit_edgeOfDistinct_eq_decide
    {m : ℕ} {i z : Fin m} (hiz : i ≠ z) {r : CutRow m}
    (hz : z ∉ cutRowSupport r) :
    cutBit r (edgeOfDistinct i z hiz) = decide (r = some i) := by
  by_cases hr : r = some i
  · subst r
    simp [cutBit_some_eq_true]
  · have hrz : r ≠ some z := by
      intro h
      exact hz (mem_cutRowSupport_iff.mpr h)
    have hnot : cutBit r (edgeOfDistinct i z hiz) ≠ true := by
      intro ht
      rcases (cutBit_eq_true_iff r (edgeOfDistinct i z hiz)).mp ht with hri | hrz'
      · exact hr hri
      · exact hrz hrz'
    cases hbit : cutBit r (edgeOfDistinct i z hiz)
    · simp [hr]
    · exact False.elim (hnot hbit)

theorem exists_edge_cutBit_eq_selected
    {m : ℕ} (hm : 4 < m) (r₀ r₁ r₂ r₃ : CutRow m) {i : Fin m}
    (hi : r₀ = some i ∨ r₁ = some i ∨ r₂ = some i ∨ r₃ = some i) :
    ∃ e : KEdge m,
      cutBit r₀ e = decide (r₀ = some i) ∧
      cutBit r₁ e = decide (r₁ = some i) ∧
      cutBit r₂ e = decide (r₂ = some i) ∧
      cutBit r₃ e = decide (r₃ = some i) := by
  classical
  rcases exists_not_mem_cutRowsSupport4 hm r₀ r₁ r₂ r₃ with ⟨z, hz⟩
  have hz₀ : z ∉ cutRowSupport r₀ := by
    intro hz₀
    exact hz (by simp [cutRowsSupport4, hz₀])
  have hz₁ : z ∉ cutRowSupport r₁ := by
    intro hz₁
    exact hz (by simp [cutRowsSupport4, hz₁])
  have hz₂ : z ∉ cutRowSupport r₂ := by
    intro hz₂
    exact hz (by simp [cutRowsSupport4, hz₂])
  have hz₃ : z ∉ cutRowSupport r₃ := by
    intro hz₃
    exact hz (by simp [cutRowsSupport4, hz₃])
  have hiz : i ≠ z := by
    intro hiz
    subst z
    rcases hi with hi | hi | hi | hi
    · exact hz₀ (mem_cutRowSupport_iff.mpr hi)
    · exact hz₁ (mem_cutRowSupport_iff.mpr hi)
    · exact hz₂ (mem_cutRowSupport_iff.mpr hi)
    · exact hz₃ (mem_cutRowSupport_iff.mpr hi)
  refine ⟨edgeOfDistinct i z hiz, ?_, ?_, ?_, ?_⟩
  · exact cutBit_edgeOfDistinct_eq_decide hiz hz₀
  · exact cutBit_edgeOfDistinct_eq_decide hiz hz₁
  · exact cutBit_edgeOfDistinct_eq_decide hiz hz₂
  · exact cutBit_edgeOfDistinct_eq_decide hiz hz₃

/--
Four distinct singleton-cut rows cannot form an affine plane: some edge
coordinate sees an odd number of them.  Equivalently, their pointwise xor is
not the zero row.
-/
theorem cutRows_four_distinct_xor_nonzero {m : ℕ} (hm : 4 < m)
    {r₀ r₁ r₂ r₃ : CutRow m}
    (h₀₁ : r₀ ≠ r₁) (h₀₂ : r₀ ≠ r₂) (h₀₃ : r₀ ≠ r₃)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (_h₂₃ : r₂ ≠ r₃) :
    ∃ e : KEdge m,
      (((cutBit r₀ e ^^ cutBit r₁ e) ^^ cutBit r₂ e) ^^ cutBit r₃ e) = true := by
  classical
  cases r₀ with
  | some i =>
      rcases exists_edge_cutBit_eq_selected hm (some i) r₁ r₂ r₃ (i := i) (Or.inl rfl)
        with ⟨e, h₀, h₁, h₂, h₃⟩
      have hn₁ : r₁ ≠ some i := by intro h; exact h₀₁ h.symm
      have hn₂ : r₂ ≠ some i := by intro h; exact h₀₂ h.symm
      have hn₃ : r₃ ≠ some i := by intro h; exact h₀₃ h.symm
      refine ⟨e, ?_⟩
      simp [h₀, h₁, h₂, h₃, hn₁, hn₂, hn₃]
  | none =>
      cases r₁ with
      | some i =>
          rcases exists_edge_cutBit_eq_selected hm none (some i) r₂ r₃ (i := i)
              (Or.inr (Or.inl rfl)) with ⟨e, h₀, h₁, h₂, h₃⟩
          have hn₂ : r₂ ≠ some i := by intro h; exact h₁₂ h.symm
          have hn₃ : r₃ ≠ some i := by intro h; exact h₁₃ h.symm
          refine ⟨e, ?_⟩
          simp [h₀, h₁, h₂, h₃, hn₂, hn₃]
      | none =>
          exact False.elim (h₀₁ rfl)

/-- Four singleton-cut rows form an affine plane when they are distinct and sum to zero. -/
def IsCutAffinePlane {m : ℕ} (r₀ r₁ r₂ r₃ : CutRow m) : Prop :=
  r₀ ≠ r₁ ∧ r₀ ≠ r₂ ∧ r₀ ≠ r₃ ∧ r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ ∧
    ∀ e : KEdge m,
      (((cutBit r₀ e ^^ cutBit r₁ e) ^^ cutBit r₂ e) ^^ cutBit r₃ e) = false

/-- Formal affine-plane obstruction behind part (iv) of `thm:singleton-cut`. -/
theorem no_cut_affine_plane {m : ℕ} (hm : 4 < m) (r₀ r₁ r₂ r₃ : CutRow m) :
    ¬ IsCutAffinePlane r₀ r₁ r₂ r₃ := by
  rintro ⟨h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃, hzero⟩
  rcases cutRows_four_distinct_xor_nonzero hm h₀₁ h₀₂ h₀₃ h₁₂ h₁₃ h₂₃ with ⟨e, he⟩
  rw [hzero e] at he
  contradiction

/-- A ladder pattern in the singleton-cut parity matrix. -/
def IsCutLadder {m k : ℕ} (row : Fin k → CutRow m) (col : Fin k → KEdge m) : Prop :=
  ∀ i j : Fin k, cutBit (row i) (col j) = true ↔ i ≤ j

/-- The two-bit projection of all singleton-cut rows to two edge coordinates. -/
def cutProjection {m : ℕ} (e f : KEdge m) : Set (Bool × Bool) :=
  {p | ∃ r : CutRow m, (cutBit r e, cutBit r f) = p}

/-- Two ordered edge coordinates are endpoint-disjoint. -/
def KEdge.Disjoint {m : ℕ} (e f : KEdge m) : Prop :=
  e.left ≠ f.left ∧ e.left ≠ f.right ∧ e.right ≠ f.left ∧ e.right ≠ f.right

theorem cutProjection_disjoint {m : ℕ} {e f : KEdge m} (hdisj : e.Disjoint f) :
    cutProjection e f = {(false, false), (true, false), (false, true)} := by
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    cases hce : cutBit r e <;> cases hcf : cutBit r f
    · simp
    · simp
    · simp
    · exfalso
      rcases (cutBit_eq_true_iff r e).mp hce with hre | hre <;>
        rcases (cutBit_eq_true_iff r f).mp hcf with hrf | hrf
      · exact hdisj.1 (Option.some.inj (hre.symm.trans hrf))
      · exact hdisj.2.1 (Option.some.inj (hre.symm.trans hrf))
      · exact hdisj.2.2.1 (Option.some.inj (hre.symm.trans hrf))
      · exact hdisj.2.2.2 (Option.some.inj (hre.symm.trans hrf))
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨none, by simp [cutBit]⟩
    · refine ⟨some e.left, ?_⟩
      have hf : cutBit (some e.left : CutRow m) f = false := by
        have hnot : ¬(e.left = f.left ∨ e.left = f.right) := by
          intro h
          rcases h with h | h
          · exact hdisj.1 h
          · exact hdisj.2.1 h
        simp [cutBit, hnot]
      simp [cutBit_some_eq_true, hf]
    · refine ⟨some f.left, ?_⟩
      have he : cutBit (some f.left : CutRow m) e = false := by
        have hnot : ¬(f.left = e.left ∨ f.left = e.right) := by
          intro h
          rcases h with h | h
          · exact hdisj.1 h.symm
          · exact hdisj.2.2.1 h.symm
        simp [cutBit, hnot]
      simp [cutBit_some_eq_true, he]

/--
If two distinct ordered edge coordinates share their left endpoint and have
different right endpoints, their singleton-cut projection realizes all four
two-bit patterns.  Other shared-endpoint cases follow by relabeling the ordered
coordinates.
-/
theorem cutProjection_shared_left {m : ℕ} {e f : KEdge m}
    (hleft : e.left = f.left) (hright : e.right ≠ f.right) :
    cutProjection e f = Set.univ := by
  ext p
  constructor
  · intro _hp
    trivial
  · intro _hp
    rcases p with ⟨b₁, b₂⟩
    cases b₁ <;> cases b₂
    · exact ⟨none, by simp [cutBit]⟩
    · refine ⟨some f.right, ?_⟩
      have he : cutBit (some f.right : CutRow m) e = false := by
        have hnot : ¬(f.right = e.left ∨ f.right = e.right) := by
          intro h
          rcases h with h | h
          · exact f.left_ne_right (hleft.symm.trans h.symm)
          · exact hright (h.symm)
        simp [cutBit, hnot]
      simp [cutBit_some_eq_true, he]
    · refine ⟨some e.right, ?_⟩
      have hf : cutBit (some e.right : CutRow m) f = false := by
        have hnot : ¬(e.right = f.left ∨ e.right = f.right) := by
          intro h
          rcases h with h | h
          · exact e.left_ne_right (hleft.trans h.symm)
          · exact hright h
        simp [cutBit, hnot]
      simp [cutBit_some_eq_true, hf]
    · refine ⟨some e.left, ?_⟩
      simp [cutBit_some_eq_true, hleft]

lemma IsCutLadder.row_injective {m k : ℕ} {row : Fin k → CutRow m} {col : Fin k → KEdge m}
    (h : IsCutLadder row col) : Function.Injective row := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have htrue : cutBit (row a) (col a) = true := (h a a).2 le_rfl
    have hfalse : cutBit (row b) (col a) ≠ true := by
      intro hb
      have hle : b ≤ a := (h b a).1 hb
      exact (not_le_of_gt hlt) hle
    rw [hab] at htrue
    exact hfalse htrue
  · have htrue : cutBit (row b) (col b) = true := (h b b).2 le_rfl
    have hfalse : cutBit (row a) (col b) ≠ true := by
      intro ha
      have hle : a ≤ b := (h a b).1 ha
      exact (not_le_of_gt hgt) hle
    rw [← hab] at htrue
    exact hfalse htrue

/--
Formal part (v) of `thm:singleton-cut`: every edge-column is supported on the
two singleton rows at its endpoints, so no ladder has size three.
-/
theorem cut_ladder_size_le_two {m k : ℕ}
    {row : Fin k → CutRow m} {col : Fin k → KEdge m}
    (h : IsCutLadder row col) : k ≤ 2 := by
  by_contra hknot
  have hk : 2 < k := Nat.lt_of_not_ge hknot
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  let i₂ : Fin k := ⟨2, by omega⟩
  let jlast : Fin k := ⟨k - 1, by omega⟩
  let e : KEdge m := col jlast
  have hlast₀ : i₀ ≤ jlast := by
    change (0 : ℕ) ≤ k - 1
    omega
  have hlast₁ : i₁ ≤ jlast := by
    change (1 : ℕ) ≤ k - 1
    omega
  have hlast₂ : i₂ ≤ jlast := by
    change (2 : ℕ) ≤ k - 1
    omega
  have hr₀ : row i₀ = some e.left ∨ row i₀ = some e.right := by
    exact (cutBit_eq_true_iff (row i₀) e).mp ((h i₀ jlast).2 hlast₀)
  have hr₁ : row i₁ = some e.left ∨ row i₁ = some e.right := by
    exact (cutBit_eq_true_iff (row i₁) e).mp ((h i₁ jlast).2 hlast₁)
  have hr₂ : row i₂ = some e.left ∨ row i₂ = some e.right := by
    exact (cutBit_eq_true_iff (row i₂) e).mp ((h i₂ jlast).2 hlast₂)
  have hinj := h.row_injective
  have h01 : i₀ ≠ i₁ := by
    intro hEq
    have := congrArg Fin.val hEq
    norm_num [i₀, i₁] at this
  have h02 : i₀ ≠ i₂ := by
    intro hEq
    have := congrArg Fin.val hEq
    norm_num [i₀, i₂] at this
  have h12 : i₁ ≠ i₂ := by
    intro hEq
    have := congrArg Fin.val hEq
    norm_num [i₁, i₂] at this
  rcases hr₀ with h₀ | h₀ <;> rcases hr₁ with h₁ | h₁ <;> rcases hr₂ with h₂ | h₂
  · exact h01 (hinj (by rw [h₀, h₁]))
  · exact h01 (hinj (by rw [h₀, h₁]))
  · exact h02 (hinj (by rw [h₀, h₂]))
  · exact h12 (hinj (by rw [h₁, h₂]))
  · exact h12 (hinj (by rw [h₁, h₂]))
  · exact h02 (hinj (by rw [h₀, h₂]))
  · exact h01 (hinj (by rw [h₀, h₁]))
  · exact h01 (hinj (by rw [h₀, h₁]))

end Erdos61
