import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Vertex substitution infrastructure

This file formalizes the graph construction and homogeneous-set mechanism used
in `lem:substitution`.  The substituted side is a homogeneous set, and the
preimage of a homogeneous set under an induced embedding is homogeneous.
-/

namespace Erdos61

/--
A set of vertices is homogeneous if every outside vertex is either complete or
anticomplete to it.
-/
def HomogeneousSet {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∀ v, v ∉ X →
    (∀ x, x ∈ X → G.Adj v x) ∨
      ∀ x, x ∈ X → ¬ G.Adj v x

/-- An induced-embedding preimage of a homogeneous set is homogeneous. -/
theorem HomogeneousSet.preimage_embedding
    {VH VG : Type*} {H : SimpleGraph VH} {G : SimpleGraph VG}
    {X : Set VG} (φ : H ↪g G) (hX : HomogeneousSet G X) :
    HomogeneousSet H {v | φ v ∈ X} := by
  intro v hv
  rcases hX (φ v) hv with hcomplete | hanti
  · left
    intro x hx
    exact (φ.map_adj_iff).mp (hcomplete (φ x) hx)
  · right
    intro x hx hvx
    exact hanti (φ x) hx ((φ.map_adj_iff).mpr hvx)

/-- Vertex type obtained by replacing `p : V₀` by a copy of `V₁`. -/
abbrev SubstitutionVertex (V₀ V₁ : Type*) (p : V₀) : Type _ :=
  Sum {v : V₀ // v ≠ p} V₁

/-- Raw directed relation for substituting `G₁` into `G₀` at `p`. -/
def substituteVertexRel {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀) :
    SubstitutionVertex V₀ V₁ p → SubstitutionVertex V₀ V₁ p → Prop
  | Sum.inl x, Sum.inl y => G₀.Adj x.1 y.1
  | Sum.inr x, Sum.inr y => G₁.Adj x y
  | Sum.inl x, Sum.inr _ => G₀.Adj x.1 p
  | Sum.inr _, Sum.inl _ => False

/--
The graph obtained from `G₀` by substituting `G₁` for the vertex `p`.
Vertices outside the substituted copy keep their `G₀` adjacencies, the new copy
has graph `G₁`, and every vertex in the copy has the old neighborhood of `p`.
-/
def substituteVertex {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀) :
    SimpleGraph (SubstitutionVertex V₀ V₁ p) :=
  SimpleGraph.fromRel (substituteVertexRel G₀ G₁ p)

@[simp] theorem substituteVertex_adj_left_left {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀)
    (x y : {v : V₀ // v ≠ p}) :
    (substituteVertex G₀ G₁ p).Adj (Sum.inl x : SubstitutionVertex V₀ V₁ p)
      (Sum.inl y) ↔ G₀.Adj x.1 y.1 := by
  constructor
  · intro h
    rcases (SimpleGraph.fromRel_adj (substituteVertexRel G₀ G₁ p)
        (Sum.inl x : SubstitutionVertex V₀ V₁ p) (Sum.inl y)).mp h with
      ⟨_hne, hrel | hrel⟩
    · exact hrel
    · exact hrel.symm
  · intro h
    exact (SimpleGraph.fromRel_adj (substituteVertexRel G₀ G₁ p)
        (Sum.inl x : SubstitutionVertex V₀ V₁ p) (Sum.inl y)).mpr
      ⟨by
        intro hxy
        injection hxy with hsub
        exact h.ne (congrArg Subtype.val hsub), Or.inl h⟩

@[simp] theorem substituteVertex_adj_right_right {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀)
    (x y : V₁) :
    (substituteVertex G₀ G₁ p).Adj (Sum.inr x : SubstitutionVertex V₀ V₁ p)
      (Sum.inr y) ↔ G₁.Adj x y := by
  constructor
  · intro h
    rcases (SimpleGraph.fromRel_adj (substituteVertexRel G₀ G₁ p)
        (Sum.inr x : SubstitutionVertex V₀ V₁ p) (Sum.inr y)).mp h with
      ⟨_hne, hrel | hrel⟩
    · exact hrel
    · exact hrel.symm
  · intro h
    exact (SimpleGraph.fromRel_adj (substituteVertexRel G₀ G₁ p)
        (Sum.inr x : SubstitutionVertex V₀ V₁ p) (Sum.inr y)).mpr
      ⟨by simp [h.ne], Or.inl h⟩

@[simp] theorem substituteVertex_adj_left_right {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀)
    (x : {v : V₀ // v ≠ p}) (y : V₁) :
    (substituteVertex G₀ G₁ p).Adj (Sum.inl x : SubstitutionVertex V₀ V₁ p)
      (Sum.inr y) ↔ G₀.Adj x.1 p := by
  simp [substituteVertex, substituteVertexRel, SimpleGraph.fromRel_adj]

@[simp] theorem substituteVertex_adj_right_left {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀)
    (x : V₁) (y : {v : V₀ // v ≠ p}) :
    (substituteVertex G₀ G₁ p).Adj (Sum.inr x : SubstitutionVertex V₀ V₁ p)
      (Sum.inl y) ↔ G₀.Adj y.1 p := by
  rw [(substituteVertex G₀ G₁ p).adj_comm]
  simp

/-- The substituted copy as a vertex set. -/
def substitutedPart {V₀ V₁ : Type*} (p : V₀) :
    Set (SubstitutionVertex V₀ V₁ p) :=
  Set.range Sum.inr

/-- The substituted copy is homogeneous in the substitution graph. -/
theorem substitutedPart_homogeneous {V₀ V₁ : Type*}
    (G₀ : SimpleGraph V₀) (G₁ : SimpleGraph V₁) (p : V₀) :
    HomogeneousSet (substituteVertex G₀ G₁ p) (substitutedPart (V₁ := V₁) p) := by
  intro v hv
  cases v with
  | inl x =>
      by_cases hx : G₀.Adj x.1 p
      · left
        intro y hy
        rcases hy with ⟨z, rfl⟩
        simp [hx]
      · right
        intro y hy hxy
        rcases hy with ⟨z, rfl⟩
        exact hx ((substituteVertex_adj_left_right G₀ G₁ p x z).mp hxy)
  | inr y =>
      exact (hv ⟨y, rfl⟩).elim

/--
If an induced copy of `H` in a substitution graph uses at least two vertices
from the substituted part and at least one vertex outside it, then `H` has a
nontrivial homogeneous set.  This is the key obstruction used in the
substitution lemma for prime forbidden graphs.
-/
theorem induced_copy_mixed_substitution_side_gives_homogeneous_set
    {VH V₀ V₁ : Type*} {H : SimpleGraph VH}
    {G₀ : SimpleGraph V₀} {G₁ : SimpleGraph V₁} {p : V₀}
    (φ : H ↪g substituteVertex G₀ G₁ p)
    {a b c : VH} {y₁ y₂ : V₁} {x : {v : V₀ // v ≠ p}}
    (ha : φ a = (Sum.inr y₁ : SubstitutionVertex V₀ V₁ p))
    (hb : φ b = (Sum.inr y₂ : SubstitutionVertex V₀ V₁ p))
    (hab : a ≠ b)
    (hc : φ c = (Sum.inl x : SubstitutionVertex V₀ V₁ p)) :
    ∃ X : Set VH,
      HomogeneousSet H X ∧ a ∈ X ∧ b ∈ X ∧ a ≠ b ∧ c ∉ X := by
  let X : Set VH := {v | φ v ∈ substitutedPart (V₁ := V₁) p}
  refine ⟨X, ?_, ?_, ?_, hab, ?_⟩
  · exact (substitutedPart_homogeneous G₀ G₁ p).preimage_embedding φ
  · exact ⟨y₁, ha.symm⟩
  · exact ⟨y₂, hb.symm⟩
  · intro hcX
    rcases hcX with ⟨z, hz⟩
    rw [hc] at hz
    simp at hz

/-- A graph is induced-`H`-free. -/
def InducedFree {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG) : Prop :=
  ¬ SimpleGraph.IsIndContained H G

/--
A graph is prime in the finite homogeneous-set sense used by the paper: every
homogeneous set is empty, a singleton, or the whole vertex set.
-/
def PrimeGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ X : Set V, HomogeneousSet G X →
    (∀ v, v ∉ X) ∨ (∃ a, X = {a}) ∨ ∀ v, v ∈ X

/--
If an induced copy in a substitution graph lies in the substituted side, it
gives a copy in `G₁`.
-/
theorem isIndContained_right_of_substitution_embedding
    {VH V₀ V₁ : Type*} {H : SimpleGraph VH}
    {G₀ : SimpleGraph V₀} {G₁ : SimpleGraph V₁} {p : V₀}
    (φ : H ↪g substituteVertex G₀ G₁ p)
    (hall : ∀ v : VH, φ v ∈ substitutedPart (V₁ := V₁) p) :
    SimpleGraph.IsIndContained H G₁ := by
  classical
  let f : VH → V₁ := fun v => Classical.choose (hall v)
  have hf : ∀ v, φ v = (Sum.inr (f v) : SubstitutionVertex V₀ V₁ p) := by
    intro v
    exact (Classical.choose_spec (hall v)).symm
  refine ⟨{
    toFun := f
    inj' := ?_
    map_rel_iff' := ?_
  }⟩
  · intro u v huv
    apply (RelEmbedding.inj φ).mp
    rw [hf u, hf v, huv]
  · intro u v
    rw [← φ.map_adj_iff, hf u, hf v]
    simp

/--
If an induced copy in a substitution graph avoids the substituted side, it
gives a copy in `G₀`.
-/
theorem isIndContained_left_of_substitution_embedding
    {VH V₀ V₁ : Type*} {H : SimpleGraph VH}
    {G₀ : SimpleGraph V₀} {G₁ : SimpleGraph V₁} {p : V₀}
    (φ : H ↪g substituteVertex G₀ G₁ p)
    (hleft : ∀ v : VH, ∃ x : {v : V₀ // v ≠ p},
      φ v = (Sum.inl x : SubstitutionVertex V₀ V₁ p)) :
    SimpleGraph.IsIndContained H G₀ := by
  classical
  let left : VH → {v : V₀ // v ≠ p} := fun v => Classical.choose (hleft v)
  let f : VH → V₀ := fun v => (left v).1
  have hf : ∀ v, φ v = (Sum.inl (left v) : SubstitutionVertex V₀ V₁ p) := by
    intro v
    exact Classical.choose_spec (hleft v)
  refine ⟨{
    toFun := f
    inj' := ?_
    map_rel_iff' := ?_
  }⟩
  · intro u v huv
    apply (RelEmbedding.inj φ).mp
    have hleft_eq : left u = left v := Subtype.ext huv
    rw [hf u, hf v, hleft_eq]
  · intro u v
    rw [← φ.map_adj_iff, hf u, hf v]
    simp [f]

/--
If an induced copy in a substitution graph meets the substituted side in exactly
one vertex, contracting that vertex back to `p` gives a copy in `G₀`.
-/
theorem isIndContained_base_of_substitution_embedding_singleton
    {VH V₀ V₁ : Type*} {H : SimpleGraph VH}
    {G₀ : SimpleGraph V₀} {G₁ : SimpleGraph V₁} {p : V₀}
    (φ : H ↪g substituteVertex G₀ G₁ p) (a : VH)
    (ha : φ a ∈ substitutedPart (V₁ := V₁) p)
    (hleft : ∀ v : VH, v ≠ a → ∃ x : {v : V₀ // v ≠ p},
      φ v = (Sum.inl x : SubstitutionVertex V₀ V₁ p)) :
    SimpleGraph.IsIndContained H G₀ := by
  classical
  let y : V₁ := Classical.choose ha
  have hφa : φ a = (Sum.inr y : SubstitutionVertex V₀ V₁ p) :=
    (Classical.choose_spec ha).symm
  let left : (v : VH) → v ≠ a → {v : V₀ // v ≠ p} :=
    fun v hv => Classical.choose (hleft v hv)
  have hφleft : ∀ (v : VH) (hv : v ≠ a),
      φ v = (Sum.inl (left v hv) : SubstitutionVertex V₀ V₁ p) := by
    intro v hv
    exact Classical.choose_spec (hleft v hv)
  let f : VH → V₀ := fun v => if hv : v = a then p else (left v hv).1
  have fa : f a = p := by simp [f]
  have fleft : ∀ (v : VH) (hv : v ≠ a), f v = (left v hv).1 := by
    intro v hv
    simp [f, hv]
  refine ⟨{
    toFun := f
    inj' := ?_
    map_rel_iff' := ?_
  }⟩
  · intro u v huv
    by_cases hu : u = a
    · subst u
      by_cases hv : v = a
      · exact hv.symm
      · have hp : p = (left v hv).1 := by
          simpa [fa, fleft v hv] using huv
        exact False.elim ((left v hv).2 hp.symm)
    · by_cases hv : v = a
      · subst v
        have hp : (left u hu).1 = p := by
          simpa [fa, fleft u hu] using huv
        exact False.elim ((left u hu).2 hp)
      · apply (RelEmbedding.inj φ).mp
        have hleft_eq : left u hu = left v hv := by
          apply Subtype.ext
          simpa [fleft u hu, fleft v hv] using huv
        rw [hφleft u hu, hφleft v hv, hleft_eq]
  · intro u v
    change G₀.Adj (f u) (f v) ↔ H.Adj u v
    by_cases hu : u = a
    · subst u
      by_cases hv : v = a
      · subst v
        simp [fa]
      · rw [fa, fleft v hv, G₀.adj_comm]
        rw [← substituteVertex_adj_right_left G₀ G₁ p y (left v hv)]
        rw [← hφa, ← hφleft v hv]
        exact φ.map_adj_iff
    · by_cases hv : v = a
      · subst v
        rw [fleft u hu, fa]
        rw [← substituteVertex_adj_left_right G₀ G₁ p (left u hu) y]
        rw [← hφleft u hu, ← hφa]
        exact φ.map_adj_iff
      · rw [fleft u hu, fleft v hv]
        rw [← substituteVertex_adj_left_left G₀ G₁ p (left u hu) (left v hv)]
        rw [← hφleft u hu, ← hφleft v hv]
        exact φ.map_adj_iff

/--
Formal version of `lem:substitution` for the local definitions in this folder:
substituting an `H`-free graph into a vertex of another `H`-free graph remains
`H`-free when `H` is prime.
-/
theorem substituteVertex_inducedFree_of_prime
    {VH V₀ V₁ : Type*} {H : SimpleGraph VH}
    {G₀ : SimpleGraph V₀} {G₁ : SimpleGraph V₁} {p : V₀}
    (hprime : PrimeGraph H)
    (hG₀ : InducedFree H G₀) (hG₁ : InducedFree H G₁) :
    InducedFree H (substituteVertex G₀ G₁ p) := by
  classical
  intro hcopy
  rcases hcopy with ⟨φ⟩
  let X : Set VH := {v | φ v ∈ substitutedPart (V₁ := V₁) p}
  have hXhom : HomogeneousSet H X :=
    (substitutedPart_homogeneous G₀ G₁ p).preimage_embedding φ
  rcases hprime X hXhom with hnone | hsingleton | hall
  · apply hG₀
    exact isIndContained_left_of_substitution_embedding φ (by
      intro v
      cases hφv : φ v with
      | inl x =>
          exact ⟨x, rfl⟩
      | inr y =>
          exact False.elim (hnone v ⟨y, hφv.symm⟩))
  · rcases hsingleton with ⟨a, hXa⟩
    apply hG₀
    refine isIndContained_base_of_substitution_embedding_singleton φ a ?_ ?_
    · change a ∈ X
      rw [hXa]
      simp
    · intro v hv
      cases hφv : φ v with
      | inl x =>
          exact ⟨x, rfl⟩
      | inr y =>
          have hvX : v ∈ X := ⟨y, hφv.symm⟩
          have hva : v = a := by simpa [hXa] using hvX
          exact False.elim (hv hva)
  · apply hG₁
    exact isIndContained_right_of_substitution_embedding φ hall

end Erdos61
