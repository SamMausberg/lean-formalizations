import FormalConjectures.Problems.Erdos.E20.Families.TransversalCounterexample
import FormalConjectures.Problems.Erdos.E20.Kernels.LeafStripping

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

section FullBlockProduct

variable {q : ℕ}

/-- The full `q`-ary code on `r` coordinates.  This is the code underlying the block-product
family `𝓑_{r,q}` from the user's leafless-core note. -/
def fullCode (r q : ℕ) : Finset (Fin r → Fin q) :=
  Finset.univ

/-- The full block-product family on `r` blocks of size `q`: every transversal chooses one vertex
from each block.  Formally this is just the transversal family of the full `q`-ary code. -/
def blockProductFamily (r q : ℕ) : Finset (Finset (Fin r × Fin q)) :=
  transversalFamily (G := Fin q) (fullCode r q)

@[simp] theorem card_fullCode (r q : ℕ) :
    (fullCode r q).card = q ^ r := by
  simp [fullCode, Fintype.card_fun]

@[simp] theorem card_blockProductFamily (r q : ℕ) :
    (blockProductFamily r q).card = q ^ r := by
  simp [blockProductFamily, fullCode, Fintype.card_fun]

/-- Fixing one coordinate of the full `q`-ary code leaves exactly `q^n` possibilities for the
remaining coordinates. -/
noncomputable def fullCodeCoordinateFiberEquiv (q n : ℕ) (i : Fin (n + 1)) (a : Fin q) :
    ↥({x ∈ fullCode (n + 1) q | x i = a}) ≃ (Fin n → Fin q) where
  toFun x := i.removeNth x.1
  invFun y := ⟨i.insertNth a y, by simp [fullCode]⟩
  left_inv x := by
    rcases Finset.mem_filter.mp x.2 with ⟨_, hxi⟩
    apply Subtype.ext
    calc
      i.insertNth a (i.removeNth x.1) = i.insertNth (x.1 i) (i.removeNth x.1) := by simp [hxi]
      _ = x.1 := by simpa using (Fin.insertNth_self_removeNth i x.1)
  right_inv y := by
    simp

@[simp] theorem card_fullCode_coordinateFiber (q n : ℕ) (i : Fin (n + 1)) (a : Fin q) :
    ({x ∈ fullCode (n + 1) q | x i = a}).card = q ^ n := by
  classical
  rw [← Fintype.card_coe ({x ∈ fullCode (n + 1) q | x i = a})]
  simpa using Fintype.card_congr (fullCodeCoordinateFiberEquiv q n i a)

@[simp] theorem coordinateCount_fullCode (q n : ℕ) (i : Fin (n + 1)) (a : Fin q) :
    coordinateCount (G := Fin q) (fullCode (n + 1) q) i a = q ^ n := by
  unfold coordinateCount fullCode
  simpa [fullCode] using card_fullCode_coordinateFiber q n i a

/-- In every transversal family, the degree of vertex `(i,a)` is exactly the number of codewords
with `i`-th coordinate equal to `a`. -/
theorem vertexDegree_transversalFamily_eq_coordinateCount
    {G : Type*} [DecidableEq G] [Fintype G]
    {r : ℕ} (C : Finset (Fin r → G)) (i : Fin r) (a : G) :
    vertexDegree' (transversalFamily (G := G) C) (i, a) = coordinateCount C i a := by
  classical
  have hfilter :
      (transversalFamily (G := G) C).filter (fun e => (i, a) ∈ e) =
        (C.filter fun x => x i = a).image transversalEdge := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨heC, hea⟩
      rcases Finset.mem_image.mp heC with ⟨x, hxC, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxC, (mem_transversalEdge_iff.mp hea)⟩, rfl⟩
    · intro he
      rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩,
          by simpa [mem_transversalEdge_iff] using (Finset.mem_filter.mp hx).2⟩
  unfold vertexDegree' coordinateCount
  calc
    ((transversalFamily (G := G) C).filter (fun e => (i, a) ∈ e)).card
        = ((C.filter fun x => x i = a).image transversalEdge).card := by rw [hfilter]
    _ = (C.filter fun x => x i = a).card := by
          exact Finset.card_image_of_injective _ transversalEdge_injective

/-- Every vertex in the full block-product family has degree `q^(r-1)`. -/
theorem vertexDegree_blockProductFamily (r q : ℕ) (i : Fin r) (a : Fin q) :
    vertexDegree' (blockProductFamily r q) (i, a) = q ^ (r - 1) := by
  cases r with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      rw [Nat.succ_sub_one]
      rw [blockProductFamily, vertexDegree_transversalFamily_eq_coordinateCount]
      simpa [fullCode] using coordinateCount_fullCode q n i a

/-- The full block-product family is `k`-sunflower-free whenever the block width `q` is smaller
than `k`.  This is exactly the user's leafless-core product family `𝓑_{n,k}` with `q = k - 1`. -/
theorem blockProductFamily_sunflowerFree
    (r q k : ℕ) (hk : 2 ≤ k) (hqk : q < k) :
    SunflowerFree (blockProductFamily r q) k := by
  simpa [blockProductFamily, fullCode] using
    (transversalFamily_sunflowerFree_of_card_lt
      (G := Fin q) (C := fullCode r q) hk (by simpa using hqk))

/-- Once there are at least `2` blocks and each block has size at least `2`, every vertex of the
block-product family survives leaf stripping. -/
theorem nonLeafVertices_blockProductFamily_eq_univ
    (r q : ℕ) (hr : 2 ≤ r) (hq : 2 ≤ q) :
    nonLeafVertices (blockProductFamily r q) = Finset.univ := by
  ext v
  constructor
  · intro _
    simp
  · intro _
    rcases v with ⟨i, a⟩
    have hdeg : 2 ≤ vertexDegree' (blockProductFamily r q) (i, a) := by
      rw [vertexDegree_blockProductFamily]
      cases r with
      | zero =>
          omega
      | succ n =>
          cases n with
          | zero =>
              omega
          | succ m =>
              have hqpos : 0 < q := by omega
              have hqm : 0 < q ^ m := Nat.pow_pos hqpos
              have hqle : q ≤ q ^ m * q := by
                calc
                  q = 1 * q := by simp
                  _ ≤ q ^ m * q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hqm)
              calc
                2 ≤ q := hq
                _ ≤ q ^ m * q := hqle
                _ = q ^ (m + 1) := by rw [pow_succ]
    simpa [nonLeafVertices] using hdeg

@[simp] theorem strippedEdge_blockProductFamily
    (r q : ℕ) (hr : 2 ≤ r) (hq : 2 ≤ q) (e : Finset (Fin r × Fin q)) :
    strippedEdge (blockProductFamily r q) e = e := by
  rw [strippedEdge, nonLeafVertices_blockProductFamily_eq_univ r q hr hq]
  simp

/-- In the leafless regime `r,q ≥ 2`, one stripping round leaves the full block-product family
unchanged. -/
theorem strippedSupport_blockProductFamily_eq
    (r q : ℕ) (hr : 2 ≤ r) (hq : 2 ≤ q) :
    strippedSupportFamily (blockProductFamily r q) = blockProductFamily r q := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, hfe⟩
    have hfe' : f = e := by
      simpa [strippedEdge_blockProductFamily r q hr hq f] using hfe
    have hef : e = f := hfe'.symm
    simpa [hef] using hf
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, strippedEdge_blockProductFamily r q hr hq e⟩

end FullBlockProduct

section TaggedProducts

variable {β : Type*} [DecidableEq β] [Fintype β]

/-- A tagged product edge: on each row `i`, keep the local set `x i` and tag its vertices by the
row index.  This is the set-family version of taking a direct product of local hypergraphs. -/
def taggedEdge {r : ℕ} (x : Fin r → Finset β) : Finset (Fin r × β) :=
  Finset.univ.biUnion fun i => (x i).image fun a => (i, a)

@[simp] theorem mem_taggedEdge_iff {r : ℕ} {x : Fin r → Finset β} {i : Fin r} {a : β} :
    (i, a) ∈ taggedEdge x ↔ a ∈ x i := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨j, -, hj⟩
    rcases Finset.mem_image.mp hj with ⟨b, hb, hpair⟩
    have hij : j = i := by simpa using congrArg Prod.fst hpair
    subst hij
    have hba : b = a := by simpa using congrArg Prod.snd hpair
    simpa [hba] using hb
  · intro h
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨a, h, rfl⟩⟩

theorem taggedEdge_injective {r : ℕ} :
    Function.Injective (fun x : Fin r → Finset β => taggedEdge x) := by
  intro x y hxy
  funext i
  ext a
  constructor
  · intro ha
    have htag : (i, a) ∈ taggedEdge x := by simpa [mem_taggedEdge_iff] using ha
    have : (i, a) ∈ taggedEdge y := by simpa [hxy] using htag
    simpa [mem_taggedEdge_iff] using this
  · intro ha
    have htag : (i, a) ∈ taggedEdge y := by simpa [mem_taggedEdge_iff] using ha
    have : (i, a) ∈ taggedEdge x := by simpa [hxy] using htag
    simpa [mem_taggedEdge_iff] using this

/-- The slice of a tagged vertex set on row `i`, forgetting the row tag. -/
def rowSlice {r : ℕ} (Q : Finset (Fin r × β)) (i : Fin r) : Finset β :=
  (Q.filter fun p => p.1 = i).image Prod.snd

@[simp] theorem mem_rowSlice_iff {r : ℕ} {Q : Finset (Fin r × β)} {i : Fin r} {a : β} :
    a ∈ rowSlice Q i ↔ (i, a) ∈ Q := by
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨p, hp, hpa⟩
    have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
    have hpa' : p.2 = a := by simpa using hpa
    rcases p with ⟨j, b⟩
    simp at hpi hpa'
    subst hpi
    subst hpa'
    exact (Finset.mem_filter.mp hp).1
  · intro ha
    exact Finset.mem_image.mpr
      ⟨(i, a), Finset.mem_filter.mpr ⟨ha, rfl⟩, rfl⟩

/-- Full tagged-product family on `r` rows built from a local family `D`.  A global edge chooses
one local edge from `D` in each row and tags the resulting union by the row index. -/
def taggedProductFamily (D : Finset (Finset β)) (r : ℕ) : Finset (Finset (Fin r × β)) :=
  (Finset.univ : Finset (Fin r → ↥D)).image fun x =>
    taggedEdge fun i => ((x i : ↥D) : Finset β)

theorem mem_taggedProductFamily_iff {D : Finset (Finset β)} {r : ℕ} {x : Fin r → Finset β} :
    taggedEdge x ∈ taggedProductFamily D r ↔ ∀ i, x i ∈ D := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, -, hy⟩
    have hxy : x = fun i => ((y i : ↥D) : Finset β) := taggedEdge_injective hy.symm
    intro i
    rw [hxy]
    exact (y i).2
  · intro hx
    refine Finset.mem_image.mpr ⟨fun i => ⟨x i, hx i⟩, Finset.mem_univ _, ?_⟩
    simp

/-- The rows of a tagged edge are disjoint, so its cardinality is the sum of the row sizes. -/
@[simp] theorem card_taggedEdge {r : ℕ} (x : Fin r → Finset β) :
    (taggedEdge x).card = ∑ i : Fin r, (x i).card := by
  classical
  unfold taggedEdge
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    exact Finset.card_image_of_injective _ (by
      intro a b hab
      exact congrArg Prod.snd hab)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp_i hp_j
    rcases Finset.mem_image.mp hp_i with ⟨a, ha, hpa⟩
    rcases Finset.mem_image.mp hp_j with ⟨b, hb, hpb⟩
    have : i = j := by
      rw [← hpa] at hpb
      simpa using (congrArg Prod.fst hpb).symm
    exact hij this

/-- Intersecting a tagged edge with a tagged vertex set acts rowwise. -/
@[simp] theorem taggedEdge_inter_eq {r : ℕ} (x : Fin r → Finset β) (Q : Finset (Fin r × β)) :
    taggedEdge x ∩ Q = taggedEdge (fun i => x i ∩ rowSlice Q i) := by
  ext p
  rcases p with ⟨i, a⟩
  simp [mem_taggedEdge_iff, mem_rowSlice_iff, and_left_comm, and_assoc]

/-- The cardinality of the intersection between a tagged edge and a tagged vertex set is the sum
of the rowwise intersection cardinalities. -/
@[simp] theorem card_taggedEdge_inter_eq_sum_rowSlices {r : ℕ}
    (x : Fin r → Finset β) (Q : Finset (Fin r × β)) :
    (taggedEdge x ∩ Q).card = ∑ i : Fin r, (x i ∩ rowSlice Q i).card := by
  rw [taggedEdge_inter_eq]
  simp

@[simp] theorem card_taggedProductFamily (D : Finset (Finset β)) (r : ℕ) :
    (taggedProductFamily D r).card = D.card ^ r := by
  classical
  unfold taggedProductFamily
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_fun]
  · intro x y hxy
    apply funext
    intro i
    apply Subtype.ext
    ext a
    constructor
    · intro ha
      have htag : (i, a) ∈ taggedEdge (fun j => ((x j : ↥D) : Finset β)) := by
        simpa [mem_taggedEdge_iff] using ha
      have : (i, a) ∈ taggedEdge (fun j => ((y j : ↥D) : Finset β)) := by
        simpa [hxy] using htag
      simpa [mem_taggedEdge_iff] using this
    · intro ha
      have htag : (i, a) ∈ taggedEdge (fun j => ((y j : ↥D) : Finset β)) := by
        simpa [mem_taggedEdge_iff] using ha
      have : (i, a) ∈ taggedEdge (fun j => ((x j : ↥D) : Finset β)) := by
        simpa [hxy] using htag
      simpa [mem_taggedEdge_iff] using this

/-- Fixing one coordinate to lie in a prescribed finite subset `P` leaves `|P| * |G|^n`
possibilities for the remaining coordinates. -/
noncomputable def wordMemFilterEquiv {G : Type*} [DecidableEq G] [Fintype G]
    (P : Finset G) (n : ℕ) (i : Fin (n + 1)) :
    ↥((Finset.univ : Finset (Fin (n + 1) → G)).filter fun x => x i ∈ P) ≃ P × (Fin n → G) where
  toFun x := (⟨x.1 i, by simpa using (Finset.mem_filter.mp x.2).2⟩, i.removeNth x.1)
  invFun y := ⟨i.insertNth y.1.1 y.2, by simp [y.1.2]⟩
  left_inv x := by
    apply Subtype.ext
    simpa using (Fin.insertNth_self_removeNth i x.1)
  right_inv y := by
    simp

@[simp] theorem card_words_mem_filter {G : Type*} [DecidableEq G] [Fintype G]
    (P : Finset G) (n : ℕ) (i : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin (n + 1) → G)).filter fun x => x i ∈ P).card =
      P.card * Fintype.card G ^ n := by
  classical
  rw [← Fintype.card_coe ((Finset.univ : Finset (Fin (n + 1) → G)).filter fun x => x i ∈ P)]
  simpa [Fintype.card_prod, Fintype.card_fun] using
    Fintype.card_congr (wordMemFilterEquiv P n i)

/-- In a tagged product family, the degree of `(i,a)` counts the row-choices whose `i`-th local
set contains `a`. -/
theorem vertexDegree_taggedProductFamily_eq_filterCard
    (D : Finset (Finset β)) (r : ℕ) (i : Fin r) (a : β) :
    vertexDegree' (taggedProductFamily D r) (i, a) =
      ((Finset.univ : Finset (Fin r → ↥D)).filter
        fun x => a ∈ (((x i : ↥D) : Finset β))).card := by
  classical
  have hfilter :
      (taggedProductFamily D r).filter (fun e => (i, a) ∈ e) =
        ((Finset.univ : Finset (Fin r → ↥D)).filter
          fun x => a ∈ (((x i : ↥D) : Finset β))).image
            (fun x => taggedEdge fun j => ((x j : ↥D) : Finset β)) := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨heD, hea⟩
      rcases Finset.mem_image.mp heD with ⟨x, hx, rfl⟩
      refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hx, by simpa [mem_taggedEdge_iff] using hea⟩
    · intro he
      rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩,
          by simpa [mem_taggedEdge_iff] using (Finset.mem_filter.mp hx).2⟩
  unfold vertexDegree'
  calc
    ((taggedProductFamily D r).filter (fun e => (i, a) ∈ e)).card
        = (((Finset.univ : Finset (Fin r → ↥D)).filter
            fun x => a ∈ (((x i : ↥D) : Finset β))).image
              (fun x => taggedEdge fun j => ((x j : ↥D) : Finset β))).card := by
              rw [hfilter]
    _ = ((Finset.univ : Finset (Fin r → ↥D)).filter
          fun x => a ∈ (((x i : ↥D) : Finset β))).card := by
            refine Finset.card_image_of_injective _ ?_
            intro x y hxy
            apply funext
            intro j
            apply Subtype.ext
            ext b
            constructor
            · intro hb
              have htag : (j, b) ∈ taggedEdge (fun l => ((x l : ↥D) : Finset β)) := by
                simpa [mem_taggedEdge_iff] using hb
              have : (j, b) ∈ taggedEdge (fun l => ((y l : ↥D) : Finset β)) := by
                simpa [hxy] using htag
              simpa [mem_taggedEdge_iff] using this
            · intro hb
              have htag : (j, b) ∈ taggedEdge (fun l => ((y l : ↥D) : Finset β)) := by
                simpa [mem_taggedEdge_iff] using hb
              have : (j, b) ∈ taggedEdge (fun l => ((x l : ↥D) : Finset β)) := by
                simpa [hxy] using htag
              simpa [mem_taggedEdge_iff] using this

/-- If every local `k`-sunflower tuple in `D` is constant, then the full tagged product over `D`
is `k`-sunflower-free. -/
theorem taggedProductFamily_sunflowerFree_of_local_constant
    (D : Finset (Finset β)) {r k : ℕ} (hk : 2 ≤ k)
    (hlocal :
      ∀ B : Fin k → Finset β, (∀ t, B t ∈ D) → IsSunflowerTuple B → ∀ u v, B u = B v) :
    SunflowerFree (taggedProductFamily D r) k := by
  classical
  intro A hA hInj hSun
  let t0 : Fin k := ⟨0, by omega⟩
  let t1 : Fin k := ⟨1, by omega⟩
  have ht01 : t0 ≠ t1 := by
    intro h
    have : (0 : ℕ) = 1 := by exact congrArg Fin.val h
    omega
  choose x hxMem hxAeq using fun t => Finset.mem_image.mp (hA t)
  have hrowSun :
      ∀ i : Fin r, IsSunflowerTuple (fun t : Fin k => ((x t i : ↥D) : Finset β)) := by
    intro i u v u' v' huv hu'v'
    ext b
    constructor
    · intro hb
      have htag : (i, b) ∈ A u ∩ A v := by
        rw [← hxAeq u, ← hxAeq v]
        exact Finset.mem_inter.mpr
          ⟨by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp hb).1,
            by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp hb).2⟩
      have htag' : (i, b) ∈ A u' ∩ A v' := by
        simpa [hSun huv hu'v'] using htag
      rw [← hxAeq u', ← hxAeq v'] at htag'
      exact Finset.mem_inter.mpr
        ⟨by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp htag').1,
          by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp htag').2⟩
    · intro hb
      have htag : (i, b) ∈ A u' ∩ A v' := by
        rw [← hxAeq u', ← hxAeq v']
        exact Finset.mem_inter.mpr
          ⟨by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp hb).1,
            by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp hb).2⟩
      have htag' : (i, b) ∈ A u ∩ A v := by
        simpa [hSun huv hu'v'] using htag
      rw [← hxAeq u, ← hxAeq v] at htag'
      exact Finset.mem_inter.mpr
        ⟨by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp htag').1,
          by simpa [mem_taggedEdge_iff] using (Finset.mem_inter.mp htag').2⟩
  have hrowConst :
      ∀ i : Fin r, ∀ u v : Fin k, ((x u i : ↥D) : Finset β) = ((x v i : ↥D) : Finset β) := by
    intro i
    exact hlocal (fun t => ((x t i : ↥D) : Finset β)) (fun t => (x t i).2) (hrowSun i)
  have hfunEq :
      (fun i => ((x t0 i : ↥D) : Finset β)) = fun i => ((x t1 i : ↥D) : Finset β) := by
    funext i
    exact hrowConst i t0 t1
  have hEdgeEq : A t0 = A t1 := by
    rw [← hxAeq t0, ← hxAeq t1]
    simp [hfunEq]
  exact ht01 (hInj hEdgeEq)

end TaggedProducts

section OneOutCoordinates

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The informal declaration "a genuine one-out-of-`q` coordinate is a `q`-set `Q` of vertices
such that every edge meets `Q` in exactly one point" from the pasted terminal-kernel note.

Formally we do not fix `q` in advance: the block is any nonempty finite set `Q`, and its size
enters later through the packed weight `(k - 1) / |Q|`. -/
def IsOneOutSet (H : Finset (Finset α)) (Q : Finset α) : Prop :=
  Q.Nonempty ∧ ∀ e ∈ H, (e ∩ Q).card = 1

/-- The informal declaration "pairwise disjoint genuine one-out-of-`q` blocks" from the pasted
terminal-kernel note. -/
def IsOneOutPack (H : Finset (Finset α)) (P : Finset (Finset α)) : Prop :=
  (∀ Q ∈ P, IsOneOutSet H Q) ∧ ((P : Set (Finset α)).PairwiseDisjoint id)

/-- The informal declaration "the maximum total weight `∑ (k - 1) / q` over pairwise disjoint
genuine one-out blocks" from the pasted terminal-kernel note, evaluated on one finite pack. -/
noncomputable def oneOutPackWeight (k : ℕ) (P : Finset (Finset α)) : ℚ :=
  ∑ Q ∈ P, (k - 1 : ℚ) / Q.card

/-- The informal declaration "`ρ_k(H)` is the maximum weighted packing of pairwise disjoint genuine
one-out blocks" from the pasted terminal-kernel note.

We take the maximum over all finite packs of subsets of the ambient finite ground set.  The extra
inserted `0` makes the maximum well-defined even when the only feasible pack is the empty one. -/
noncomputable def rhoOneOut (H : Finset (Finset α)) (k : ℕ) : ℚ :=
  by
    classical
    exact ({0} ∪
      (((Finset.univ : Finset α).powerset.powerset.filter (IsOneOutPack H)).image
        (oneOutPackWeight k))).max' (by simp)

/-- The empty family of blocks is always a valid one-out packing. -/
@[simp] theorem isOneOutPack_empty (H : Finset (Finset α)) :
    IsOneOutPack H ∅ := by
  constructor
  · intro Q hQ
    cases hQ
  · simpa [Set.PairwiseDisjoint]

/-- If a hypergraph has no genuine one-out block at all, then every feasible packed block family is
empty. -/
theorem isOneOutPack_eq_empty_of_no_oneOutSet
    {H : Finset (Finset α)} (hnone : ¬ ∃ Q, IsOneOutSet H Q)
    {P : Finset (Finset α)} (hP : IsOneOutPack H P) :
    P = ∅ := by
  by_contra hne
  obtain ⟨Q, hQ⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact hnone ⟨Q, hP.1 Q hQ⟩

/-- If no genuine one-out block exists, then the weighted packing parameter `ρ_k` vanishes.  This
is the formal version of the user’s statement "if there is no such block at all, then `ρ_k(H)=0`".
-/
theorem rhoOneOut_eq_zero_of_no_oneOutSet
    {H : Finset (Finset α)} {k : ℕ}
    (hnone : ¬ ∃ Q, IsOneOutSet H Q) :
    rhoOneOut H k = 0 := by
  classical
  have hpacks :
      (Finset.univ : Finset α).powerset.powerset.filter (IsOneOutPack H) = {∅} := by
    ext P
    constructor
    · intro hP
      have hpack : IsOneOutPack H P := (Finset.mem_filter.mp hP).2
      have hPempty : P = ∅ := isOneOutPack_eq_empty_of_no_oneOutSet hnone hpack
      simp [hPempty]
    · intro hP
      have hPempty : P = ∅ := by simpa using hP
      subst hPempty
      exact Finset.mem_filter.mpr ⟨by simp, isOneOutPack_empty H⟩
  have hweights :
      (((Finset.univ : Finset α).powerset.powerset.filter (IsOneOutPack H)).image
        (oneOutPackWeight k)) = {0} := by
    rw [hpacks]
    ext q
    simp [oneOutPackWeight]
  have hinsert :
      insert 0
          ((((Finset.univ : Finset α).powerset.powerset.filter (IsOneOutPack H)).image
            (oneOutPackWeight k))) = ({0} : Finset ℚ) := by
    simpa using congrArg (insert 0) hweights
  let S : Finset ℚ :=
    insert 0
      ((((Finset.univ : Finset α).powerset.powerset.filter (IsOneOutPack H)).image
        (oneOutPackWeight k)))
  have hS : S = ({0} : Finset ℚ) := by
    simpa [S] using hinsert
  have hS_nonempty : S.Nonempty := by
    simp [S]
  have hmax :
      S.max' hS_nonempty = 0 := by
    simpa [hS] using (Finset.max'_singleton (0 : ℚ))
  unfold rhoOneOut
  simpa [S] using hmax

end OneOutCoordinates

section PairTensor

/-- The local alphabet for the `K_k` tensor-product kernel: all 2-subsets of `Fin k`, i.e. the
edge set of the complete graph `K_k`. -/
def twoSubsets (k : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k)).powersetCard 2

@[simp] theorem mem_twoSubsets_iff {k : ℕ} {e : Finset (Fin k)} :
    e ∈ twoSubsets k ↔ e.card = 2 := by
  simp [twoSubsets]

@[simp] theorem card_twoSubsets (k : ℕ) :
    (twoSubsets k).card = Nat.choose k 2 := by
  simpa [twoSubsets] using Finset.card_powersetCard 2 (Finset.univ : Finset (Fin k))

/-- The global `K_k` tensor-product family from the user's kernel note: in each row one chooses an
edge of `K_k`, and the global edge is the tagged union of those row-choices. -/
def pairTensorFamily (t k : ℕ) : Finset (Finset (Fin t × Fin k)) :=
  taggedProductFamily (twoSubsets k) t

@[simp] theorem card_pairTensorFamily (t k : ℕ) :
    (pairTensorFamily t k).card = Nat.choose k 2 ^ t := by
  simpa [pairTensorFamily] using card_taggedProductFamily (D := twoSubsets k) t

theorem twoSubsetsContaining_eq_image (k : ℕ) (a : Fin k) :
    ((Finset.univ.erase a).powersetCard 1).image (fun s => insert a s) =
      (twoSubsets k).filter fun e => a ∈ e := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨s, hs, rfl⟩
    rcases Finset.mem_powersetCard.mp hs with ⟨hsSub, hsCard⟩
    have hnot : a ∉ s := by
      intro ha
      have : a ∈ Finset.univ.erase a := hsSub ha
      simpa using this
    refine Finset.mem_filter.mpr ?_
    constructor
    · rw [mem_twoSubsets_iff]
      simp [hsCard, hnot]
    · simp
  · intro he
    rcases Finset.mem_filter.mp he with ⟨he2, hea⟩
    refine Finset.mem_image.mpr ⟨e.erase a, ?_, Finset.insert_erase hea⟩
    refine Finset.mem_powersetCard.mpr ?_
    constructor
    · intro x hx
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, by simp⟩
    · have hecard : e.card = 2 := by simpa [twoSubsets] using he2
      rw [Finset.card_erase_of_mem hea]
      omega

@[simp] theorem card_twoSubsetsContaining (k : ℕ) (a : Fin k) :
    ((twoSubsets k).filter fun e => a ∈ e).card = k - 1 := by
  rw [← twoSubsetsContaining_eq_image k a]
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard]
    simp
  · intro s hs t ht hst
    have hsa : a ∉ s := by
      intro ha
      have : a ∈ Finset.univ.erase a := (Finset.mem_powersetCard.mp hs).1 ha
      simpa using this
    have hta : a ∉ t := by
      intro ha
      have : a ∈ Finset.univ.erase a := (Finset.mem_powersetCard.mp ht).1 ha
      simpa using this
    have := congrArg (fun u : Finset (Fin k) => u.erase a) hst
    simpa [hsa, hta] using this

/-- A `k`-tuple of 2-subsets of a `k`-element set whose pairwise intersections all agree must be
constant.  This is the local obstruction behind the `K_k` tensor-product family. -/
theorem twoSubsets_sunflowerTuple_constant (k : ℕ) (hk : 3 ≤ k)
    {A : Fin k → Finset (Fin k)} (hA : ∀ t, A t ∈ twoSubsets k) (hSun : IsSunflowerTuple A) :
    ∀ u v, A u = A v := by
  classical
  let t0 : Fin k := ⟨0, by omega⟩
  let t1 : Fin k := ⟨1, by omega⟩
  have ht01 : t0 ≠ t1 := by
    intro h
    have : (0 : ℕ) = 1 := by exact congrArg Fin.val h
    omega
  have hcardA : ∀ t, (A t).card = 2 := by
    intro t
    simpa using (hA t)
  let K := A t0 ∩ A t1
  have hpair : ∀ i j : Fin k, i ≠ j → A i ∩ A j = K := by
    intro i j hij
    simpa [K] using hSun hij ht01
  have hKle : K.card ≤ 2 := by
    calc
      K.card ≤ (A t0).card := by
        dsimp [K]
        exact Finset.card_le_card Finset.inter_subset_left
      _ = 2 := hcardA t0
  interval_cases hK : K.card
  · have hKempty : K = ∅ := Finset.card_eq_zero.mp hK
    have hdisj :
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint A := by
      intro i _ j _ hij
      change Disjoint (A i) (A j)
      rw [Finset.disjoint_iff_inter_eq_empty, hpair i j hij, hKempty]
    have hcardUnion :
        ((Finset.univ : Finset (Fin k)).biUnion A).card = ∑ t : Fin k, (A t).card := by
      simpa using Finset.card_biUnion hdisj
    have hsub : (Finset.univ : Finset (Fin k)).biUnion A ⊆ Finset.univ := by
      intro x hx
      simp
    have hle : ((Finset.univ : Finset (Fin k)).biUnion A).card ≤ k := by
      simpa using Finset.card_le_card hsub
    have hsum : (∑ t : Fin k, (A t).card) = k * 2 := by
      simp [hcardA]
    rw [hcardUnion, hsum] at hle
    omega
  · rcases Finset.card_eq_one.mp hK with ⟨x, hxK⟩
    have hxKmem : x ∈ K := by simpa [hxK]
    have hxmem : ∀ t : Fin k, x ∈ A t := by
      intro t
      by_cases ht : t = t0
      · subst ht
        exact (Finset.mem_inter.mp (by simpa [K] using hxKmem)).1
      · have hmem : x ∈ A t ∩ A t0 := by
          simpa [hpair t t0 ht, hxK] using hxKmem
        exact (Finset.mem_inter.mp hmem).1
    let B : Fin k → Finset (Fin k) := fun t => (A t).erase x
    have hBcard : ∀ t : Fin k, (B t).card = 1 := by
      intro t
      dsimp [B]
      rw [Finset.card_erase_of_mem (hxmem t), hcardA t]
    have hBdisj :
        ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint B := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro y hyi hyj
      have hyiA : y ∈ A i := Finset.mem_of_mem_erase hyi
      have hyjA : y ∈ A j := Finset.mem_of_mem_erase hyj
      have hyK : y ∈ K := by
        have : y ∈ A i ∩ A j := Finset.mem_inter.mpr ⟨hyiA, hyjA⟩
        simpa [hpair i j hij] using this
      have hyx : y = x := by simpa [hxK] using hyK
      exact (Finset.ne_of_mem_erase hyi) hyx
    have hcardUnion :
        ((Finset.univ : Finset (Fin k)).biUnion B).card = ∑ t : Fin k, (B t).card := by
      simpa using Finset.card_biUnion hBdisj
    have hsub : (Finset.univ : Finset (Fin k)).biUnion B ⊆ Finset.univ.erase x := by
      intro y hy
      rcases Finset.mem_biUnion.mp hy with ⟨t, -, hyt⟩
      exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hyt, by simp⟩
    have hle : ((Finset.univ : Finset (Fin k)).biUnion B).card ≤ k - 1 := by
      calc
        ((Finset.univ : Finset (Fin k)).biUnion B).card ≤ (Finset.univ.erase x).card :=
          Finset.card_le_card hsub
        _ = k - 1 := by simp
    have hsum : (∑ t : Fin k, (B t).card) = k := by
      simp [hBcard]
    rw [hcardUnion, hsum] at hle
    omega
  · intro u v
    by_cases huv : u = v
    · simpa [huv]
    · have hKu : K = A u := by
        apply Finset.eq_of_subset_of_card_le
        · rw [← hpair u v huv]
          exact Finset.inter_subset_left
        · rw [hK, hcardA u]
      have hKv : K = A v := by
        apply Finset.eq_of_subset_of_card_le
        · rw [← hpair u v huv]
          exact Finset.inter_subset_right
        · rw [hK, hcardA v]
      exact hKu.symm.trans hKv

/-- The `K_k` tensor-product family is `k`-sunflower-free.  This formalizes the core structural
claim from the user's "terminal kernel with no genuine one-out-of-q coordinate" note. -/
theorem pairTensorFamily_sunflowerFree (t k : ℕ) (hk : 3 ≤ k) :
    SunflowerFree (pairTensorFamily t k) k := by
  refine taggedProductFamily_sunflowerFree_of_local_constant (D := twoSubsets k) (r := t)
    (hk := by omega) ?_
  intro B hB hSun
  exact twoSubsets_sunflowerTuple_constant k hk hB hSun

/-- The informal declaration "there is no genuine one-out-of-`q` coordinate in `K_k` itself"
from the pasted terminal-kernel note.

Formally: no nonempty vertex set of `K_k` meets every graph edge in exactly one point once
`k ≥ 3`; equivalently `K_k` is not bipartite. -/
theorem no_oneOut_twoSubsets (k : ℕ) (hk : 3 ≤ k) (S : Finset (Fin k)) :
    ¬ ∀ e ∈ twoSubsets k, (e ∩ S).card = 1 := by
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  let c : Fin k := ⟨2, by omega⟩
  have hab : a ≠ b := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hac : a ≠ c := by
    intro h
    have : (0 : ℕ) = 2 := congrArg Fin.val h
    omega
  have hbc : b ≠ c := by
    intro h
    have : (1 : ℕ) = 2 := congrArg Fin.val h
    omega
  have habMem : pairEdge a b ∈ twoSubsets k := by
    rw [mem_twoSubsets_iff]
    exact card_pairEdge hab
  have hacMem : pairEdge a c ∈ twoSubsets k := by
    rw [mem_twoSubsets_iff]
    exact card_pairEdge hac
  have hbcMem : pairEdge b c ∈ twoSubsets k := by
    rw [mem_twoSubsets_iff]
    exact card_pairEdge hbc
  intro h
  have hab1 : ((pairEdge a b) ∩ S).card = 1 := h _ habMem
  have hac1 : ((pairEdge a c) ∩ S).card = 1 := h _ hacMem
  have hbc1 : ((pairEdge b c) ∩ S).card = 1 := h _ hbcMem
  by_cases ha : a ∈ S
  · have hb : b ∉ S := by
      intro hb
      have : ((pairEdge a b) ∩ S).card = 2 := by
        simp [pairEdge, ha, hb, hab]
      omega
    have hc : c ∉ S := by
      intro hc
      have : ((pairEdge a c) ∩ S).card = 2 := by
        simp [pairEdge, ha, hc, hac]
      omega
    have : ((pairEdge b c) ∩ S).card = 0 := by
      simp [pairEdge, hb, hc, hbc]
    omega
  · have hb : b ∈ S := by
      by_contra hb
      have : ((pairEdge a b) ∩ S).card = 0 := by
        simp [pairEdge, ha, hb, hab]
      omega
    have hc : c ∈ S := by
      by_contra hc
      have : ((pairEdge a c) ∩ S).card = 0 := by
        simp [pairEdge, ha, hc, hac]
      omega
    have : ((pairEdge b c) ∩ S).card = 2 := by
      simp [pairEdge, hb, hc, hbc]
    omega

/-- For a genuine one-out block in the tensor product, the contribution of any fixed row is
independent of which local `K_k`-edge is chosen in that row.  This is the rowwise constancy step
in the user's proof that the tensor-product kernel has no genuine one-out coordinate. -/
theorem pairTensor_rowContribution_const
    (t k : ℕ) (hk : 3 ≤ k)
    {Q : Finset (Fin (t + 1) × Fin k)}
    (hQ : IsOneOutSet (pairTensorFamily (t + 1) k) Q)
    (i : Fin (t + 1)) {e f : Finset (Fin k)}
    (he : e ∈ twoSubsets k) (hf : f ∈ twoSubsets k) :
    (e ∩ rowSlice Q i).card = (f ∩ rowSlice Q i).card := by
  classical
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  let d : Finset (Fin k) := pairEdge a b
  have hd : d ∈ twoSubsets k := by
    rw [show d = pairEdge a b by rfl, mem_twoSubsets_iff]
    exact card_pairEdge hab
  let x : Fin (t + 1) → Finset (Fin k) := Function.update (fun _ => d) i e
  let y : Fin (t + 1) → Finset (Fin k) := Function.update (fun _ => d) i f
  let rest : ℕ := Finset.sum (Finset.univ.erase i) fun j => (d ∩ rowSlice Q j).card
  have hxMem : taggedEdge x ∈ pairTensorFamily (t + 1) k := by
    rw [pairTensorFamily, mem_taggedProductFamily_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [x] using he
    · have hxj : x j = d := by
          simp [x, Function.update_of_ne hji]
      rw [hxj]
      exact hd
  have hyMem : taggedEdge y ∈ pairTensorFamily (t + 1) k := by
    rw [pairTensorFamily, mem_taggedProductFamily_iff]
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [y] using hf
    · have hyj : y j = d := by
          simp [y, Function.update_of_ne hji]
      rw [hyj]
      exact hd
  have hsumx :
      ∑ j : Fin (t + 1), (x j ∩ rowSlice Q j).card =
        (e ∩ rowSlice Q i).card + rest := by
    calc
      ∑ j : Fin (t + 1), (x j ∩ rowSlice Q j).card
          = (x i ∩ rowSlice Q i).card +
              Finset.sum (Finset.univ.erase i) (fun j => (x j ∩ rowSlice Q j).card) := by
                simpa using
                  (Finset.add_sum_erase
                    (s := (Finset.univ : Finset (Fin (t + 1))))
                    (f := fun j : Fin (t + 1) => (x j ∩ rowSlice Q j).card)
                    (a := i) (by simp)).symm
      _ = (e ∩ rowSlice Q i).card + rest := by
            congr 1
            · simp [x]
            · unfold rest
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [x, Function.update_of_ne hji]
  have hsumy :
      ∑ j : Fin (t + 1), (y j ∩ rowSlice Q j).card =
        (f ∩ rowSlice Q i).card + rest := by
    calc
      ∑ j : Fin (t + 1), (y j ∩ rowSlice Q j).card
          = (y i ∩ rowSlice Q i).card +
              Finset.sum (Finset.univ.erase i) (fun j => (y j ∩ rowSlice Q j).card) := by
                simpa using
                  (Finset.add_sum_erase
                    (s := (Finset.univ : Finset (Fin (t + 1))))
                    (f := fun j : Fin (t + 1) => (y j ∩ rowSlice Q j).card)
                    (a := i) (by simp)).symm
      _ = (f ∩ rowSlice Q i).card + rest := by
            congr 1
            · simp [y]
            · unfold rest
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [y, Function.update_of_ne hji]
  have hxEq : (e ∩ rowSlice Q i).card + rest = 1 := by
    calc
      (e ∩ rowSlice Q i).card + rest
          = ∑ j : Fin (t + 1), (x j ∩ rowSlice Q j).card := hsumx.symm
      _ = (taggedEdge x ∩ Q).card := by
            simpa using (card_taggedEdge_inter_eq_sum_rowSlices x Q).symm
      _ = 1 := hQ.2 _ hxMem
  have hyEq : (f ∩ rowSlice Q i).card + rest = 1 := by
    calc
      (f ∩ rowSlice Q i).card + rest
          = ∑ j : Fin (t + 1), (y j ∩ rowSlice Q j).card := hsumy.symm
      _ = (taggedEdge y ∩ Q).card := by
            simpa using (card_taggedEdge_inter_eq_sum_rowSlices y Q).symm
      _ = 1 := hQ.2 _ hyMem
  omega

/-- The informal declaration "the `K_k` tensor-product kernel has no genuine one-out-of-`q`
coordinate for any `q`" from the pasted terminal-kernel note. -/
theorem pairTensorFamily_no_oneOutSet (t k : ℕ) (hk : 3 ≤ k) :
    ¬ ∃ Q, IsOneOutSet (pairTensorFamily (t + 1) k) Q := by
  classical
  intro h
  rcases h with ⟨Q, hQ⟩
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  let d : Finset (Fin k) := pairEdge a b
  have hd : d ∈ twoSubsets k := by
    rw [show d = pairEdge a b by rfl, mem_twoSubsets_iff]
    exact card_pairEdge hab
  have hdefaultMem : taggedEdge (fun _ : Fin (t + 1) => d) ∈ pairTensorFamily (t + 1) k := by
    rw [pairTensorFamily, mem_taggedProductFamily_iff]
    intro i
    exact hd
  have hsum : ∑ i : Fin (t + 1), (d ∩ rowSlice Q i).card = 1 := by
    calc
      ∑ i : Fin (t + 1), (d ∩ rowSlice Q i).card = (taggedEdge (fun _ => d) ∩ Q).card := by
        simpa using (card_taggedEdge_inter_eq_sum_rowSlices (fun _ : Fin (t + 1) => d) Q).symm
      _ = 1 := hQ.2 _ hdefaultMem
  have hpos : ∃ i : Fin (t + 1), 0 < (d ∩ rowSlice Q i).card := by
    by_contra hnone
    have hzero : ∀ i : Fin (t + 1), (d ∩ rowSlice Q i).card = 0 := by
      intro i
      have hnot : ¬ 0 < (d ∩ rowSlice Q i).card := by
        intro hi
        exact hnone ⟨i, hi⟩
      omega
    have : ∑ i : Fin (t + 1), (d ∩ rowSlice Q i).card = 0 := by
      simp [hzero]
    omega
  rcases hpos with ⟨i0, hi0pos⟩
  have hi0le_sum : (d ∩ rowSlice Q i0).card ≤ ∑ i : Fin (t + 1), (d ∩ rowSlice Q i).card := by
    simpa using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (t + 1))))
        (f := fun i : Fin (t + 1) => (d ∩ rowSlice Q i).card)
        (a := i0)
        (fun j _ => Nat.zero_le ((d ∩ rowSlice Q j).card))
        (by simp))
  have hi0le : (d ∩ rowSlice Q i0).card ≤ 1 := by
    rw [hsum] at hi0le_sum
    exact hi0le_sum
  have hi0eq : (d ∩ rowSlice Q i0).card = 1 := by
    omega
  have hrow : ∀ e ∈ twoSubsets k, (e ∩ rowSlice Q i0).card = 1 := by
    intro e he
    have hconst := pairTensor_rowContribution_const t k hk hQ i0 he hd
    simpa [d, hi0eq] using hconst
  exact no_oneOut_twoSubsets k hk (rowSlice Q i0) hrow

/-- The informal declaration "`ρ_k(𝓗_t)=0` because the tensor-product kernel has no genuine
one-out-of-`q` coordinate at all" from the pasted terminal-kernel note. -/
theorem rhoOneOut_pairTensorFamily_eq_zero (t k : ℕ) (hk : 3 ≤ k) :
    rhoOneOut (pairTensorFamily (t + 1) k) k = 0 := by
  apply rhoOneOut_eq_zero_of_no_oneOutSet
  exact pairTensorFamily_no_oneOutSet t k hk

@[simp] theorem vertexDegree_pairTensorFamily (t k : ℕ) (i : Fin (t + 1)) (a : Fin k) :
    vertexDegree' (pairTensorFamily (t + 1) k) (i, a) =
      (k - 1) * Nat.choose k 2 ^ t := by
  classical
  rw [pairTensorFamily, vertexDegree_taggedProductFamily_eq_filterCard]
  let P : Finset ↥(twoSubsets k) :=
    (Finset.univ : Finset ↥(twoSubsets k)).filter fun e => a ∈ ((e : ↥(twoSubsets k)) : Finset (Fin k))
  have hPcard : P.card = k - 1 := by
    have hP :
        P = ((twoSubsets k).filter fun e => a ∈ e).attach.map
          ((Function.Embedding.refl _).subtypeMap mem_of_mem_filter) := by
      simpa [P] using
        (Finset.filter_attach (fun e : Finset (Fin k) => a ∈ e) (twoSubsets k))
    rw [hP]
    simp [card_twoSubsetsContaining]
  have hcount := card_words_mem_filter P t i
  rw [hPcard] at hcount
  simpa [P, card_twoSubsets] using hcount

/-- Every vertex of the `K_k` tensor-product family survives leaf stripping as soon as there is at
least one row and `k ≥ 3`. -/
theorem nonLeafVertices_pairTensorFamily_eq_univ (t k : ℕ) (hk : 3 ≤ k) :
    nonLeafVertices (pairTensorFamily (t + 1) k) = Finset.univ := by
  ext v
  constructor
  · intro _
    simp
  · intro _
    rcases v with ⟨i, a⟩
    have hdeg : 2 ≤ vertexDegree' (pairTensorFamily (t + 1) k) (i, a) := by
      rw [vertexDegree_pairTensorFamily]
      have hk1 : 2 ≤ k - 1 := by omega
      have hchoosepos : 0 < Nat.choose k 2 := by
        exact Nat.choose_pos (by omega)
      have hpow : 1 ≤ Nat.choose k 2 ^ t := by
        exact Nat.succ_le_of_lt (Nat.pow_pos hchoosepos)
      calc
        2 ≤ k - 1 := hk1
        _ ≤ (k - 1) * Nat.choose k 2 ^ t := by
              simpa [Nat.one_mul] using Nat.mul_le_mul_left (k - 1) hpow
    simpa [nonLeafVertices] using hdeg

@[simp] theorem strippedEdge_pairTensorFamily
    (t k : ℕ) (hk : 3 ≤ k) (e : Finset (Fin (t + 1) × Fin k)) :
    strippedEdge (pairTensorFamily (t + 1) k) e = e := by
  rw [strippedEdge, nonLeafVertices_pairTensorFamily_eq_univ t k hk]
  simp

/-- One leaf-stripping round leaves the `K_k` tensor-product family unchanged. -/
theorem strippedSupport_pairTensorFamily_eq (t k : ℕ) (hk : 3 ≤ k) :
    strippedSupportFamily (pairTensorFamily (t + 1) k) = pairTensorFamily (t + 1) k := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, hfe⟩
    have hfe' : f = e := by
      simpa [strippedEdge_pairTensorFamily t k hk f] using hfe
    simpa [hfe'.symm] using hf
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, strippedEdge_pairTensorFamily t k hk e⟩

end PairTensor

end FormalConjectures.Problems.Erdos.E20
