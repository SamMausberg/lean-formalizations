import FormalConjectures.Problems.Erdos.E61.PathInfrastructure

/-!
# Path-profile graph models

This file starts the graph infrastructure for the path-profile section of the
paper: a path plus one new vertex with prescribed neighborhood on the path.
-/

namespace Erdos61

open Finset

/-- Raw directed relation used to build `oneVertexExtension`. -/
def oneVertexExtensionRel {n : ℕ} (S : Finset (Fin n)) :
    Option (Fin n) → Option (Fin n) → Prop
  | some i, some j => (SimpleGraph.pathGraph n).Adj i j
  | none, some j => j ∈ S
  | _, _ => False

/--
The graph obtained from `pathGraph n` by adding one new vertex `none` adjacent
exactly to the path vertices in `S`.
-/
def oneVertexExtension {n : ℕ} (S : Finset (Fin n)) : SimpleGraph (Option (Fin n)) :=
  SimpleGraph.fromRel (oneVertexExtensionRel S)

@[simp] theorem oneVertexExtension_adj_some_some {n : ℕ} (S : Finset (Fin n))
    (i j : Fin n) :
    (oneVertexExtension S).Adj (some i) (some j) ↔
      (SimpleGraph.pathGraph n).Adj i j := by
  constructor
  · intro h
    rcases (SimpleGraph.fromRel_adj (oneVertexExtensionRel S) (some i) (some j)).mp h
      with ⟨_hne, hrel | hrel⟩
    · exact hrel
    · exact hrel.symm
  · intro h
    exact (SimpleGraph.fromRel_adj (oneVertexExtensionRel S) (some i) (some j)).mpr
      ⟨by simp [h.ne], Or.inl h⟩

@[simp] theorem oneVertexExtension_adj_none_some {n : ℕ} (S : Finset (Fin n))
    (j : Fin n) :
    (oneVertexExtension S).Adj none (some j) ↔ j ∈ S := by
  simp [oneVertexExtension, oneVertexExtensionRel, SimpleGraph.fromRel_adj]

@[simp] theorem oneVertexExtension_adj_some_none {n : ℕ} (S : Finset (Fin n))
    (j : Fin n) :
    (oneVertexExtension S).Adj (some j) none ↔ j ∈ S := by
  rw [(oneVertexExtension S).adj_comm]
  simp

@[simp] theorem oneVertexExtension_not_adj_none_none {n : ℕ} (S : Finset (Fin n)) :
    ¬ (oneVertexExtension S).Adj none none := by
  exact (oneVertexExtension S).irrefl

def leftEndpointPathVertex (n : ℕ) (i : Fin (n + 2)) : Option (Fin (n + 1)) :=
  if h : i.val = 0 then none else some ⟨i.val - 1, by omega⟩

@[simp] theorem leftEndpointPathVertex_zero (n : ℕ) :
    leftEndpointPathVertex n 0 = none := by
  simp [leftEndpointPathVertex]

theorem leftEndpointPathVertex_succ (n : ℕ) (i : Fin (n + 1)) :
    leftEndpointPathVertex n ⟨i.val + 1, by omega⟩ = some i := by
  rw [leftEndpointPathVertex]
  simp only [Nat.add_one_ne_zero, ↓reduceDIte, Option.some.injEq]
  exact Fin.ext (by simp)

theorem leftEndpointPathVertex_injective (n : ℕ) :
    Function.Injective (leftEndpointPathVertex n) := by
  intro i j hij
  by_cases hi : i.val = 0
  · have hj : j.val = 0 := by
      by_contra hj
      simp [leftEndpointPathVertex, hi, hj] at hij
    exact Fin.ext (by omega)
  · by_cases hj : j.val = 0
    · simp [leftEndpointPathVertex, hi, hj] at hij
    · simp [leftEndpointPathVertex, hi, hj, Option.some.injEq, Fin.ext_iff] at hij
      exact Fin.ext (by omega)

/--
If the added vertex attaches to the left endpoint of a path on `n + 1`
vertices, the extension contains an induced path on `n + 2` vertices.
-/
noncomputable def leftEndpointExtensionEmbedding (n : ℕ) :
    SimpleGraph.pathGraph (n + 2) ↪g
      oneVertexExtension ({0} : Finset (Fin (n + 1))) where
  toFun := leftEndpointPathVertex n
  inj' := leftEndpointPathVertex_injective n
  map_rel_iff' := by
    intro i j
    change (oneVertexExtension ({0} : Finset (Fin (n + 1)))).Adj
        (leftEndpointPathVertex n i) (leftEndpointPathVertex n j) ↔
      (SimpleGraph.pathGraph (n + 2)).Adj i j
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst j
        simp
      · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
        have hjsucc : leftEndpointPathVertex n j =
            some ⟨j.val - 1, by omega⟩ := by simp [leftEndpointPathVertex, hj]
        rw [leftEndpointPathVertex_zero, hjsucc]
        rw [oneVertexExtension_adj_none_some, SimpleGraph.pathGraph_adj]
        constructor
        · intro hmem
          rw [mem_singleton] at hmem
          have hv := congrArg Fin.val hmem
          simp at hv
          omega
        · intro hpath
          rw [mem_singleton]
          apply Fin.ext
          rcases hpath with hpath | hpath
          · simp
            omega
          · omega
    · by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst j
        have hisucc : leftEndpointPathVertex n i =
            some ⟨i.val - 1, by omega⟩ := by simp [leftEndpointPathVertex, hi]
        rw [leftEndpointPathVertex_zero, hisucc]
        rw [oneVertexExtension_adj_some_none, SimpleGraph.pathGraph_adj]
        constructor
        · intro hmem
          rw [mem_singleton] at hmem
          have hv := congrArg Fin.val hmem
          simp at hv
          omega
        · intro hpath
          rw [mem_singleton]
          apply Fin.ext
          rcases hpath with hpath | hpath
          · omega
          · simp
            omega
      · have hisucc : leftEndpointPathVertex n i =
            some ⟨i.val - 1, by omega⟩ := by simp [leftEndpointPathVertex, hi]
        have hjsucc : leftEndpointPathVertex n j =
            some ⟨j.val - 1, by omega⟩ := by simp [leftEndpointPathVertex, hj]
        rw [hisucc, hjsucc]
        rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]
        change ((i.val - 1) + 1 = (j.val - 1) ∨ (j.val - 1) + 1 = (i.val - 1)) ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val
        omega

theorem left_endpoint_extension_contains_path (n : ℕ) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
      (oneVertexExtension ({0} : Finset (Fin (n + 1)))) :=
  ⟨leftEndpointExtensionEmbedding n⟩

def rightEndpointPathVertex (n : ℕ) (i : Fin (n + 2)) : Option (Fin (n + 1)) :=
  if h : i.val = n + 1 then none else some ⟨i.val, by omega⟩

theorem rightEndpointPathVertex_last (n : ℕ) :
    rightEndpointPathVertex n ⟨n + 1, by omega⟩ = none := by
  simp [rightEndpointPathVertex]

theorem rightEndpointPathVertex_injective (n : ℕ) :
    Function.Injective (rightEndpointPathVertex n) := by
  intro i j hij
  by_cases hi : i.val = n + 1
  · have hj : j.val = n + 1 := by
      by_contra hj
      simp [rightEndpointPathVertex, hi, hj] at hij
    exact Fin.ext (by omega)
  · by_cases hj : j.val = n + 1
    · simp [rightEndpointPathVertex, hi, hj] at hij
    · simp [rightEndpointPathVertex, hi, hj, Option.some.injEq, Fin.ext_iff] at hij
      exact Fin.ext (by omega)

/--
If the added vertex attaches to the right endpoint of a path on `n + 1`
vertices, the extension contains an induced path on `n + 2` vertices.
-/
noncomputable def rightEndpointExtensionEmbedding (n : ℕ) :
    SimpleGraph.pathGraph (n + 2) ↪g
      oneVertexExtension ({⟨n, by omega⟩} : Finset (Fin (n + 1))) where
  toFun := rightEndpointPathVertex n
  inj' := rightEndpointPathVertex_injective n
  map_rel_iff' := by
    intro i j
    change (oneVertexExtension ({⟨n, by omega⟩} : Finset (Fin (n + 1)))).Adj
        (rightEndpointPathVertex n i) (rightEndpointPathVertex n j) ↔
      (SimpleGraph.pathGraph (n + 2)).Adj i j
    by_cases hi : i.val = n + 1
    · have hiLast : i = ⟨n + 1, by omega⟩ := Fin.ext hi
      rw [hiLast]
      by_cases hj : j.val = n + 1
      · have hjLast : j = ⟨n + 1, by omega⟩ := Fin.ext hj
        rw [hjLast]
        simp
      · have hjsome : rightEndpointPathVertex n j =
            some ⟨j.val, by omega⟩ := by simp [rightEndpointPathVertex, hj]
        rw [rightEndpointPathVertex_last, hjsome]
        rw [oneVertexExtension_adj_none_some, SimpleGraph.pathGraph_adj]
        constructor
        · intro hmem
          rw [mem_singleton] at hmem
          have hv := congrArg Fin.val hmem
          simp at hv
          omega
        · intro hpath
          rw [mem_singleton]
          apply Fin.ext
          rcases hpath with hpath | hpath
          · omega
          · simp
            omega
    · by_cases hj : j.val = n + 1
      · have hjLast : j = ⟨n + 1, by omega⟩ := Fin.ext hj
        rw [hjLast]
        have hisome : rightEndpointPathVertex n i =
            some ⟨i.val, by omega⟩ := by simp [rightEndpointPathVertex, hi]
        rw [rightEndpointPathVertex_last, hisome]
        rw [oneVertexExtension_adj_some_none, SimpleGraph.pathGraph_adj]
        constructor
        · intro hmem
          rw [mem_singleton] at hmem
          have hv := congrArg Fin.val hmem
          simp at hv
          omega
        · intro hpath
          rw [mem_singleton]
          apply Fin.ext
          rcases hpath with hpath | hpath
          · simp
            omega
          · omega
      · have hisome : rightEndpointPathVertex n i =
            some ⟨i.val, by omega⟩ := by simp [rightEndpointPathVertex, hi]
        have hjsome : rightEndpointPathVertex n j =
            some ⟨j.val, by omega⟩ := by simp [rightEndpointPathVertex, hj]
        rw [hisome, hjsome]
        rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]

theorem right_endpoint_extension_contains_path (n : ℕ) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
      (oneVertexExtension ({⟨n, by omega⟩} : Finset (Fin (n + 1)))) :=
  ⟨rightEndpointExtensionEmbedding n⟩

theorem path_extension_embedding_surjective {n : ℕ} {S : Finset (Fin (n + 1))}
    (φ : SimpleGraph.pathGraph (n + 2) ↪g oneVertexExtension S) :
    Function.Surjective φ := by
  classical
  intro y
  have hinj : Function.Injective φ := by
    intro a b hab
    exact (RelEmbedding.inj φ).mp hab
  have hcard :
      (Finset.univ.image φ).card = Fintype.card (Option (Fin (n + 1))) := by
    rw [Finset.card_image_of_injOn]
    · simp [Fintype.card_option, Fintype.card_fin]
    · intro a _ b _ hab
      exact hinj hab
  have himage : Finset.univ.image φ = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hy : y ∈ Finset.univ.image φ := by rw [himage]; simp
  rcases Finset.mem_image.mp hy with ⟨x, _hx, hxy⟩
  exact ⟨x, hxy⟩

theorem pathGraph_exists_neighbor {N : ℕ} (hN : 2 ≤ N) (r : Fin N) :
    ∃ a : Fin N, (SimpleGraph.pathGraph N).Adj r a := by
  by_cases hsucc : r.val + 1 < N
  · refine ⟨⟨r.val + 1, hsucc⟩, ?_⟩
    rw [SimpleGraph.pathGraph_adj]
    left
    simp
  · have hpos : 0 < r.val := by omega
    refine ⟨⟨r.val - 1, by omega⟩, ?_⟩
    rw [SimpleGraph.pathGraph_adj]
    right
    simp
    omega

theorem pathGraph_three_neighbors_impossible {N : ℕ}
    (r a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hra : (SimpleGraph.pathGraph N).Adj r a)
    (hrb : (SimpleGraph.pathGraph N).Adj r b)
    (hrc : (SimpleGraph.pathGraph N).Adj r c) :
    False := by
  rw [SimpleGraph.pathGraph_adj] at hra hrb hrc
  rcases hra with hra | hra <;> rcases hrb with hrb | hrb <;> rcases hrc with hrc | hrc
  · exact hab (Fin.ext (by omega))
  · exact hab (Fin.ext (by omega))
  · exact hac (Fin.ext (by omega))
  · exact hab (Fin.ext (by omega))
  · exact hab (Fin.ext (by omega))
  · exact hac (Fin.ext (by omega))
  · exact hbc (Fin.ext (by omega))
  · exact hab (Fin.ext (by omega))

theorem pathGraph_zero_two_neighbors_impossible {N : ℕ} (hN : 2 ≤ N)
    (a b : Fin N) (hab : a ≠ b)
    (ha : (SimpleGraph.pathGraph N).Adj ⟨0, by omega⟩ a)
    (hb : (SimpleGraph.pathGraph N).Adj ⟨0, by omega⟩ b) :
    False := by
  rw [SimpleGraph.pathGraph_adj] at ha hb
  simp at ha hb
  exact hab (Fin.ext (by omega))

theorem path_extension_no_isolated_vertex {n : ℕ} {S : Finset (Fin (n + 1))}
    (φ : SimpleGraph.pathGraph (n + 2) ↪g oneVertexExtension S)
    (y : Option (Fin (n + 1))) :
    ∃ z : Option (Fin (n + 1)), (oneVertexExtension S).Adj y z := by
  classical
  obtain ⟨r, rfl⟩ := path_extension_embedding_surjective φ y
  obtain ⟨a, hra⟩ := pathGraph_exists_neighbor (N := n + 2) (by omega) r
  exact ⟨φ a, (φ.map_adj_iff).mpr hra⟩

theorem path_extension_three_neighbors_impossible {n : ℕ} {S : Finset (Fin (n + 1))}
    (φ : SimpleGraph.pathGraph (n + 2) ↪g oneVertexExtension S)
    {y a b c : Option (Fin (n + 1))}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hya : (oneVertexExtension S).Adj y a)
    (hyb : (oneVertexExtension S).Adj y b)
    (hyc : (oneVertexExtension S).Adj y c) :
    False := by
  classical
  have hsurj := path_extension_embedding_surjective φ
  obtain ⟨r, rfl⟩ := hsurj y
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  obtain ⟨c', rfl⟩ := hsurj c
  have ha'b' : a' ≠ b' := by
    intro h
    exact hab (by rw [h])
  have ha'c' : a' ≠ c' := by
    intro h
    exact hac (by rw [h])
  have hb'c' : b' ≠ c' := by
    intro h
    exact hbc (by rw [h])
  exact pathGraph_three_neighbors_impossible r a' b' c' ha'b' ha'c' hb'c'
    ((φ.map_adj_iff).mp hya) ((φ.map_adj_iff).mp hyb) ((φ.map_adj_iff).mp hyc)

theorem path_extension_profile_nonempty {n : ℕ} {S : Finset (Fin (n + 1))}
    (φ : SimpleGraph.pathGraph (n + 2) ↪g oneVertexExtension S) :
    S.Nonempty := by
  obtain ⟨z, hz⟩ := path_extension_no_isolated_vertex φ none
  cases z with
  | none =>
      exact False.elim ((oneVertexExtension_not_adj_none_none S) hz)
  | some i =>
      exact ⟨i, by simpa using hz⟩

theorem path_extension_no_internal_profile_vertex {n : ℕ}
    {S : Finset (Fin (n + 1))}
    (φ : SimpleGraph.pathGraph (n + 2) ↪g oneVertexExtension S)
    {i : Fin (n + 1)} (hiS : i ∈ S) (hi0 : i.val ≠ 0) (hin : i.val ≠ n) :
    False := by
  let pred : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let succ : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  have hnone_pred : (none : Option (Fin (n + 1))) ≠ some pred := by simp
  have hnone_succ : (none : Option (Fin (n + 1))) ≠ some succ := by simp
  have hpred_succ : (some pred : Option (Fin (n + 1))) ≠ some succ := by
    intro h
    have hval := congrArg Fin.val (Option.some.inj h)
    simp [pred, succ] at hval
  refine path_extension_three_neighbors_impossible (φ := φ) (y := some i)
    (a := none) (b := some pred) (c := some succ)
    hnone_pred hnone_succ hpred_succ ?_ ?_ ?_
  · simpa using (oneVertexExtension_adj_some_none S i).mpr hiS
  · rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj]
    right
    simp [pred]
    omega
  · rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj]
    left
    simp [succ]

theorem path_extension_not_both_endpoint_profile {n : ℕ} (hn : 1 ≤ n)
    {S : Finset (Fin (n + 1))}
    (φ : SimpleGraph.pathGraph (n + 2) ↪g oneVertexExtension S)
    (hleft : (0 : Fin (n + 1)) ∈ S) (hright : ⟨n, by omega⟩ ∈ S) :
    False := by
  classical
  let left : Fin (n + 1) := 0
  let right : Fin (n + 1) := ⟨n, by omega⟩
  have hsurj := path_extension_embedding_surjective φ
  have htwo :
      ∀ y : Option (Fin (n + 1)),
        ∃ u v : Option (Fin (n + 1)),
          u ≠ v ∧ (oneVertexExtension S).Adj y u ∧ (oneVertexExtension S).Adj y v := by
    intro y
    cases y with
    | none =>
        refine ⟨some left, some right, ?_, ?_, ?_⟩
        · intro h
          have hval := congrArg Fin.val (Option.some.inj h)
          simp [left, right] at hval
          omega
        · simpa [left] using (oneVertexExtension_adj_none_some S left).mpr hleft
        · simpa [right] using (oneVertexExtension_adj_none_some S right).mpr hright
    | some i =>
        by_cases hi0 : i.val = 0
        · let next : Fin (n + 1) := ⟨1, by omega⟩
          refine ⟨none, some next, by simp, ?_, ?_⟩
          · have hi_left : i = left := Fin.ext (by simpa [left] using hi0)
            exact (oneVertexExtension_adj_some_none S i).mpr (by simpa [hi_left] using hleft)
          · rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj]
            exact Or.inl (by change i.val + 1 = 1; omega)
        · by_cases hin : i.val = n
          · let prev : Fin (n + 1) := ⟨n - 1, by omega⟩
            refine ⟨none, some prev, by simp, ?_, ?_⟩
            · have hi_right : i = right := Fin.ext (by simpa [right] using hin)
              exact (oneVertexExtension_adj_some_none S i).mpr (by simpa [hi_right] using hright)
            · rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj]
              right
              simp [prev]
              omega
          · let pred : Fin (n + 1) := ⟨i.val - 1, by omega⟩
            let succ : Fin (n + 1) := ⟨i.val + 1, by omega⟩
            refine ⟨some pred, some succ, ?_, ?_, ?_⟩
            · intro h
              have hval := congrArg Fin.val (Option.some.inj h)
              simp [pred, succ] at hval
            · rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj]
              right
              simp [pred]
              omega
            · rw [oneVertexExtension_adj_some_some, SimpleGraph.pathGraph_adj]
              left
              simp [succ]
  let sourceZero : Fin (n + 2) := ⟨0, by omega⟩
  obtain ⟨u, v, huv, hu, hv⟩ := htwo (φ sourceZero)
  obtain ⟨u', rfl⟩ := hsurj u
  obtain ⟨v', rfl⟩ := hsurj v
  have hu'v' : u' ≠ v' := by
    intro h
    exact huv (by rw [h])
  exact pathGraph_zero_two_neighbors_impossible (N := n + 2) (by omega) u' v' hu'v'
    ((φ.map_adj_iff).mp hu) ((φ.map_adj_iff).mp hv)

/--
Exact one-vertex extension classification from `lem:one-vertex-extension`.
For paths on at least four vertices (`2 ≤ n`, so the final path has `n + 2`
vertices), adding one vertex to `pathGraph (n + 1)` creates an induced
`pathGraph (n + 2)` exactly for the two endpoint singleton profiles.
-/
theorem oneVertexExtension_contains_path_iff_endpoint_singleton
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (n + 1))) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
        (oneVertexExtension S) ↔
      S = ({0} : Finset (Fin (n + 1))) ∨
        S = ({⟨n, by omega⟩} : Finset (Fin (n + 1))) := by
  constructor
  · intro hpath
    rcases hpath with ⟨φ⟩
    let left : Fin (n + 1) := 0
    let right : Fin (n + 1) := ⟨n, by omega⟩
    have hendpoint : ∀ x ∈ S, x = left ∨ x = right := by
      intro x hx
      by_cases hx0 : x.val = 0
      · left
        exact Fin.ext (by simpa [left] using hx0)
      · by_cases hxn : x.val = n
        · right
          exact Fin.ext (by simpa [right] using hxn)
        · exact False.elim
            (path_extension_no_internal_profile_vertex φ hx hx0 hxn)
    have hnonempty : S.Nonempty := path_extension_profile_nonempty φ
    by_cases hleft : left ∈ S
    · by_cases hright : right ∈ S
      · exact False.elim
          (path_extension_not_both_endpoint_profile (by omega) φ
            (by simpa [left] using hleft) (by simpa [right] using hright))
      · left
        ext x
        constructor
        · intro hx
          rcases hendpoint x hx with hxleft | hxright
          · simpa [left] using hxleft
          · exact False.elim (hright (by simpa [hxright] using hx))
        · intro hx
          rw [Finset.mem_singleton] at hx
          simpa [left, hx] using hleft
    · have hright : right ∈ S := by
        rcases hnonempty with ⟨x, hx⟩
        rcases hendpoint x hx with hxleft | hxright
        · exact False.elim (hleft (by simpa [hxleft] using hx))
        · simpa [hxright] using hx
      right
      ext x
      constructor
      · intro hx
        rcases hendpoint x hx with hxleft | hxright
        · exact False.elim (hleft (by simpa [hxleft] using hx))
        · simpa [right] using hxright
      · intro hx
        rw [Finset.mem_singleton] at hx
        simpa [right, hx] using hright
  · intro hS
    rcases hS with hS | hS
    · rw [hS]
      exact left_endpoint_extension_contains_path n
    · rw [hS]
      exact right_endpoint_extension_contains_path n

/-- The `P_k`-free form of `lem:one-vertex-extension`. -/
theorem oneVertexExtension_pathFree_iff_not_endpoint_singleton
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin (n + 1))) :
    ¬ SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
        (oneVertexExtension S) ↔
      S ≠ ({0} : Finset (Fin (n + 1))) ∧
        S ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))) := by
  rw [oneVertexExtension_contains_path_iff_endpoint_singleton n hn S]
  exact not_or

end Erdos61
