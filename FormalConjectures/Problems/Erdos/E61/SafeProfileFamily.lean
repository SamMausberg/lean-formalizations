import FormalConjectures.Problems.Erdos.E61.PathPrimeness

/-!
# Exact safe profile families

This file gives a finite graph model for a path together with a graph whose
vertices choose profiles on that path.  It packages the remaining exact
safe-profile classification from the draft.
-/

namespace Erdos61

open Finset

/-- Raw relation for a path plus a graph whose vertices choose path-neighborhood profiles. -/
def profileBlowupRel {n : ℕ} {VB : Type*} (B : SimpleGraph VB)
    (ν : VB → Finset (Fin (n + 1))) :
    Sum (Fin (n + 1)) VB → Sum (Fin (n + 1)) VB → Prop
  | Sum.inl i, Sum.inl j => (SimpleGraph.pathGraph (n + 1)).Adj i j
  | Sum.inr x, Sum.inr y => B.Adj x y
  | Sum.inr x, Sum.inl i => i ∈ ν x
  | _, _ => False

/--
The graph obtained from a base path by adding a `B` side whose vertices attach
to the path according to `ν`.
-/
def profileBlowup {n : ℕ} {VB : Type*} (B : SimpleGraph VB)
    (ν : VB → Finset (Fin (n + 1))) :
    SimpleGraph (Sum (Fin (n + 1)) VB) :=
  SimpleGraph.fromRel (profileBlowupRel B ν)

@[simp] theorem profileBlowup_adj_left_left {n : ℕ} {VB : Type*}
    (B : SimpleGraph VB) (ν : VB → Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    (profileBlowup B ν).Adj (Sum.inl i : Sum (Fin (n + 1)) VB) (Sum.inl j) ↔
      (SimpleGraph.pathGraph (n + 1)).Adj i j := by
  constructor
  · intro h
    rcases (SimpleGraph.fromRel_adj (profileBlowupRel B ν)
        (Sum.inl i : Sum (Fin (n + 1)) VB) (Sum.inl j)).mp h with
      ⟨_hne, hrel | hrel⟩
    · exact hrel
    · exact hrel.symm
  · intro h
    exact (SimpleGraph.fromRel_adj (profileBlowupRel B ν)
        (Sum.inl i : Sum (Fin (n + 1)) VB) (Sum.inl j)).mpr
      ⟨by simp [h.ne], Or.inl h⟩

@[simp] theorem profileBlowup_adj_right_right {n : ℕ} {VB : Type*}
    (B : SimpleGraph VB) (ν : VB → Finset (Fin (n + 1))) (x y : VB) :
    (profileBlowup B ν).Adj (Sum.inr x : Sum (Fin (n + 1)) VB) (Sum.inr y) ↔
      B.Adj x y := by
  constructor
  · intro h
    rcases (SimpleGraph.fromRel_adj (profileBlowupRel B ν)
        (Sum.inr x : Sum (Fin (n + 1)) VB) (Sum.inr y)).mp h with
      ⟨_hne, hrel | hrel⟩
    · exact hrel
    · exact hrel.symm
  · intro h
    exact (SimpleGraph.fromRel_adj (profileBlowupRel B ν)
        (Sum.inr x : Sum (Fin (n + 1)) VB) (Sum.inr y)).mpr
      ⟨by simp [h.ne], Or.inl h⟩

@[simp] theorem profileBlowup_adj_left_right {n : ℕ} {VB : Type*}
    (B : SimpleGraph VB) (ν : VB → Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (x : VB) :
    (profileBlowup B ν).Adj (Sum.inl i : Sum (Fin (n + 1)) VB) (Sum.inr x) ↔
      i ∈ ν x := by
  simp [profileBlowup, profileBlowupRel, SimpleGraph.fromRel_adj]

@[simp] theorem profileBlowup_adj_right_left {n : ℕ} {VB : Type*}
    (B : SimpleGraph VB) (ν : VB → Finset (Fin (n + 1)))
    (x : VB) (i : Fin (n + 1)) :
    (profileBlowup B ν).Adj (Sum.inr x : Sum (Fin (n + 1)) VB) (Sum.inl i) ↔
      i ∈ ν x := by
  rw [(profileBlowup B ν).adj_comm]
  simp

/-- A path on `n + 1` vertices is `P_{n+2}`-free for cardinality reasons. -/
theorem shorter_path_inducedFree (n : ℕ) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (SimpleGraph.pathGraph (n + 1)) := by
  intro hcopy
  rcases hcopy with ⟨φ⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    exact (RelEmbedding.inj φ).mp hxy
  have hle := Fintype.card_le_of_injective φ hinj
  simp [Fintype.card_fin] at hle

/-- A one-vertex graph is `P_{n+2}`-free when `n ≥ 0`. -/
theorem one_vertex_inducedFree_path (n : ℕ) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (⊥ : SimpleGraph PUnit) := by
  intro hcopy
  rcases hcopy with ⟨φ⟩
  have hinj : Function.Injective φ := by
    intro x y hxy
    exact (RelEmbedding.inj φ).mp hxy
  have hle := Fintype.card_le_of_injective φ hinj
  simp [Fintype.card_fin] at hle

/-- The assignment using `S` on the first path vertex and `T` thereafter. -/
def firstProfileThen {n : ℕ} (S T : Finset (Fin (n + 1))) :
    Fin (n + 1) → Finset (Fin (n + 1)) :=
  fun x => if x.val = 0 then S else T

/-- Witness map for the path created by two distinct profiles. -/
def distinctProfilesWitnessVertex {n : ℕ} (q : Fin (n + 1)) (i : Fin (n + 2)) :
    Sum (Fin (n + 1)) (Fin (n + 1)) :=
  if h : i.val = 0 then Sum.inl q else Sum.inr ⟨i.val - 1, by omega⟩

/-- Numeric code of a witness vertex in the displayed path. -/
def distinctProfilesWitnessCode {n : ℕ} :
    Sum (Fin (n + 1)) (Fin (n + 1)) → ℕ
  | Sum.inl _ => 0
  | Sum.inr i => i.val + 1

@[simp] theorem distinctProfilesWitnessCode_vertex {n : ℕ}
    (q : Fin (n + 1)) (i : Fin (n + 2)) :
    distinctProfilesWitnessCode (distinctProfilesWitnessVertex q i) = i.val := by
  rw [distinctProfilesWitnessVertex]
  by_cases hi : i.val = 0
  · simp [hi, distinctProfilesWitnessCode]
  · simp [hi, distinctProfilesWitnessCode]
    omega

theorem distinctProfilesWitnessVertex_injective {n : ℕ} (q : Fin (n + 1)) :
    Function.Injective (distinctProfilesWitnessVertex q) := by
  intro i j hij
  have hval : i.val = j.val := by
    simpa only [distinctProfilesWitnessCode_vertex] using
      congrArg distinctProfilesWitnessCode hij
  exact Fin.ext hval

theorem distinctProfilesWitness_adj_iff {n : ℕ}
    {S T : Finset (Fin (n + 1))} {q : Fin (n + 1)}
    (hqS : q ∈ S) (hqT : q ∉ T) (i j : Fin (n + 2)) :
    (profileBlowup (SimpleGraph.pathGraph (n + 1)) (firstProfileThen S T)).Adj
        (distinctProfilesWitnessVertex q i) (distinctProfilesWitnessVertex q j) ↔
      (SimpleGraph.pathGraph (n + 2)).Adj i j := by
  rw [SimpleGraph.pathGraph_adj]
  rw [distinctProfilesWitnessVertex, distinctProfilesWitnessVertex]
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · simp [hi, hj]
    · by_cases hjone : j.val = 1
      · have hpred : j.val - 1 = 0 := by omega
        simp [hi, firstProfileThen, hqS, hjone]
      · have hpred : ¬ j.val - 1 = 0 := by omega
        simp [hi, hj, firstProfileThen, hpred, hqT]
        omega
  · by_cases hj : j.val = 0
    · by_cases hione : i.val = 1
      · have hpred : i.val - 1 = 0 := by omega
        simp [hj, firstProfileThen, hqS, hione]
      · have hpred : ¬ i.val - 1 = 0 := by omega
        simp [hi, hj, firstProfileThen, hpred, hqT]
        omega
    · simp [hi, hj, SimpleGraph.pathGraph_adj]
      omega

/-- Two distinct profiles create an induced forbidden path in the profile blow-up. -/
noncomputable def distinctProfilesPathEmbedding {n : ℕ}
    {S T : Finset (Fin (n + 1))} {q : Fin (n + 1)}
    (hqS : q ∈ S) (hqT : q ∉ T) :
    SimpleGraph.pathGraph (n + 2) ↪g
      profileBlowup (SimpleGraph.pathGraph (n + 1)) (firstProfileThen S T) where
  toFun := distinctProfilesWitnessVertex q
  inj' := distinctProfilesWitnessVertex_injective q
  map_rel_iff' := by
    intro i j
    exact distinctProfilesWitness_adj_iff hqS hqT i j

theorem distinct_profiles_blowup_contains_path {n : ℕ}
    {S T : Finset (Fin (n + 1))} {q : Fin (n + 1)}
    (hqS : q ∈ S) (hqT : q ∉ T) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
      (profileBlowup (SimpleGraph.pathGraph (n + 1)) (firstProfileThen S T)) :=
  ⟨distinctProfilesPathEmbedding hqS hqT⟩

/-- Vertex map from a constant-profile blow-up into the substitution graph. -/
def profileBlowupToSubstitutionMap {n : ℕ} {VB : Type*} :
    Sum (Fin (n + 1)) VB →
      SubstitutionVertex (Option (Fin (n + 1))) VB (none : Option (Fin (n + 1)))
  | Sum.inl i => Sum.inl ⟨some i, by simp⟩
  | Sum.inr b => Sum.inr b

theorem profileBlowupToSubstitutionMap_injective {n : ℕ} {VB : Type*} :
    Function.Injective (profileBlowupToSubstitutionMap (n := n) (VB := VB)) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          injection hxy with hsub
          exact congrArg Sum.inl (Option.some.inj (congrArg Subtype.val hsub))
      | inr b =>
          simp [profileBlowupToSubstitutionMap] at hxy
  | inr a =>
      cases y with
      | inl j =>
          simp [profileBlowupToSubstitutionMap] at hxy
      | inr b =>
          injection hxy with hab
          exact congrArg Sum.inr hab

/--
A blow-up where every vertex uses the same profile embeds inducedly into the
substitution graph for that one profile.
-/
noncomputable def profileBlowupToSubstitutionEmbedding {n : ℕ} {VB : Type*}
    (S : Finset (Fin (n + 1))) (B : SimpleGraph VB)
    (ν : VB → Finset (Fin (n + 1))) (hν : ∀ b, ν b = S) :
    profileBlowup B ν ↪g
      substituteVertex (oneVertexExtension S) B (none : Option (Fin (n + 1))) where
  toFun := profileBlowupToSubstitutionMap
  inj' := profileBlowupToSubstitutionMap_injective
  map_rel_iff' := by
    intro x y
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            simp [profileBlowupToSubstitutionMap]
        | inr b =>
            simp [profileBlowupToSubstitutionMap, hν b]
    | inr a =>
        cases y with
        | inl j =>
            simp [profileBlowupToSubstitutionMap, hν a]
        | inr b =>
            simp [profileBlowupToSubstitutionMap]

/-- A one-vertex extension embeds into any profile blow-up containing a vertex with that profile. -/
noncomputable def oneVertexExtensionToProfileBlowupEmbedding {n : ℕ} {VB : Type*}
    (S : Finset (Fin (n + 1))) (B : SimpleGraph VB)
    (ν : VB → Finset (Fin (n + 1))) (b₀ : VB) (hb₀ : ν b₀ = S) :
    oneVertexExtension S ↪g profileBlowup B ν where
  toFun
    | none => Sum.inr b₀
    | some i => Sum.inl i
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j => simp at hxy
    | some i =>
        cases y with
        | none => simp at hxy
        | some j =>
            injection hxy with hij
            exact congrArg some hij
  map_rel_iff' := by
    intro x y
    cases x <;> cases y <;> simp [hb₀]

/--
If a constant-profile substitution is `P_{n+2}`-free, then so is the matching
profile blow-up.
-/
theorem profileBlowup_constant_inducedFree {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin (n + 1))) {VB : Type*} (B : SimpleGraph VB)
    (ν : VB → Finset (Fin (n + 1))) (hν : ∀ b, ν b = S)
    (hS : S ≠ ({0} : Finset (Fin (n + 1))) ∧
      S ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))))
    (hB : InducedFree (SimpleGraph.pathGraph (n + 2)) B) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (profileBlowup B ν) := by
  intro hcopy
  have hsubFree :=
    singleton_safe_profile_substitution_for_paths n hn S hS B hB
  exact hsubFree
    (SimpleGraph.IsIndContained.trans hcopy
      ⟨profileBlowupToSubstitutionEmbedding S B ν hν⟩)

/-- Safe profile families for paths, stated using the profile blow-up model. -/
def ProfileFamilySafe (n : ℕ) (Pi : Finset (Finset (Fin (n + 1)))) : Prop :=
  ∀ {VB : Type} (B : SimpleGraph VB),
    InducedFree (SimpleGraph.pathGraph (n + 2)) B →
      ∀ ν : VB → Finset (Fin (n + 1)),
        (∀ b, ν b ∈ Pi) →
          InducedFree (SimpleGraph.pathGraph (n + 2)) (profileBlowup B ν)

/-- If the right side has no possible profile, the blow-up is just the shorter path. -/
theorem profileBlowup_inducedFree_of_no_profiles {n : ℕ} {VB : Type*}
    (B : SimpleGraph VB) (ν : VB → Finset (Fin (n + 1)))
    (hno : ∀ _b : VB, False) :
    InducedFree (SimpleGraph.pathGraph (n + 2)) (profileBlowup B ν) := by
  intro hcopy
  rcases hcopy with ⟨φ⟩
  let f : Fin (n + 2) → Fin (n + 1) := fun i =>
    match φ i with
    | Sum.inl q => q
    | Sum.inr b => False.elim (hno b)
  have hf : Function.Injective f := by
    intro i j hij
    apply (RelEmbedding.inj φ).mp
    cases hi : φ i with
    | inl qi =>
        cases hj : φ j with
        | inl qj =>
            have hq : qi = qj := by
              simpa [f, hi, hj] using hij
            exact congrArg Sum.inl hq
        | inr bj =>
            exact False.elim (hno bj)
    | inr bi =>
        exact False.elim (hno bi)
  have hle := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at hle

theorem profileFamilySafe_empty (n : ℕ) :
    ProfileFamilySafe n (∅ : Finset (Finset (Fin (n + 1)))) := by
  intro VB B _hB ν hν
  exact profileBlowup_inducedFree_of_no_profiles B ν (by
    intro b
    exact (by simpa using hν b))

/-- Any safe family contains at most one profile. -/
theorem ProfileFamilySafe.eq_of_mem {n : ℕ} {Pi : Finset (Finset (Fin (n + 1)))}
    (hsafe : ProfileFamilySafe n Pi)
    {S T : Finset (Fin (n + 1))} (hSPi : S ∈ Pi) (hTPi : T ∈ Pi) :
    S = T := by
  classical
  by_contra hne
  have hdiff :
      ∃ q : Fin (n + 1), (q ∈ S ∧ q ∉ T) ∨ (q ∈ T ∧ q ∉ S) := by
    by_contra hnone
    apply hne
    ext q
    constructor
    · intro hqS
      by_contra hqT
      exact hnone ⟨q, Or.inl ⟨hqS, hqT⟩⟩
    · intro hqT
      by_contra hqS
      exact hnone ⟨q, Or.inr ⟨hqT, hqS⟩⟩
  rcases hdiff with ⟨q, hq | hq⟩
  · let B : SimpleGraph (Fin (n + 1)) := SimpleGraph.pathGraph (n + 1)
    let ν : Fin (n + 1) → Finset (Fin (n + 1)) := firstProfileThen S T
    have hfree : InducedFree (SimpleGraph.pathGraph (n + 2)) (profileBlowup B ν) :=
      hsafe B (shorter_path_inducedFree n) ν (by
        intro x
        by_cases hx : x.val = 0
        · simp [ν, firstProfileThen, hx, hSPi]
        · simp [ν, firstProfileThen, hx, hTPi])
    exact hfree (distinct_profiles_blowup_contains_path hq.1 hq.2)
  · let B : SimpleGraph (Fin (n + 1)) := SimpleGraph.pathGraph (n + 1)
    let ν : Fin (n + 1) → Finset (Fin (n + 1)) := firstProfileThen T S
    have hfree : InducedFree (SimpleGraph.pathGraph (n + 2)) (profileBlowup B ν) :=
      hsafe B (shorter_path_inducedFree n) ν (by
        intro x
        by_cases hx : x.val = 0
        · simp [ν, firstProfileThen, hx, hTPi]
        · simp [ν, firstProfileThen, hx, hSPi])
    exact hfree (distinct_profiles_blowup_contains_path hq.1 hq.2)

/-- A safe family cannot contain either endpoint singleton profile. -/
theorem ProfileFamilySafe.not_endpoint_singleton {n : ℕ} (_hn : 2 ≤ n)
    {Pi : Finset (Finset (Fin (n + 1)))} (hsafe : ProfileFamilySafe n Pi)
    {S : Finset (Fin (n + 1))} (hSPi : S ∈ Pi) :
    S ≠ ({0} : Finset (Fin (n + 1))) ∧
      S ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))) := by
  constructor
  · intro hS
    let ν : PUnit → Finset (Fin (n + 1)) := fun _ => S
    have hfree := hsafe (⊥ : SimpleGraph PUnit) (one_vertex_inducedFree_path n) ν
      (by intro b; exact hSPi)
    have hbase : SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
        (oneVertexExtension S) := by
      rw [hS]
      exact left_endpoint_extension_contains_path n
    exact hfree (SimpleGraph.IsIndContained.trans hbase
      ⟨oneVertexExtensionToProfileBlowupEmbedding S (⊥ : SimpleGraph PUnit) ν
        PUnit.unit rfl⟩)
  · intro hS
    let ν : PUnit → Finset (Fin (n + 1)) := fun _ => S
    have hfree := hsafe (⊥ : SimpleGraph PUnit) (one_vertex_inducedFree_path n) ν
      (by intro b; exact hSPi)
    have hbase : SimpleGraph.IsIndContained (SimpleGraph.pathGraph (n + 2))
        (oneVertexExtension S) := by
      rw [hS]
      exact right_endpoint_extension_contains_path n
    exact hfree (SimpleGraph.IsIndContained.trans hbase
      ⟨oneVertexExtensionToProfileBlowupEmbedding S (⊥ : SimpleGraph PUnit) ν
        PUnit.unit rfl⟩)

/-- Exact safe-profile classification for paths. -/
theorem profileFamilySafe_iff {n : ℕ} (hn : 2 ≤ n)
    (Pi : Finset (Finset (Fin (n + 1)))) :
    ProfileFamilySafe n Pi ↔
      Pi = ∅ ∨
        ∃ S : Finset (Fin (n + 1)),
          Pi = {S} ∧
            S ≠ ({0} : Finset (Fin (n + 1))) ∧
              S ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))) := by
  constructor
  · intro hsafe
    by_cases hPi : Pi = ∅
    · exact Or.inl hPi
    · right
      rcases Finset.nonempty_iff_ne_empty.mpr hPi with ⟨S, hSPi⟩
      refine ⟨S, ?_, ProfileFamilySafe.not_endpoint_singleton hn hsafe hSPi⟩
      ext T
      constructor
      · intro hTPi
        rw [Finset.mem_singleton]
        exact hsafe.eq_of_mem hTPi hSPi
      · intro hTS
        rw [Finset.mem_singleton] at hTS
        rw [hTS]
        exact hSPi
  · intro hclass
    rcases hclass with hPi | hPi
    · rw [hPi]
      exact profileFamilySafe_empty n
    · rcases hPi with ⟨S, hPi, hS⟩
      intro VB B hB ν hνPi
      have hν : ∀ b, ν b = S := by
        intro b
        have hb := hνPi b
        simpa [hPi] using hb
      exact profileBlowup_constant_inducedFree hn S B ν hν hS hB

end Erdos61
