import Mathlib
import FormalConjectures.Problems.Erdos.E20.Foundations.BetaChain

open Finset
open scoped Classical

namespace FormalConjectures.Problems.Erdos.E20

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Informal leaf-stripping preamble:
for a family `𝓕`, the surviving vertex set is
`L(𝓕) := {v : d_𝓕(v) ≥ 2}`. -/
def nonLeafVertices (H : Finset (Finset α)) : Finset α :=
  Finset.univ.filter fun v => 2 ≤ vertexDegree' H v

/-- Informal leaf-stripping preamble:
for an edge `E ∈ 𝓕`, its stripped image is `r(E) := E ∩ L(𝓕)`. -/
def strippedEdge (H : Finset (Finset α)) (e : Finset α) : Finset α :=
  e ∩ nonLeafVertices H

/-- Informal leaf-stripping preamble:
`∂𝓕` is obtained by stripping every edge and then deduplicating, i.e. it is the support
of the stripped-image multiset.  Formally we encode that support as a `Finset`. -/
def strippedSupportFamily (H : Finset (Finset α)) : Finset (Finset α) :=
  H.image (strippedEdge H)

/-- The iterated leaf-stripping sequence `F_t`. -/
def iteratedStripping (H : Finset (Finset α)) : ℕ → Finset (Finset α)
  | 0 => H
  | t + 1 => strippedSupportFamily (iteratedStripping H t)

/-- A family is terminal for leaf stripping when one more stripping round changes nothing. -/
def IsTerminalFamily (H : Finset (Finset α)) : Prop :=
  strippedSupportFamily H = H

/-- Informal leaf-stripping preamble:
`m_K` is the multiplicity of `K` in the stripped-image multiset
`!{ r(E) : E ∈ 𝓕 }!`.  Formally we record that multiplicity by counting the corresponding
fiber of the stripping map. -/
def strippedMultiplicity (H : Finset (Finset α)) (K : Finset α) : ℕ :=
  (H.filter fun e => strippedEdge H e = K).card

/-- Informal §1:
for a subfamily `𝓐`, the common intersection `⋂_{E ∈ 𝓐} E`.  Since the ambient type is finite,
we realize it as a `Finset` rather than a set. -/
def familyInter (A : Finset (Finset α)) : Finset α :=
  Finset.univ.filter fun x => ∀ e ∈ A, x ∈ e

/-- Informal §2:
a subfamily is a sunflower with kernel `K` when every edge contains `K` and every pair of
distinct edges intersects exactly in `K`.  This is the finite-subfamily version used in the
one-round reconstruction theorem. -/
def IsSunflowerWithKernel (U : Finset (Finset α)) (K : Finset α) : Prop :=
  (∀ e ∈ U, K ⊆ e) ∧ ∀ e ∈ U, ∀ f ∈ U, e ≠ f → e ∩ f = K

/-- Informal §2:
the `K`-fiber of the stripping map consists of all edges whose stripped image is exactly `K`. -/
def kernelFiber (H : Finset (Finset α)) (K : Finset α) : Finset (Finset α) :=
  H.filter fun e => strippedEdge H e = K

/-- Informal §2, corrected singleton-safe version of `s_K`:
among distinct stripped edges different from `K`, `strippedPetalChoices H K` records the candidate
subfamilies that already form a sunflower with kernel `K` after one stripping round. -/
noncomputable def strippedPetalChoices (H : Finset (Finset α)) (K : Finset α) :
    Finset (Finset (Finset α)) :=
  ((strippedSupportFamily H).erase K).powerset.filter fun S => IsSunflowerWithKernel S K

/-- Informal §2, corrected singleton-safe version of `s_K`:
this is the maximum number of distinct non-kernel stripped petals that can coexist with kernel `K`
after one stripping round. -/
noncomputable def strippedPetalMax (H : Finset (Finset α)) (K : Finset α) : ℕ :=
  (strippedPetalChoices H K).sup Finset.card

/-- Informal §2, corrected singleton-safe one-round parameter:
the exact one-round sunflower size is controlled by the kernel multiplicity plus the maximum number
of distinct non-kernel stripped petals. -/
noncomputable def oneRoundSunflowerBound (H : Finset (Finset α)) (K : Finset α) : ℕ :=
  strippedMultiplicity H K + strippedPetalMax H K

/-- Informal leaf-stripping preamble:
the support really is the image of the stripping map, so every stripped edge in `∂𝓕` comes from
an original edge. -/
theorem mem_strippedSupportFamily_iff {H : Finset (Finset α)} {A : Finset α} :
    A ∈ strippedSupportFamily H ↔ ∃ e ∈ H, strippedEdge H e = A := by
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

@[simp] theorem iteratedStripping_zero (H : Finset (Finset α)) :
    iteratedStripping H 0 = H := rfl

@[simp] theorem iteratedStripping_succ (H : Finset (Finset α)) (t : ℕ) :
    iteratedStripping H (t + 1) = strippedSupportFamily (iteratedStripping H t) := rfl

/-- If every edge survives one stripping round unchanged, then the family is terminal. -/
theorem strippedSupportFamily_eq_self_of_forall_strippedEdge_eq
    {H : Finset (Finset α)}
    (h : ∀ e ∈ H, strippedEdge H e = e) :
    strippedSupportFamily H = H := by
  ext A
  constructor
  · intro hA
    rcases mem_strippedSupportFamily_iff.mp hA with ⟨e, he, hstrip⟩
    simpa [← hstrip, h e he] using he
  · intro hA
    exact Finset.mem_image.mpr ⟨A, hA, h A hA⟩

/-- A non-fixed stripping round contains an edge that actually shrinks. -/
theorem exists_shrinking_edge_of_strippedSupportFamily_ne_self
    {H : Finset (Finset α)} (h : strippedSupportFamily H ≠ H) :
    ∃ e ∈ H, strippedEdge H e ≠ e := by
  classical
  by_contra hnone
  apply h
  exact strippedSupportFamily_eq_self_of_forall_strippedEdge_eq (by
    intro e he
    by_contra hshrink
    exact hnone ⟨e, he, hshrink⟩)

/-- Informal §1:
for every subfamily `𝓐`, membership in `⋂_{E ∈ 𝓐} E` means belonging to every edge of `𝓐`. -/
theorem mem_familyInter_iff {A : Finset (Finset α)} {x : α} :
    x ∈ familyInter A ↔ ∀ e ∈ A, x ∈ e := by
  simp [familyInter]

/-- Informal §1:
if `x` belongs to the intersection of a subfamily `𝓐 ⊆ 𝓕` with at least two members,
then `x` survives stripping because it lies in at least two edges of `𝓕`. -/
theorem mem_nonLeafVertices_of_mem_familyInter
    {H A : Finset (Finset α)} (hA : A ⊆ H) (hcard : 2 ≤ A.card) {x : α}
    (hx : x ∈ familyInter A) :
    x ∈ nonLeafVertices H := by
  have hsubset : A ⊆ H.filter fun e => x ∈ e := by
    intro e heA
    exact Finset.mem_filter.mpr ⟨hA heA, (mem_familyInter_iff.mp hx) e heA⟩
  have hdeg : 2 ≤ vertexDegree' H x := by
    simpa [vertexDegree'] using le_trans hcard (Finset.card_le_card hsubset)
  simpa [nonLeafVertices] using hdeg

/-- Informal §1:
stripping preserves the intersection of every subfamily of cardinality at least `2`. -/
theorem familyInter_stripped_eq
    {H A : Finset (Finset α)} (hA : A ⊆ H) (hcard : 2 ≤ A.card) :
    familyInter A = familyInter (A.image (strippedEdge H)) := by
  ext x
  constructor
  · intro hx
    have hxLeaf : x ∈ nonLeafVertices H :=
      mem_nonLeafVertices_of_mem_familyInter hA hcard hx
    rw [mem_familyInter_iff] at hx ⊢
    intro A' hA'
    rcases Finset.mem_image.mp hA' with ⟨e, heA, rfl⟩
    exact Finset.mem_inter.mpr ⟨hx e heA, hxLeaf⟩
  · intro hx
    rw [mem_familyInter_iff] at hx ⊢
    intro e heA
    have hmem : strippedEdge H e ∈ A.image (strippedEdge H) :=
      Finset.mem_image.mpr ⟨e, heA, rfl⟩
    exact (Finset.mem_inter.mp (hx _ hmem)).1

/-- Informal §1, pairwise version:
for distinct edges `E,F ∈ 𝓕`, leaf stripping removes only private padding and preserves the exact
intersection `E ∩ F = r(E) ∩ r(F)`. -/
theorem pairwise_intersection_stripped_eq
    {H : Finset (Finset α)} {e f : Finset α}
    (he : e ∈ H) (hf : f ∈ H) (hef : e ≠ f) :
    e ∩ f = strippedEdge H e ∩ strippedEdge H f := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxe, hxf⟩
    let A : Finset (Finset α) := {e, f}
    have hA : A ⊆ H := by
      intro g hg
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact he
      · exact hf
    have hcard : 2 ≤ A.card := by
      simp [A, hef]
    have hxInter : x ∈ familyInter A := by
      rw [mem_familyInter_iff]
      intro g hg
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact hxe
      · exact hxf
    have hxLeaf : x ∈ nonLeafVertices H :=
      mem_nonLeafVertices_of_mem_familyInter hA hcard hxInter
    simp [strippedEdge, hxe, hxf, hxLeaf]
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx₁).1, (Finset.mem_inter.mp hx₂).1⟩

/-- Every stripped edge is a subset of its parent edge. -/
theorem strippedEdge_subset (H : Finset (Finset α)) (e : Finset α) :
    strippedEdge H e ⊆ e := by
  simp [strippedEdge]

/-- Informal strict-parent lemma:
if an edge `B` in a stripped family shrinks again in the next round, then it has a strict parent
in the previous round.  More precisely, there is some `A ∈ H` with `∂A = B` and `B ⊂ A`. -/
theorem strict_parent_of_shrinking_child
    {H : Finset (Finset α)} {B : Finset α}
    (hB : B ∈ strippedSupportFamily H)
    (hshrink : strippedEdge (strippedSupportFamily H) B ≠ B) :
    ∃ A ∈ H, strippedEdge H A = B ∧ B ⊂ A := by
  classical
  rcases mem_strippedSupportFamily_iff.mp hB with ⟨A₀, hA₀, hA₀strip⟩
  have hBssub : strippedEdge (strippedSupportFamily H) B ⊂ B := by
    refine Finset.ssubset_iff_subset_ne.mpr ?_
    refine ⟨strippedEdge_subset _ _, hshrink⟩
  rcases Finset.exists_of_ssubset hBssub with ⟨x, hxB, hxnot⟩
  have hxAB : x ∈ strippedEdge H A₀ := by
    simpa [hA₀strip] using hxB
  have hxnonleafH : x ∈ nonLeafVertices H := (Finset.mem_inter.mp hxAB).2
  have hxdegH2 : 2 ≤ ((H.filter fun e => x ∈ e)).card := by
    simpa [vertexDegree'] using (by
      simpa [nonLeafVertices] using hxnonleafH : 2 ≤ vertexDegree' H x)
  have hxdegH : 1 < ((H.filter fun e => x ∈ e)).card := by omega
  rcases Finset.exists_mem_notMem_of_card_lt_card
      (s := ({A₀} : Finset (Finset α)))
      (t := H.filter fun e => x ∈ e) (by simpa using hxdegH) with ⟨C, hC, hCne⟩
  have hCmemH : C ∈ H := (Finset.mem_filter.mp hC).1
  have hxC : x ∈ C := (Finset.mem_filter.mp hC).2
  have hxnextle1 : ((strippedSupportFamily H).filter fun e => x ∈ e).card ≤ 1 := by
    have hxnotleaf : x ∉ nonLeafVertices (strippedSupportFamily H) := by
      intro hxleaf
      exact hxnot (by simpa [strippedEdge, hxleaf] using hxB)
    have hdeg : vertexDegree' (strippedSupportFamily H) x ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ vertexDegree' (strippedSupportFamily H) x := by omega
      exact hxnotleaf (by simpa [nonLeafVertices] using h2)
    simpa [vertexDegree'] using hdeg
  have hBmemnext : B ∈ (strippedSupportFamily H).filter fun e => x ∈ e := by
    exact Finset.mem_filter.mpr ⟨hB, hxB⟩
  have hCstrip_mem : strippedEdge H C ∈ (strippedSupportFamily H).filter fun e => x ∈ e := by
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact Finset.mem_image.mpr ⟨C, hCmemH, rfl⟩
    · have hxnonleafH' : x ∈ nonLeafVertices H := hxnonleafH
      simpa [strippedEdge] using ⟨hxC, hxnonleafH'⟩
  have hCstrip_eq : strippedEdge H C = B := by
    exact (Finset.card_le_one_iff.mp hxnextle1) hCstrip_mem hBmemnext
  by_cases hABeq : A₀ = B
  · refine ⟨C, hCmemH, hCstrip_eq, ?_⟩
    have hsub : B ⊆ C := by
      simpa [hCstrip_eq] using (strippedEdge_subset H C)
    have hCB : C ≠ B := by
      intro hEq
      apply hCne
      simp [hABeq, hEq]
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by intro hEq; exact hCB hEq.symm⟩
  · refine ⟨A₀, hA₀, hA₀strip, ?_⟩
    have hsub : B ⊆ A₀ := by
      simpa [hA₀strip] using (strippedEdge_subset H A₀)
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by intro hEq; exact hABeq hEq.symm⟩

/-- Along an iterated stripping sequence from an `n`-uniform family, any edge that still shrinks
at time `t` leaves room for `t + 1` strict size drops from an original `n`-edge. -/
theorem iteratedStripping_shrinking_card_add_le_uniformity
    {H : Finset (Finset α)} {n t : ℕ} (hH : IsRUniform H n) {B : Finset α}
    (hB : B ∈ iteratedStripping H t)
    (hshrink : strippedEdge (iteratedStripping H t) B ≠ B) :
    t + 1 + (strippedEdge (iteratedStripping H t) B).card ≤ n := by
  induction t generalizing B with
  | zero =>
      have hssub : strippedEdge H B ⊂ B := by
        exact Finset.ssubset_iff_subset_ne.mpr ⟨strippedEdge_subset H B, hshrink⟩
      have hlt : (strippedEdge H B).card < B.card := Finset.card_lt_card hssub
      have hBcard : B.card = n := hH B hB
      have hlt' : (strippedEdge (iteratedStripping H 0) B).card < n := by
        simpa [iteratedStripping_zero, hBcard] using hlt
      omega
  | succ t ih =>
      have hB' : B ∈ strippedSupportFamily (iteratedStripping H t) := by
        simpa using hB
      rcases strict_parent_of_shrinking_child
          (H := iteratedStripping H t) (B := B) hB' hshrink with
        ⟨A, hA, hAstrip, hBA⟩
      have hAshrink : strippedEdge (iteratedStripping H t) A ≠ A := by
        intro hEq
        have hBAeq : B = A := by
          rw [← hAstrip, hEq]
        exact (Finset.ssubset_iff_subset_ne.mp hBA).2 hBAeq
      have hih := ih hA hAshrink
      rw [hAstrip] at hih
      have hchild_ssub :
          strippedEdge (iteratedStripping H (t + 1)) B ⊂ B := by
        exact Finset.ssubset_iff_subset_ne.mpr
          ⟨strippedEdge_subset (iteratedStripping H (t + 1)) B, hshrink⟩
      have hchild_lt :
          (strippedEdge (iteratedStripping H (t + 1)) B).card < B.card :=
        Finset.card_lt_card hchild_ssub
      omega

/-- The stripping process for an `n`-uniform family is fixed after at most `n` rounds. -/
theorem iteratedStripping_fixed_after_uniformity
    (H : Finset (Finset α)) {n : ℕ} (hH : IsRUniform H n) :
    iteratedStripping H (n + 1) = iteratedStripping H n := by
  classical
  by_contra hne
  have hround :
      strippedSupportFamily (iteratedStripping H n) ≠ iteratedStripping H n := by
    simpa using hne
  rcases exists_shrinking_edge_of_strippedSupportFamily_ne_self hround with
    ⟨B, hB, hshrink⟩
  have hle :=
    iteratedStripping_shrinking_card_add_le_uniformity (H := H) (n := n) (t := n)
      hH hB hshrink
  omega

/-- The `n`th stripping stage of an `n`-uniform family is terminal. -/
theorem terminal_iteratedStripping_of_uniform
    (H : Finset (Finset α)) {n : ℕ} (hH : IsRUniform H n) :
    IsTerminalFamily (iteratedStripping H n) := by
  unfold IsTerminalFamily
  simpa using iteratedStripping_fixed_after_uniformity H hH

/-- Once a stripping sequence has reached a fixed point, all later stages are equal. -/
theorem iteratedStripping_stable_after_fixed
    {H : Finset (Finset α)} {t : ℕ}
    (hfix : iteratedStripping H (t + 1) = iteratedStripping H t) :
    ∀ r : ℕ, iteratedStripping H (t + r) = iteratedStripping H t := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, iteratedStripping_succ, ih]
      simpa using hfix

/-- After round `n`, an `n`-uniform family's stripping sequence remains stable forever. -/
theorem iteratedStripping_stable_after_uniformity
    (H : Finset (Finset α)) {n : ℕ} (hH : IsRUniform H n) :
    ∀ r : ℕ, iteratedStripping H (n + r) = iteratedStripping H n :=
  iteratedStripping_stable_after_fixed (iteratedStripping_fixed_after_uniformity H hH)

/-- Stripping never increases edge sizes, so every iterated kernel of an `n`-uniform family has
rank at most `n`. -/
theorem iteratedStripping_edge_card_le_uniformity
    {H : Finset (Finset α)} {n t : ℕ} (hH : IsRUniform H n)
    {B : Finset α} (hB : B ∈ iteratedStripping H t) :
    B.card ≤ n := by
  induction t generalizing B with
  | zero =>
      exact le_of_eq (hH B hB)
  | succ t ih =>
      rcases mem_strippedSupportFamily_iff.mp (by simpa using hB) with ⟨A, hA, hstrip⟩
      calc
        B.card = (strippedEdge (iteratedStripping H t) A).card := by rw [hstrip]
        _ ≤ A.card := Finset.card_le_card (strippedEdge_subset _ _)
        _ ≤ n := ih hA

/-- Informal §2, first consequence:
if two distinct original edges have the same stripped image, then those two edges already form a
sunflower with that common stripped image as kernel. -/
theorem stripped_duplicate_intersection
    {H : Finset (Finset α)} {e f G : Finset α}
    (he : e ∈ H) (hf : f ∈ H) (hef : e ≠ f)
    (hstrip : strippedEdge H e = G) (hstrip' : strippedEdge H f = G) :
    e ∩ f = G := by
  calc
    e ∩ f = strippedEdge H e ∩ strippedEdge H f :=
      pairwise_intersection_stripped_eq he hf hef
    _ = G := by simp [hstrip, hstrip']

/-- Informal §2:
in any nontrivial sunflower subfamily `𝓤 ⊆ 𝓕` with kernel `K`, the kernel survives stripping:
every vertex of `K` lies in `L(𝓕)`. -/
theorem kernel_subset_nonLeafVertices_of_sunflower
    {H U : Finset (Finset α)} {K : Finset α} (hU : U ⊆ H) (hcard : 2 ≤ U.card)
    (hSun : IsSunflowerWithKernel U K) :
    K ⊆ nonLeafVertices H := by
  intro x hxK
  have hxInter : x ∈ familyInter U := by
    rw [mem_familyInter_iff]
    intro e heU
    exact hSun.1 e heU hxK
  exact mem_nonLeafVertices_of_mem_familyInter hU hcard hxInter

/-- Informal §2:
once one strips a nontrivial sunflower, only the kernel image can repeat; repeated non-kernel
images are impossible. -/
theorem stripped_duplicates_only_at_kernel
    {H U : Finset (Finset α)} {K : Finset α} (hU : U ⊆ H) (hcard : 2 ≤ U.card)
    (hSun : IsSunflowerWithKernel U K) {e f : Finset α}
    (heU : e ∈ U) (hfU : f ∈ U) (hef : e ≠ f)
    (hstrip : strippedEdge H e = strippedEdge H f) :
    strippedEdge H e = K := by
  have _ := hcard
  have hEq : e ∩ f = K := hSun.2 e heU f hfU hef
  calc
    strippedEdge H e = strippedEdge H e ∩ strippedEdge H f := by simp [hstrip]
    _ = e ∩ f := by
      symm
      exact pairwise_intersection_stripped_eq (hU heU) (hU hfU) hef
    _ = K := hEq

/-- Informal §2:
any stripped sunflower on distinct reduced edges lifts to a sunflower in the original family by
choosing one preimage for each reduced edge.  The formal statement also records that the lifted
subfamily has the prescribed stripped-image set. -/
theorem exists_lift_of_strippedSunflower
    {H : Finset (Finset α)} {S : Finset (Finset α)} {K : Finset α}
    (hS : S ⊆ strippedSupportFamily H)
    (hSun : IsSunflowerWithKernel S K) :
    ∃ U ⊆ H, IsSunflowerWithKernel U K ∧ U.card = S.card ∧
      U.image (strippedEdge H) = S := by
  classical
  let rep : S → Finset α := fun A =>
    Classical.choose <| mem_strippedSupportFamily_iff.mp (hS A.2)
  let U : Finset (Finset α) := S.attach.image fun A => rep A
  have hrep_mem : ∀ A : S, rep A ∈ H := fun A =>
    (Classical.choose_spec (mem_strippedSupportFamily_iff.mp (hS A.2))).1
  have hrep_strip : ∀ A : S, strippedEdge H (rep A) = A.1 := fun A =>
    (Classical.choose_spec (mem_strippedSupportFamily_iff.mp (hS A.2))).2
  have hrep_inj : Function.Injective rep := by
    intro A B hEq
    apply Subtype.ext
    simpa [hrep_strip A, hrep_strip B] using congrArg (strippedEdge H) hEq
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro e heU
    rcases Finset.mem_image.mp heU with ⟨A, -, rfl⟩
    exact hrep_mem A
  · refine ⟨?_, ?_⟩
    · intro e heU
      rcases Finset.mem_image.mp heU with ⟨A, hA, rfl⟩
      intro x hxK
      have hxA : x ∈ A.1 := hSun.1 _ A.2 hxK
      have hxStrip : x ∈ strippedEdge H (rep A) := by
        simpa [hrep_strip A] using hxA
      exact (Finset.mem_inter.mp hxStrip).1
    · intro e heU f hfU hef
      rcases Finset.mem_image.mp heU with ⟨A, hA, rfl⟩
      rcases Finset.mem_image.mp hfU with ⟨B, hB, rfl⟩
      have hAB : A.1 ≠ B.1 := by
        intro hEq
        apply hef
        have hSub : A = B := Subtype.ext hEq
        simp [hSub]
      have hrep_ne : rep A ≠ rep B := by
        intro hEq
        exact hAB (congrArg Subtype.val (hrep_inj hEq))
      calc
        rep A ∩ rep B = strippedEdge H (rep A) ∩ strippedEdge H (rep B) := by
          exact pairwise_intersection_stripped_eq (hrep_mem A) (hrep_mem B) hrep_ne
        _ = A.1 ∩ B.1 := by simp [hrep_strip]
        _ = K := hSun.2 _ A.2 _ B.2 hAB
  · simpa [U] using Finset.card_image_of_injOn
      (s := S.attach) (f := fun A => rep A)
      (by
        intro A hA B hB hEq
        exact hrep_inj hEq)
  · ext A
    constructor
    · intro hA
      rcases Finset.mem_image.mp hA with ⟨e, heU, hEq⟩
      rcases Finset.mem_image.mp heU with ⟨B, hB, rfl⟩
      have hAB : A = B.1 := by
        simpa [hrep_strip B] using hEq.symm
      simp [hAB, B.2]
    · intro hA
      refine Finset.mem_image.mpr ?_
      refine ⟨rep ⟨A, hA⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨A, hA⟩, by simp, rfl⟩
      · simp [hrep_strip]

/-- Informal §2, upper-bound direction of the exact one-round theorem:
every nontrivial sunflower with kernel `K` has size at most
`m_K + s_K = strippedMultiplicity H K + strippedPetalMax H K`. -/
theorem sunflower_card_le_oneRoundSunflowerBound
    {H U : Finset (Finset α)} {K : Finset α} (hU : U ⊆ H) (hcard : 2 ≤ U.card)
    (hSun : IsSunflowerWithKernel U K) :
    U.card ≤ oneRoundSunflowerBound H K := by
  classical
  let U₀ : Finset (Finset α) := U.filter fun e => strippedEdge H e = K
  let U₁ : Finset (Finset α) := U.filter fun e => strippedEdge H e ≠ K
  let S : Finset (Finset α) := U₁.image (strippedEdge H)
  have hUcard : U.card = U₀.card + U₁.card := by
    simpa [U₀, U₁] using
      (Finset.card_filter_add_card_filter_not
        (s := U) (p := fun e => strippedEdge H e = K)).symm
  have hU₀ : U₀.card ≤ strippedMultiplicity H K := by
    exact Finset.card_le_card (by
      intro e he
      exact Finset.mem_filter.mpr
        ⟨hU (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩)
  have hinjOn : Set.InjOn (strippedEdge H) U₁ := by
    intro e he f hf hEq
    by_contra hne
    have heU : e ∈ U := (Finset.mem_filter.mp he).1
    have hfU : f ∈ U := (Finset.mem_filter.mp hf).1
    have hker : strippedEdge H e = K :=
      stripped_duplicates_only_at_kernel hU hcard hSun heU hfU hne hEq
    exact (Finset.mem_filter.mp he).2 hker
  have hSchoice : S ∈ strippedPetalChoices H K := by
    refine Finset.mem_filter.mpr ?_
    constructor
    · refine Finset.mem_powerset.mpr ?_
      intro A hA
      rcases Finset.mem_image.mp hA with ⟨e, he, rfl⟩
      refine Finset.mem_erase.mpr ?_
      exact ⟨(Finset.mem_filter.mp he).2,
        Finset.mem_image.mpr ⟨e, hU (Finset.mem_filter.mp he).1, rfl⟩⟩
    · refine ⟨?_, ?_⟩
      · intro A hA
        rcases Finset.mem_image.mp hA with ⟨e, he, rfl⟩
        have heU : e ∈ U := (Finset.mem_filter.mp he).1
        have hKsurvives : K ⊆ nonLeafVertices H :=
          kernel_subset_nonLeafVertices_of_sunflower hU hcard hSun
        intro x hxK
        exact Finset.mem_inter.mpr ⟨hSun.1 _ heU hxK, hKsurvives hxK⟩
      · intro A hA B hB hAB
        rcases Finset.mem_image.mp hA with ⟨e, he, rfl⟩
        rcases Finset.mem_image.mp hB with ⟨f, hf, rfl⟩
        have hef : e ≠ f := by
          intro hEq
          apply hAB
          simp [hEq]
        calc
          strippedEdge H e ∩ strippedEdge H f = e ∩ f := by
            symm
            exact pairwise_intersection_stripped_eq
              (hU (Finset.mem_filter.mp he).1)
              (hU (Finset.mem_filter.mp hf).1) hef
          _ = K := hSun.2 _ (Finset.mem_filter.mp he).1 _ (Finset.mem_filter.mp hf).1 hef
  have hSbound : S.card ≤ strippedPetalMax H K := Finset.le_sup hSchoice
  have hU₁card : U₁.card = S.card := by
    symm
    simpa [S] using Finset.card_image_of_injOn (s := U₁) (f := strippedEdge H) hinjOn
  calc
    U.card = U₀.card + U₁.card := hUcard
    _ = U₀.card + S.card := by rw [hU₁card]
    _ ≤ strippedMultiplicity H K + strippedPetalMax H K := add_le_add hU₀ hSbound

/-- Informal §2, lower-bound direction of the exact one-round theorem:
if `m_K + s_K ≥ 2`, then one can realize that bound by taking all kernel-fiber edges together
with one lifted preimage of each stripped non-kernel petal in an optimal stripped sunflower. -/
theorem exists_sunflower_card_eq_oneRoundSunflowerBound
    {H : Finset (Finset α)} {K : Finset α}
    (hbound : 2 ≤ oneRoundSunflowerBound H K) :
    ∃ U ⊆ H, IsSunflowerWithKernel U K ∧ U.card = oneRoundSunflowerBound H K := by
  classical
  have _ := hbound
  have hchoices_nonempty : (strippedPetalChoices H K).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [strippedPetalChoices, IsSunflowerWithKernel]
  rcases Finset.exists_mem_eq_sup (s := strippedPetalChoices H K) hchoices_nonempty
      (f := Finset.card) with ⟨S, hS, hSmax⟩
  have hSsun : IsSunflowerWithKernel S K := (Finset.mem_filter.mp hS).2
  have hSerase : S ⊆ (strippedSupportFamily H).erase K :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSsub : S ⊆ strippedSupportFamily H := fun A hA => (Finset.mem_erase.mp (hSerase hA)).2
  obtain ⟨U₁, hU₁H, hU₁sun, hU₁card, hU₁image⟩ := exists_lift_of_strippedSunflower hSsub hSsun
  let U₀ : Finset (Finset α) := kernelFiber H K
  let U : Finset (Finset α) := U₀ ∪ U₁
  have hUdisj : Disjoint U₀ U₁ := by
    refine Finset.disjoint_left.mpr ?_
    intro e he₀ he₁
    have hstrip₀ : strippedEdge H e = K := (Finset.mem_filter.mp he₀).2
    have hstripS : strippedEdge H e ∈ S := by
      rw [← hU₁image]
      exact Finset.mem_image.mpr ⟨e, he₁, rfl⟩
    exact (Finset.mem_erase.mp (hSerase hstripS)).1 hstrip₀
  have hUcard : U.card = oneRoundSunflowerBound H K := by
    have hfiber : U₀.card = strippedMultiplicity H K := by
      simp [U₀, kernelFiber, strippedMultiplicity]
    have hpetal : S.card = strippedPetalMax H K := by
      symm
      simpa [strippedPetalMax] using hSmax
    rw [Finset.card_union_of_disjoint hUdisj, hfiber, hU₁card, hpetal, oneRoundSunflowerBound]
  refine ⟨U, ?_, ?_, hUcard⟩
  · intro e heU
    rcases Finset.mem_union.mp heU with he₀ | he₁
    · exact (Finset.mem_filter.mp he₀).1
    · exact hU₁H he₁
  · refine ⟨?_, ?_⟩
    · intro e heU x hxK
      rcases Finset.mem_union.mp heU with he₀ | he₁
      · have hxIn : x ∈ strippedEdge H e := by
          simpa [(Finset.mem_filter.mp he₀).2] using hxK
        exact (Finset.mem_inter.mp hxIn).1
      · exact hU₁sun.1 _ he₁ hxK
    · intro e heU f hfU hef
      rcases Finset.mem_union.mp heU with he₀ | he₁ <;>
        rcases Finset.mem_union.mp hfU with hf₀ | hf₁
      · exact stripped_duplicate_intersection
          (Finset.mem_filter.mp he₀).1 (Finset.mem_filter.mp hf₀).1 hef
          (Finset.mem_filter.mp he₀).2 (Finset.mem_filter.mp hf₀).2
      · calc
          e ∩ f = strippedEdge H e ∩ strippedEdge H f := by
            exact pairwise_intersection_stripped_eq
              (Finset.mem_filter.mp he₀).1 (hU₁H hf₁) hef
          _ = K := by
            rw [(Finset.mem_filter.mp he₀).2]
            have hstripf : strippedEdge H f ∈ S := by
              rw [← hU₁image]
              exact Finset.mem_image.mpr ⟨f, hf₁, rfl⟩
            exact Finset.inter_eq_left.mpr (hSsun.1 _ hstripf)
      · simpa [inter_comm] using
          (calc
            e ∩ f = strippedEdge H e ∩ strippedEdge H f := by
              exact pairwise_intersection_stripped_eq
                (hU₁H he₁) (Finset.mem_filter.mp hf₀).1 hef
            _ = K := by
              rw [(Finset.mem_filter.mp hf₀).2]
              have hstripe : strippedEdge H e ∈ S := by
                rw [← hU₁image]
                exact Finset.mem_image.mpr ⟨e, he₁, rfl⟩
              exact Finset.inter_eq_right.mpr (hSsun.1 _ hstripe))
      · exact hU₁sun.2 _ he₁ _ hf₁ hef

/-- Informal §2, exact one-round sunflower theorem, formalized in the nontrivial regime relevant
to `k ≥ 3`:
`m_K + s_K` is both an upper bound for every sunflower with kernel `K`, and it is attained whenever
that bound is at least `2`. -/
theorem exact_one_round_sunflower_theorem
    (H : Finset (Finset α)) (K : Finset α) :
    (∀ U ⊆ H, 2 ≤ U.card → IsSunflowerWithKernel U K →
        U.card ≤ oneRoundSunflowerBound H K) ∧
      (2 ≤ oneRoundSunflowerBound H K →
        ∃ U ⊆ H, IsSunflowerWithKernel U K ∧ U.card = oneRoundSunflowerBound H K) := by
  constructor
  · intro U hU hcard hSun
    exact sunflower_card_le_oneRoundSunflowerBound hU hcard hSun
  · exact exists_sunflower_card_eq_oneRoundSunflowerBound

theorem kernelFiber_card_eq_strippedMultiplicity (H : Finset (Finset α)) (K : Finset α) :
    (kernelFiber H K).card = strippedMultiplicity H K := by
  simp [kernelFiber, strippedMultiplicity]

/-- If `H` is `k`-sunflower-free, then no stripping fiber has `k` distinct preimages. -/
theorem strippedMultiplicity_le_pred_of_sunflowerFree
    {H : Finset (Finset α)} {k : ℕ} (hfree : SunflowerFree H k) (K : Finset α) :
    strippedMultiplicity H K ≤ k - 1 := by
  classical
  rw [← kernelFiber_card_eq_strippedMultiplicity]
  by_contra hle
  have hk_le : k ≤ (kernelFiber H K).card := by omega
  obtain ⟨f, hf_range⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := Fin k) (s := kernelFiber H K)
      (by simpa using hk_le)
  let A : Fin k → Finset α := fun i => f i
  have hA_mem_fiber : ∀ i : Fin k, A i ∈ kernelFiber H K := by
    intro i
    exact hf_range (Set.mem_range_self i)
  have hA_mem : ∀ i : Fin k, A i ∈ H := by
    intro i
    exact (Finset.mem_filter.mp (hA_mem_fiber i)).1
  have hA_strip : ∀ i : Fin k, strippedEdge H (A i) = K := by
    intro i
    exact (Finset.mem_filter.mp (hA_mem_fiber i)).2
  have hA_inj : Function.Injective A := by
    intro i j hij
    exact f.injective hij
  have hSun : IsSunflowerTuple A := by
    intro i j i' j' hij hi'j'
    have hne : A i ≠ A j := by
      intro hEq
      exact hij (hA_inj hEq)
    have hne' : A i' ≠ A j' := by
      intro hEq
      exact hi'j' (hA_inj hEq)
    calc
      A i ∩ A j = K :=
        stripped_duplicate_intersection (hA_mem i) (hA_mem j) hne
          (hA_strip i) (hA_strip j)
      _ = A i' ∩ A j' := by
        symm
        exact stripped_duplicate_intersection (hA_mem i') (hA_mem j') hne'
          (hA_strip i') (hA_strip j')
  exact hfree A hA_mem hA_inj hSun

/-- Stripping preserves sunflower-freeness: every sunflower downstairs lifts by choosing one
preimage per stripped edge. -/
theorem SunflowerFree.strippedSupportFamily
    {H : Finset (Finset α)} {k : ℕ} (hfree : SunflowerFree H k) :
    SunflowerFree (strippedSupportFamily H) k := by
  classical
  intro A hA hInj hSun
  let pre : Fin k → Finset α := fun i =>
    Classical.choose (mem_strippedSupportFamily_iff.mp (hA i))
  have hpre_mem : ∀ i, pre i ∈ H := fun i =>
    (Classical.choose_spec (mem_strippedSupportFamily_iff.mp (hA i))).1
  have hpre_strip : ∀ i, strippedEdge H (pre i) = A i := fun i =>
    (Classical.choose_spec (mem_strippedSupportFamily_iff.mp (hA i))).2
  have hpre_inj : Function.Injective pre := by
    intro i j hij
    apply hInj
    simpa [hpre_strip i, hpre_strip j] using congrArg (strippedEdge H) hij
  have hpre_sun : IsSunflowerTuple pre := by
    intro i j i' j' hij hi'j'
    have hpre_ne : pre i ≠ pre j := hpre_inj.ne hij
    have hpre_ne' : pre i' ≠ pre j' := hpre_inj.ne hi'j'
    calc
      pre i ∩ pre j = strippedEdge H (pre i) ∩ strippedEdge H (pre j) :=
        pairwise_intersection_stripped_eq (hpre_mem i) (hpre_mem j) hpre_ne
      _ = A i ∩ A j := by simp [hpre_strip]
      _ = A i' ∩ A j' := hSun hij hi'j'
      _ = strippedEdge H (pre i') ∩ strippedEdge H (pre j') := by simp [hpre_strip]
      _ = pre i' ∩ pre j' := by
        symm
        exact pairwise_intersection_stripped_eq (hpre_mem i') (hpre_mem j') hpre_ne'
  exact hfree pre hpre_mem hpre_inj hpre_sun

/-- Sunflower-freeness is preserved at every iterated stripping stage. -/
theorem SunflowerFree.iteratedStripping
    {H : Finset (Finset α)} {k : ℕ} (hfree : SunflowerFree H k) :
    ∀ t : ℕ, SunflowerFree (iteratedStripping H t) k := by
  intro t
  induction t with
  | zero => simpa using hfree
  | succ t ih =>
      simpa using ih.strippedSupportFamily

/-- Exact fiber decomposition for the one-round stripping map. -/
theorem card_eq_sum_strippedMultiplicity (H : Finset (Finset α)) :
    H.card = ∑ K ∈ strippedSupportFamily H, strippedMultiplicity H K := by
  classical
  let f : Finset α → Finset α := strippedEdge H
  have hcover :
      (H.image f).biUnion (fun K => H.filter fun e => f e = K) = H := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨K, hK, heK⟩
      exact (Finset.mem_filter.mp heK).1
    · intro he
      exact Finset.mem_biUnion.mpr
        ⟨f e, Finset.mem_image.mpr ⟨e, he, rfl⟩, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  have hdisj :
      ((H.image f : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint
        (fun K => H.filter fun e => f e = K) := by
    intro K hK L hL hKL
    change Disjoint (H.filter fun e => f e = K) (H.filter fun e => f e = L)
    rw [Finset.disjoint_left]
    intro e heK heL
    have hfK : f e = K := (Finset.mem_filter.mp heK).2
    have hfL : f e = L := (Finset.mem_filter.mp heL).2
    exact hKL (hfK.symm.trans hfL)
  calc
    H.card = ((H.image f).biUnion fun K => H.filter fun e => f e = K).card := by
      rw [hcover]
    _ = ∑ K ∈ H.image f, (H.filter fun e => f e = K).card := by
      exact Finset.card_biUnion hdisj
    _ = ∑ K ∈ strippedSupportFamily H, strippedMultiplicity H K := by
      rfl

/-- One stripping round loses at most a factor `k - 1` on a `k`-sunflower-free family. -/
theorem card_le_mul_card_strippedSupportFamily_of_sunflowerFree
    {H : Finset (Finset α)} {k : ℕ} (hfree : SunflowerFree H k) :
    H.card ≤ (k - 1) * (strippedSupportFamily H).card := by
  rw [card_eq_sum_strippedMultiplicity H]
  calc
    (∑ K ∈ strippedSupportFamily H, strippedMultiplicity H K)
        ≤ ∑ K ∈ strippedSupportFamily H, (k - 1) := by
          exact Finset.sum_le_sum (fun K hK =>
            strippedMultiplicity_le_pred_of_sunflowerFree hfree K)
    _ = (k - 1) * (strippedSupportFamily H).card := by
          simp [Nat.mul_comm]

/-- Iterating the one-round bound gives the sharp family-level loss factor. -/
theorem card_le_pow_mul_card_iteratedStripping_of_sunflowerFree
    {H : Finset (Finset α)} {k : ℕ} (hfree : SunflowerFree H k) :
    ∀ t : ℕ, H.card ≤ (k - 1) ^ t * (iteratedStripping H t).card := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have hstep :
          (iteratedStripping H t).card ≤
            (k - 1) * (iteratedStripping H (t + 1)).card := by
        simpa using
          card_le_mul_card_strippedSupportFamily_of_sunflowerFree
            ((hfree.iteratedStripping t))
      calc
        H.card ≤ (k - 1) ^ t * (iteratedStripping H t).card := ih
        _ ≤ (k - 1) ^ t * ((k - 1) * (iteratedStripping H (t + 1)).card) := by
          exact Nat.mul_le_mul_left _ hstep
        _ = (k - 1) ^ (t + 1) * (iteratedStripping H (t + 1)).card := by
          ring

end FormalConjectures.Problems.Erdos.E20
