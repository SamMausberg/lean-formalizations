import Mathlib
import FormalConjectures.Problems.Erdos.E20.BetaChain

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
      simpa [hAB] using B.2
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

end FormalConjectures.Problems.Erdos.E20
