import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Rooted `P4` extraction and rectangle traces

This file formalizes finite cores from the rooted-`P4` section of
`eh_forum_trimmed_v9.tex`: the two-anchor defect extraction and the local
rectangle obstruction used in the star-forest shattering discussion.
-/

open Finset
open scoped BigOperators

namespace Erdos61

variable {α β γ : Type*}

/-- The `Y*` defect set from the two-anchor extraction argument. -/
def twoAnchorDefect
    (RA : γ → α → Prop) (RD : γ → β → Prop)
    [DecidableRel RA] [DecidableRel RD]
    (A : Finset α) (D : Finset β) (Y : Finset γ) : Finset γ :=
  Y.filter fun y => (∃ a ∈ A, RA y a) ∧ (∃ d ∈ D, RD y d)

/--
Finite core of `prop:defect-extraction`.

After removing the defect vertices that see both anchors, at least half of what
remains avoids one anchor side.  Pair that side with `A` or `D`.
-/
theorem two_anchor_extraction_defect
    [DecidableEq γ]
    (RA : γ → α → Prop) (RD : γ → β → Prop)
    [DecidableRel RA] [DecidableRel RD]
    (A : Finset α) (D : Finset β) (Y : Finset γ) :
    (∃ Z : Finset γ, Z ⊆ Y ∧
        (Y \ twoAnchorDefect RA RD A D Y).card ≤ 2 * Z.card ∧
        Anticomplete (fun a y => RA y a) A Z) ∨
      ∃ Z : Finset γ, Z ⊆ Y ∧
        (Y \ twoAnchorDefect RA RD A D Y).card ≤ 2 * Z.card ∧
        Anticomplete (fun d y => RD y d) D Z := by
  classical
  let YA : Finset γ := Y.filter fun y => ∀ a ∈ A, ¬ RA y a
  let YD : Finset γ := Y.filter fun y => ∀ d ∈ D, ¬ RD y d
  have hcover : Y \ twoAnchorDefect RA RD A D Y ⊆ YA ∪ YD := by
    intro y hy
    have hyY : y ∈ Y := (mem_sdiff.mp hy).1
    have hynot : y ∉ twoAnchorDefect RA RD A D Y := (mem_sdiff.mp hy).2
    by_cases hA : ∃ a ∈ A, RA y a
    · have hnoD : ∀ d ∈ D, ¬ RD y d := by
        intro d hdD hyd
        exact hynot (mem_filter.mpr ⟨hyY, hA, ⟨d, hdD, hyd⟩⟩)
      exact mem_union_right YA (mem_filter.mpr ⟨hyY, hnoD⟩)
    · have hnoA : ∀ a ∈ A, ¬ RA y a := by
        intro a haA hya
        exact hA ⟨a, haA, hya⟩
      exact mem_union_left YD (mem_filter.mpr ⟨hyY, hnoA⟩)
  have hcard :
      (Y \ twoAnchorDefect RA RD A D Y).card ≤ YA.card + YD.card := by
    calc
      (Y \ twoAnchorDefect RA RD A D Y).card ≤ (YA ∪ YD).card := card_mono hcover
      _ ≤ YA.card + YD.card := card_union_le YA YD
  by_cases hAhalf : (Y \ twoAnchorDefect RA RD A D Y).card ≤ 2 * YA.card
  · left
    refine ⟨YA, ?_, hAhalf, ?_⟩
    · intro y hy
      exact (mem_filter.mp hy).1
    · intro a ha y hy
      exact (mem_filter.mp hy).2 a ha
  · right
    have hDhalf : (Y \ twoAnchorDefect RA RD A D Y).card ≤ 2 * YD.card := by
      omega
    refine ⟨YD, ?_, hDhalf, ?_⟩
    · intro y hy
      exact (mem_filter.mp hy).1
    · intro d hd y hy
      exact (mem_filter.mp hy).2 d hd

/--
No-defect specialization of `two_anchor_extraction_defect`, corresponding to
`thm:two-anchor-extraction` after the forbidden induced cycle proves `Y* = ∅`.
-/
theorem two_anchor_extraction_no_defect
    (RA : γ → α → Prop) (RD : γ → β → Prop)
    [DecidableRel RA] [DecidableRel RD]
    (A : Finset α) (D : Finset β) (Y : Finset γ)
    (hdef : twoAnchorDefect RA RD A D Y = ∅) :
    (∃ Z : Finset γ, Z ⊆ Y ∧ Y.card ≤ 2 * Z.card ∧
        Anticomplete (fun a y => RA y a) A Z) ∨
      ∃ Z : Finset γ, Z ⊆ Y ∧ Y.card ≤ 2 * Z.card ∧
        Anticomplete (fun d y => RD y d) D Z := by
  classical
  rcases two_anchor_extraction_defect RA RD A D Y with
    ⟨Z, hZY, hcard, hanti⟩ | ⟨Z, hZY, hcard, hanti⟩
  · left
    refine ⟨Z, hZY, ?_, hanti⟩
    simpa [hdef] using hcard
  · right
    refine ⟨Z, hZY, ?_, hanti⟩
    simpa [hdef] using hcard

/--
Finite average principle used in `thm:two-anchor-extraction`: some edge has
weight at least the average, stated multiplicatively to avoid division.
-/
theorem exists_weight_at_least_average {ε : Type*} (E : Finset ε) (w : ε → ℕ)
    (hE : E.Nonempty) :
    ∃ e ∈ E, (∑ e' ∈ E, w e') ≤ E.card * w e := by
  classical
  obtain ⟨e, he, hmax⟩ := exists_max_image E w hE
  refine ⟨e, he, ?_⟩
  calc
    (∑ e' ∈ E, w e') ≤ ∑ _e' ∈ E, w e := by
      refine sum_le_sum ?_
      intro e' he'
      exact hmax e' he'
    _ = E.card * w e := by simp

/-- Rectangle trace `E ∩ (P × Q)` for a bipartite edge set `E`. -/
def rectangleTrace [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (P : Finset α) (Q : Finset β) : Finset (α × β) :=
  E.filter fun e => e.1 ∈ P ∧ e.2 ∈ Q

/-- A finite edge set is shattered by rectangle traces, restricted to `F`. -/
def ShatteredByRectangles [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (F : Finset (α × β)) : Prop :=
  ∀ S : Finset (α × β), S ⊆ F →
    ∃ P : Finset α, ∃ Q : Finset β,
      ∀ e ∈ F, e ∈ S ↔ e ∈ rectangleTrace E P Q

/--
The formal obstruction in `thm:star-forest`: a three-edge path cannot be
shattered by rectangles.  Selecting the two diagonal edges forces the middle
edge of the path.
-/
theorem three_edge_path_not_shattered
    [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (F : Finset (α × β)) (hFE : F ⊆ E)
    {u₁ u₂ : α} {v₁ v₂ : β} (hu : u₁ ≠ u₂) (hv : v₁ ≠ v₂)
    (h₁₁ : (u₁, v₁) ∈ F) (h₂₁ : (u₂, v₁) ∈ F) (h₂₂ : (u₂, v₂) ∈ F) :
    ¬ ShatteredByRectangles E F := by
  classical
  intro hshatter
  let S : Finset (α × β) := {(u₁, v₁), (u₂, v₂)}
  have hSsub : S ⊆ F := by
    intro e he
    simp only [S, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact h₁₁
    · exact h₂₂
  rcases hshatter S hSsub with ⟨P, Q, hPQ⟩
  have hdiag₁ : (u₁, v₁) ∈ rectangleTrace E P Q := (hPQ (u₁, v₁) h₁₁).1 (by simp [S])
  have hdiag₂ : (u₂, v₂) ∈ rectangleTrace E P Q := (hPQ (u₂, v₂) h₂₂).1 (by simp [S])
  have hu₁P : u₁ ∈ P := (mem_filter.mp hdiag₁).2.1
  have hv₁Q : v₁ ∈ Q := (mem_filter.mp hdiag₁).2.2
  have hu₂P : u₂ ∈ P := (mem_filter.mp hdiag₂).2.1
  have hv₂Q : v₂ ∈ Q := (mem_filter.mp hdiag₂).2.2
  have hmiddle_rect : (u₂, v₁) ∈ rectangleTrace E P Q := by
    exact mem_filter.mpr ⟨hFE h₂₁, hu₂P, hv₁Q⟩
  have hmiddle_S : (u₂, v₁) ∈ S := (hPQ (u₂, v₁) h₂₁).2 hmiddle_rect
  simp only [S, mem_insert, mem_singleton, Prod.mk.injEq] at hmiddle_S
  rcases hmiddle_S with ⟨hleft, _⟩ | ⟨_, hright⟩
  · exact hu hleft.symm
  · exact hv hright

/-- A star of bipartite edges is shattered by rectangle traces. -/
theorem star_edges_shattered_by_rectangles
    [DecidableEq α] [DecidableEq β]
    (u : α) (Leaves : Finset β)
    (E : Finset (α × β))
    (hE : Leaves.image (fun v => (u, v)) ⊆ E) :
    ShatteredByRectangles E (Leaves.image fun v => (u, v)) := by
  classical
  intro S hS
  refine ⟨{u}, S.image Prod.snd, ?_⟩
  intro e heF
  rcases mem_image.mp heF with ⟨v, hvLeaves, rfl⟩
  constructor
  · intro hSuv
    exact mem_filter.mpr ⟨hE heF, by simp, mem_image.mpr ⟨(u, v), hSuv, rfl⟩⟩
  · intro hrect
    rcases mem_image.mp (mem_filter.mp hrect).2.2 with ⟨e, heS, heq⟩
    have heF' : e ∈ Leaves.image fun v => (u, v) := hS heS
    rcases mem_image.mp heF' with ⟨w, _hwLeaves, rfl⟩
    change w = v at heq
    simpa [heq] using heS

/--
A one-sided star forest whose components are centered on the left side is
shattered by rectangle traces.  The map `center` assigns to each right-side leaf
the left-side center of its component.
-/
theorem right_unique_edges_shattered_by_rectangles
    [DecidableEq α] [DecidableEq β]
    (center : β → α) (Leaves : Finset β)
    (E : Finset (α × β))
    (hE : Leaves.image (fun v => (center v, v)) ⊆ E) :
    ShatteredByRectangles E (Leaves.image fun v => (center v, v)) := by
  classical
  intro S hS
  refine ⟨S.image Prod.fst, Leaves.filter fun v => (center v, v) ∈ S, ?_⟩
  intro e heF
  rcases mem_image.mp heF with ⟨v, hvLeaves, rfl⟩
  constructor
  · intro hSedge
    exact mem_filter.mpr
      ⟨hE heF, mem_image.mpr ⟨(center v, v), hSedge, rfl⟩,
        mem_filter.mpr ⟨hvLeaves, hSedge⟩⟩
  · intro hrect
    exact (mem_filter.mp (mem_filter.mp hrect).2.2).2

/--
The symmetric one-sided star forest theorem, with components centered on the
right side.
-/
theorem left_unique_edges_shattered_by_rectangles
    [DecidableEq α] [DecidableEq β]
    (center : α → β) (Roots : Finset α)
    (E : Finset (α × β))
    (hE : Roots.image (fun u => (u, center u)) ⊆ E) :
    ShatteredByRectangles E (Roots.image fun u => (u, center u)) := by
  classical
  intro S hS
  refine ⟨Roots.filter fun u => (u, center u) ∈ S, S.image Prod.snd, ?_⟩
  intro e heF
  rcases mem_image.mp heF with ⟨u, huRoots, rfl⟩
  constructor
  · intro hSedge
    exact mem_filter.mpr
      ⟨hE heF, mem_filter.mpr ⟨huRoots, hSedge⟩,
        mem_image.mpr ⟨(u, center u), hSedge, rfl⟩⟩
  · intro hrect
    exact (mem_filter.mp (mem_filter.mp hrect).2.1).2

/-- A matching of bipartite edges is shattered by rectangle traces. -/
theorem matching_edges_shattered_by_rectangles
    [DecidableEq α] [DecidableEq β]
    (U : ι → α) (V : ι → β) (I : Finset ι)
    (hU : Set.InjOn U I) (hV : Set.InjOn V I)
    (E : Finset (α × β))
    (hE : I.image (fun i => (U i, V i)) ⊆ E) :
    ShatteredByRectangles E (I.image fun i => (U i, V i)) := by
  classical
  intro S hS
  let IS : Finset ι := I.filter fun i => (U i, V i) ∈ S
  refine ⟨IS.image U, IS.image V, ?_⟩
  intro e heF
  rcases mem_image.mp heF with ⟨i, hiI, rfl⟩
  have hi_iff : i ∈ IS ↔ (U i, V i) ∈ S := by
    simp [IS, hiI]
  constructor
  · intro hiS
    have hiIS : i ∈ IS := hi_iff.mpr hiS
    exact mem_filter.mpr
      ⟨hE heF, mem_image.mpr ⟨i, hiIS, rfl⟩, mem_image.mpr ⟨i, hiIS, rfl⟩⟩
  · intro hrect
    rcases (mem_filter.mp hrect).2 with ⟨hUi, hVi⟩
    rcases mem_image.mp hUi with ⟨iU, hiUIS, hUi_eq⟩
    rcases mem_image.mp hVi with ⟨iV, hiVIS, hVi_eq⟩
    have hiU_I : iU ∈ I := (mem_filter.mp hiUIS).1
    have hiV_I : iV ∈ I := (mem_filter.mp hiVIS).1
    have h_iU : iU = i := hU hiU_I hiI hUi_eq
    have h_iV : iV = i := hV hiV_I hiI hVi_eq
    exact hi_iff.mp (by simpa [h_iU] using hiUIS)

/-- A trace family shatters `F` if it contains every subset of `F`. -/
def ShattersAllSubsets {ε : Type*} (traces : Set (Finset ε)) (F : Finset ε) : Prop :=
  ∀ S : Finset ε, S ⊆ F → S ∈ traces

/-- The powerset-indexed Boolean cube shatters its ground set. -/
theorem full_powerset_shatters {ε : Type*} (F : Finset ε) :
    ShattersAllSubsets (Set.range fun S : {S : Finset ε // S ⊆ F} => (S : Finset ε)) F := by
  intro S hSF
  exact ⟨⟨S, hSF⟩, rfl⟩

section TraceCompression

variable {B₁ B₂ B₃ B₄ : Type*}

/--
Exact finite form of `prop:trace-count`.

If the endpoint trace families from `B₂` into `B₁` and from `B₃` into `B₄`
have at most `q` values, and the middle blocks have size at least `q * s`,
then either a large anticomplete pair is already visible on one of the three
interfaces, or there is a middle edge whose endpoint traces miss fewer than
`s` vertices on both sides.
-/
theorem trace_count_compression_finite
    [DecidableEq B₁] [DecidableEq B₄]
    (R₁₂ : B₂ → B₁ → Prop) (R₃₄ : B₃ → B₄ → Prop) (M : B₂ → B₃ → Prop)
    [DecidableRel R₁₂] [DecidableRel R₃₄]
    (B₁s : Finset B₁) (B₂s : Finset B₂) (B₃s : Finset B₃) (B₄s : Finset B₄)
    {q s : ℕ}
    (hB₂ne : B₂s.Nonempty) (hB₃ne : B₃s.Nonempty)
    (hB₂ : q * s ≤ B₂s.card) (hB₃ : q * s ≤ B₃s.card)
    (htr₁ : (B₂s.image (traceFinset R₁₂ B₁s)).card ≤ q)
    (htr₄ : (B₃s.image (traceFinset R₃₄ B₄s)).card ≤ q) :
    (∃ U : Finset B₂, U ⊆ B₂s ∧ s ≤ U.card ∧
      ∃ V : Finset B₃, V ⊆ B₃s ∧ s ≤ V.card ∧ Anticomplete M U V) ∨
    (∃ U : Finset B₂, U ⊆ B₂s ∧ s ≤ U.card ∧
      ∃ Z : Finset B₁, Z ⊆ B₁s ∧ Z.card = s ∧
        Anticomplete (fun b₂ b₁ => R₁₂ b₂ b₁) U Z) ∨
    (∃ V : Finset B₃, V ⊆ B₃s ∧ s ≤ V.card ∧
      ∃ Z : Finset B₄, Z ⊆ B₄s ∧ Z.card = s ∧
        Anticomplete (fun b₃ b₄ => R₃₄ b₃ b₄) V Z) ∨
    ∃ b₂ ∈ B₂s, ∃ b₃ ∈ B₃s, M b₂ b₃ ∧
      (B₁s \ traceFinset R₁₂ B₁s b₂).card < s ∧
      (B₄s \ traceFinset R₃₄ B₄s b₃).card < s := by
  classical
  let f₁ : B₂ → Finset B₁ := traceFinset R₁₂ B₁s
  let f₄ : B₃ → Finset B₄ := traceFinset R₃₄ B₄s
  rcases exists_fiber_card_ge B₂s f₁ hB₂ne htr₁ hB₂ with ⟨T₁, hT₁, hT₁large⟩
  rcases exists_fiber_card_ge B₃s f₄ hB₃ne htr₄ hB₃ with ⟨T₄, hT₄, hT₄large⟩
  let U : Finset B₂ := fiberOver B₂s f₁ T₁
  let V : Finset B₃ := fiberOver B₃s f₄ T₄
  have hUsub : U ⊆ B₂s := by intro x hx; exact (mem_fiberOver_iff.mp hx).1
  have hVsub : V ⊆ B₃s := by intro x hx; exact (mem_fiberOver_iff.mp hx).1
  have hUlarge : s ≤ U.card := hT₁large
  have hVlarge : s ≤ V.card := hT₄large
  by_cases hEdge : ∃ b₂ ∈ U, ∃ b₃ ∈ V, M b₂ b₃
  · rcases hEdge with ⟨b₂, hb₂U, b₃, hb₃V, hb₂b₃⟩
    have hb₂B₂ : b₂ ∈ B₂s := hUsub hb₂U
    have hb₃B₃ : b₃ ∈ B₃s := hVsub hb₃V
    by_cases hmiss₁ : s ≤ (B₁s \ traceFinset R₁₂ B₁s b₂).card
    · right; left
      rcases exists_subset_card_eq hmiss₁ with ⟨Z, hZsub, hZcard⟩
      refine ⟨U, hUsub, hUlarge, Z, ?_, hZcard, ?_⟩
      · intro z hz
        exact (mem_sdiff.mp (hZsub hz)).1
      · intro x hxU z hzZ hxz
        have hxtrace : traceFinset R₁₂ B₁s x = traceFinset R₁₂ B₁s b₂ := by
          have hxT : f₁ x = T₁ := (mem_fiberOver_iff.mp hxU).2
          have hbT : f₁ b₂ = T₁ := (mem_fiberOver_iff.mp hb₂U).2
          exact hxT.trans hbT.symm
        have hz_not : z ∉ traceFinset R₁₂ B₁s b₂ := (mem_sdiff.mp (hZsub hzZ)).2
        have hz_in_x : z ∈ traceFinset R₁₂ B₁s x :=
          mem_filter.mpr ⟨(mem_sdiff.mp (hZsub hzZ)).1, hxz⟩
        rw [hxtrace] at hz_in_x
        exact hz_not hz_in_x
    · by_cases hmiss₄ : s ≤ (B₄s \ traceFinset R₃₄ B₄s b₃).card
      · right; right; left
        rcases exists_subset_card_eq hmiss₄ with ⟨Z, hZsub, hZcard⟩
        refine ⟨V, hVsub, hVlarge, Z, ?_, hZcard, ?_⟩
        · intro z hz
          exact (mem_sdiff.mp (hZsub hz)).1
        · intro x hxV z hzZ hxz
          have hxtrace : traceFinset R₃₄ B₄s x = traceFinset R₃₄ B₄s b₃ := by
            have hxT : f₄ x = T₄ := (mem_fiberOver_iff.mp hxV).2
            have hbT : f₄ b₃ = T₄ := (mem_fiberOver_iff.mp hb₃V).2
            exact hxT.trans hbT.symm
          have hz_not : z ∉ traceFinset R₃₄ B₄s b₃ := (mem_sdiff.mp (hZsub hzZ)).2
          have hz_in_x : z ∈ traceFinset R₃₄ B₄s x :=
            mem_filter.mpr ⟨(mem_sdiff.mp (hZsub hzZ)).1, hxz⟩
          rw [hxtrace] at hz_in_x
          exact hz_not hz_in_x
      · right; right; right
        exact ⟨b₂, hb₂B₂, b₃, hb₃B₃, hb₂b₃, Nat.lt_of_not_ge hmiss₁,
          Nat.lt_of_not_ge hmiss₄⟩
  · left
    refine ⟨U, hUsub, hUlarge, V, hVsub, hVlarge, ?_⟩
    intro b₂ hb₂U b₃ hb₃V hb₂b₃
    exact hEdge ⟨b₂, hb₂U, b₃, hb₃V, hb₂b₃⟩

end TraceCompression

end Erdos61
