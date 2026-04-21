import FormalConjectures.Problems.Erdos.E20.Kernels.KernelBounds
import FormalConjectures.Problems.Erdos.E20.Families.Counterexample

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Degree-two kernels

This file packages the degree-two row from `sunflower_selected_results.tex`.
The sharp one-copy extremizer is the simplex family, represented by the complete-graph dual
family on `s + 1` vertices.
-/

/-- The `s`-simplex degree-two kernel: all vertex stars of `K_{s+1}`, viewed as sets of graph
edges. -/
def degreeTwoSimplexFamily (s : ℕ) : Finset (Finset (Finset (Fin (s + 1)))) :=
  completeGraphDualFamily (s + 1)

lemma exists_ne_fin_of_three_le {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    ∃ l : Fin m, l ≠ i := by
  have hproper : ({i} : Finset (Fin m)) ⊂ (Finset.univ : Finset (Fin m)) := by
    refine ⟨by simp, ?_⟩
    intro hsub
    have hcard : m ≤ 1 := by
      calc
        m = (Finset.univ : Finset (Fin m)).card := by simp
        _ ≤ ({i} : Finset (Fin m)).card := Finset.card_le_card hsub
        _ = 1 := by simp
    omega
  rcases Finset.exists_of_ssubset hproper with ⟨l, -, hl⟩
  exact ⟨l, by simpa using hl⟩

/-- Every two simplex edges meet. -/
theorem completeGraphDualFamily_pairwise_not_disjoint {m : ℕ} (hm : 3 ≤ m)
    {E F : Finset (Finset (Fin m))}
    (hE : E ∈ completeGraphDualFamily m) (hF : F ∈ completeGraphDualFamily m) :
    ¬ Disjoint E F := by
  rcases Finset.mem_image.mp hE with ⟨i, -, rfl⟩
  rcases Finset.mem_image.mp hF with ⟨j, -, rfl⟩
  by_cases hij : i = j
  · subst j
    rcases exists_ne_fin_of_three_le hm i with ⟨l, hli⟩
    exact not_disjoint_iff.mpr ⟨pairEdge i l,
      (pairEdge_mem_completeGraphStar_iff (i := i) (j := l) (l := i) hli.symm).2
        (Or.inl rfl),
      (pairEdge_mem_completeGraphStar_iff (i := i) (j := l) (l := i) hli.symm).2
        (Or.inl rfl)⟩
  · exact not_disjoint_iff.mpr ⟨pairEdge i j,
      (pairEdge_mem_completeGraphStar_iff (i := i) (j := j) (l := i) hij).2
        (Or.inl rfl),
      (pairEdge_mem_completeGraphStar_iff (i := i) (j := j) (l := j) hij).2
        (Or.inr rfl)⟩

/-- Exact vertex degrees in the complete-graph dual family.  Ground elements that are graph
edges have degree `2`; all other finite subsets have degree `0`. -/
theorem vertexDegree_completeGraphDualFamily {m : ℕ} (hm : 3 ≤ m)
    (e : Finset (Fin m)) :
    vertexDegree' (completeGraphDualFamily m) e = if e.card = 2 then 2 else 0 := by
  unfold vertexDegree' completeGraphDualFamily
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective]
  · simp [mem_completeGraphStar_iff]
    by_cases h : e.card = 2
    · simp [h]
    · simp [h]
  · exact completeGraphStar_injective hm

/-- The complete-graph dual family has maximum vertex degree at most `2`. -/
theorem completeGraphDualFamily_maxVertexDegreeAtMost_two {m : ℕ} (hm : 3 ≤ m) :
    MaxVertexDegreeAtMost (completeGraphDualFamily m) 2 := by
  intro e
  rw [vertexDegree_completeGraphDualFamily hm e]
  by_cases h : e.card = 2 <;> simp [h]

/-- The simplex family is `s`-uniform. -/
theorem degreeTwoSimplexFamily_uniform (s : ℕ) :
    IsRUniform (degreeTwoSimplexFamily s) s := by
  simpa [degreeTwoSimplexFamily] using completeGraphDualFamily_uniform (m := s + 1)

/-- The simplex family has exactly `s + 1` edges. -/
theorem card_degreeTwoSimplexFamily (s : ℕ) (hs : 2 ≤ s) :
    (degreeTwoSimplexFamily s).card = s + 1 := by
  have hm : 3 ≤ s + 1 := by omega
  simpa [degreeTwoSimplexFamily] using card_completeGraphDualFamily (m := s + 1) hm

/-- The simplex family is `k`-sunflower-free for every `k ≥ 3`. -/
theorem degreeTwoSimplexFamily_sunflowerFree (s k : ℕ) (hs : 2 ≤ s) (hk : 3 ≤ k) :
    SunflowerFree (degreeTwoSimplexFamily s) k := by
  have hm : 3 ≤ s + 1 := by omega
  simpa [degreeTwoSimplexFamily] using
    completeGraphDualFamily_sunflowerFree (m := s + 1) (k := k) hm hk

/-- The simplex family has maximum vertex degree at most `2`. -/
theorem degreeTwoSimplexFamily_maxVertexDegreeAtMost_two (s : ℕ) (hs : 2 ≤ s) :
    MaxVertexDegreeAtMost (degreeTwoSimplexFamily s) 2 := by
  have hm : 3 ≤ s + 1 := by omega
  simpa [degreeTwoSimplexFamily] using
    completeGraphDualFamily_maxVertexDegreeAtMost_two (m := s + 1) hm

/-- Every two simplex-family edges meet. -/
theorem degreeTwoSimplexFamily_pairwise_not_disjoint (s : ℕ) (hs : 2 ≤ s)
    {E F : Finset (Finset (Fin (s + 1)))}
    (hE : E ∈ degreeTwoSimplexFamily s) (hF : F ∈ degreeTwoSimplexFamily s) :
    ¬ Disjoint E F := by
  have hm : 3 ≤ s + 1 := by omega
  exact completeGraphDualFamily_pairwise_not_disjoint (m := s + 1) hm
    (by simpa [degreeTwoSimplexFamily] using hE)
    (by simpa [degreeTwoSimplexFamily] using hF)

/-- Any pairwise-disjoint subfamily of the simplex has size at most one. -/
theorem card_le_one_of_pairwiseDisjoint_subfamily_degreeTwoSimplex
    (s : ℕ) (hs : 2 ≤ s)
    {M : Finset (Finset (Finset (Fin (s + 1))))}
    (hsub : M ⊆ degreeTwoSimplexFamily s) (hpair : PairwiseDisjointFamily M) :
    M.card ≤ 1 := by
  by_contra hle
  have htwo : 2 ≤ M.card := by omega
  have hpos : 0 < M.card := lt_of_lt_of_le (by decide : 0 < 2) htwo
  rcases Finset.card_pos.mp hpos with ⟨E, hE⟩
  have herase_pos : 0 < (M.erase E).card := by
    rw [Finset.card_erase_of_mem hE]
    omega
  rcases Finset.card_pos.mp herase_pos with ⟨F, hFerase⟩
  have hF : F ∈ M := (Finset.mem_erase.mp hFerase).2
  have hFE : F ≠ E := (Finset.mem_erase.mp hFerase).1
  have hdisj : Disjoint E F := hpair hE hF (fun hEF => hFE hEF.symm)
  exact degreeTwoSimplexFamily_pairwise_not_disjoint s hs (hsub hE) (hsub hF) hdisj

/-- A singleton edge is a maximal matching witness in the simplex family. -/
theorem degreeTwoSimplexFamily_singleton_isMaximalMatching (s : ℕ) (hs : 2 ≤ s) :
    IsMaximalMatchingIn (degreeTwoSimplexFamily s) {completeGraphStar (s + 1) 0} := by
  have hstar : completeGraphStar (s + 1) 0 ∈ degreeTwoSimplexFamily s := by
    exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
  refine
    { subset := ?_
      pairwiseDisjoint := ?_
      meets_every_edge := ?_ }
  · intro E hE
    rw [Finset.mem_singleton] at hE
    simpa [hE] using hstar
  · intro E F hE hF hne
    simp_all
  · intro E hE
    exact ⟨completeGraphStar (s + 1) 0, by simp,
      degreeTwoSimplexFamily_pairwise_not_disjoint s hs hE hstar⟩

/-- The one-copy simplex attains the degree-two bound `|J| ≤ (s + 1)|M|` with a
maximal matching witness of size `1`. -/
theorem degreeTwoSimplexFamily_attains_degreeTwo_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ M : Finset (Finset (Finset (Fin (s + 1)))),
      IsMaximalMatchingIn (degreeTwoSimplexFamily s) M ∧
        M.card = 1 ∧
        (degreeTwoSimplexFamily s).card = (s + 1) * M.card := by
  refine ⟨{completeGraphStar (s + 1) 0}, ?_, by simp, ?_⟩
  · exact degreeTwoSimplexFamily_singleton_isMaximalMatching s hs
  · rw [card_degreeTwoSimplexFamily s hs]
    simp

/-- The complete one-copy sharpness package for the degree-two row. -/
theorem degreeTwoSimplexFamily_sharpness (s : ℕ) (hs : 2 ≤ s) :
    IsRUniform (degreeTwoSimplexFamily s) s ∧
      MaxVertexDegreeAtMost (degreeTwoSimplexFamily s) 2 ∧
      (∀ {M : Finset (Finset (Finset (Fin (s + 1))))},
        M ⊆ degreeTwoSimplexFamily s → PairwiseDisjointFamily M → M.card ≤ 1) ∧
      ∃ M : Finset (Finset (Finset (Fin (s + 1)))),
        IsMaximalMatchingIn (degreeTwoSimplexFamily s) M ∧
          M.card = 1 ∧
          (degreeTwoSimplexFamily s).card = (s + 1) * M.card := by
  exact ⟨degreeTwoSimplexFamily_uniform s,
    degreeTwoSimplexFamily_maxVertexDegreeAtMost_two s hs,
    fun hsub hpair => card_le_one_of_pairwiseDisjoint_subfamily_degreeTwoSimplex s hs hsub hpair,
    degreeTwoSimplexFamily_attains_degreeTwo_bound s hs⟩

/-- The copy-`c`, vertex-`i` edge in a disjoint union of `t` simplex kernels. -/
def taggedDegreeTwoSimplexEdge (s t : ℕ) (c : Fin t) (i : Fin (s + 1)) :
    Finset (Fin t × Finset (Fin (s + 1))) :=
  (completeGraphStar (s + 1) i).image fun e => (c, e)

/-- The disjoint union of `t` copies of the `s`-simplex degree-two kernel. -/
def degreeTwoSimplexUnion (s t : ℕ) :
    Finset (Finset (Fin t × Finset (Fin (s + 1)))) :=
  (Finset.univ : Finset (Fin t × Fin (s + 1))).image
    fun p => taggedDegreeTwoSimplexEdge s t p.1 p.2

/-- The matching consisting of one distinguished simplex edge in each copy. -/
def degreeTwoSimplexUnionMatching (s t : ℕ) :
    Finset (Finset (Fin t × Finset (Fin (s + 1)))) :=
  (Finset.univ : Finset (Fin t)).image fun c => taggedDegreeTwoSimplexEdge s t c 0

lemma mem_taggedDegreeTwoSimplexEdge {s t : ℕ} {c : Fin t} {i : Fin (s + 1)}
    {x : Fin t × Finset (Fin (s + 1))} :
    x ∈ taggedDegreeTwoSimplexEdge s t c i ↔
      x.1 = c ∧ x.2 ∈ completeGraphStar (s + 1) i := by
  unfold taggedDegreeTwoSimplexEdge
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨e, he, hxe⟩
    subst x
    simp [he]
  · rintro ⟨rfl, hx⟩
    exact Finset.mem_image.mpr ⟨x.2, hx, by simp⟩

lemma taggedDegreeTwoSimplexEdge_injective {s t : ℕ} (hs : 2 ≤ s) :
    Function.Injective
      (fun p : Fin t × Fin (s + 1) => taggedDegreeTwoSimplexEdge s t p.1 p.2) := by
  intro p q hpq
  have hcard : (completeGraphStar (s + 1) p.2).card = s := by
    simpa using card_completeGraphStar (m := s + 1) p.2
  have hpos : 0 < (completeGraphStar (s + 1) p.2).card := by
    rw [hcard]
    omega
  rcases Finset.card_pos.mp hpos with ⟨e, he⟩
  have hxq : (p.1, e) ∈ taggedDegreeTwoSimplexEdge s t q.1 q.2 := by
    have hxp : (p.1, e) ∈ taggedDegreeTwoSimplexEdge s t p.1 p.2 :=
      (mem_taggedDegreeTwoSimplexEdge).2 ⟨rfl, he⟩
    simpa [hpq] using hxp
  have htag : p.1 = q.1 := (mem_taggedDegreeTwoSimplexEdge.1 hxq).1
  have hstars : completeGraphStar (s + 1) p.2 = completeGraphStar (s + 1) q.2 := by
    ext e'
    constructor
    · intro he'
      have hxq' : (p.1, e') ∈ taggedDegreeTwoSimplexEdge s t q.1 q.2 := by
        have hxp' : (p.1, e') ∈ taggedDegreeTwoSimplexEdge s t p.1 p.2 :=
          (mem_taggedDegreeTwoSimplexEdge).2 ⟨rfl, he'⟩
        simpa [hpq] using hxp'
      exact (mem_taggedDegreeTwoSimplexEdge.1 hxq').2
    · intro he'
      have hxp' : (q.1, e') ∈ taggedDegreeTwoSimplexEdge s t p.1 p.2 := by
        have hxq' : (q.1, e') ∈ taggedDegreeTwoSimplexEdge s t q.1 q.2 :=
          (mem_taggedDegreeTwoSimplexEdge).2 ⟨rfl, he'⟩
        simpa [hpq] using hxq'
      exact (mem_taggedDegreeTwoSimplexEdge.1 hxp').2
  have hm : 3 ≤ s + 1 := by omega
  have hidx : p.2 = q.2 := completeGraphStar_injective hm hstars
  exact Prod.ext htag hidx

lemma taggedDegreeTwoSimplexEdge_mem_union {s t : ℕ} (c : Fin t) (i : Fin (s + 1)) :
    taggedDegreeTwoSimplexEdge s t c i ∈ degreeTwoSimplexUnion s t := by
  exact Finset.mem_image.mpr ⟨(c, i), by simp, rfl⟩

/-- The tagged disjoint union has `t(s+1)` edges. -/
theorem card_degreeTwoSimplexUnion (s t : ℕ) (hs : 2 ≤ s) :
    (degreeTwoSimplexUnion s t).card = t * (s + 1) := by
  unfold degreeTwoSimplexUnion
  rw [Finset.card_image_of_injective _ (taggedDegreeTwoSimplexEdge_injective hs)]
  simp

/-- The tagged disjoint union is still `s`-uniform. -/
theorem degreeTwoSimplexUnion_uniform (s t : ℕ) :
    IsRUniform (degreeTwoSimplexUnion s t) s := by
  intro E hE
  rcases Finset.mem_image.mp hE with ⟨p, -, rfl⟩
  unfold taggedDegreeTwoSimplexEdge
  rw [Finset.card_image_of_injective]
  · simpa using card_completeGraphStar (m := s + 1) p.2
  · intro a b hab
    simpa using congrArg Prod.snd hab

theorem vertexDegree_degreeTwoSimplexUnion (s t : ℕ) (hs : 2 ≤ s)
    (x : Fin t × Finset (Fin (s + 1))) :
    vertexDegree' (degreeTwoSimplexUnion s t) x =
      vertexDegree' (completeGraphDualFamily (s + 1)) x.2 := by
  unfold vertexDegree' degreeTwoSimplexUnion completeGraphDualFamily
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ (taggedDegreeTwoSimplexEdge_injective hs)]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ (completeGraphStar_injective (by omega : 3 ≤ s + 1))]
  have hfilter :
      ((Finset.univ : Finset (Fin t × Fin (s + 1))).filter fun p =>
          x ∈ taggedDegreeTwoSimplexEdge s t p.1 p.2) =
        (((Finset.univ : Finset (Fin (s + 1))).filter fun i =>
            x.2 ∈ completeGraphStar (s + 1) i).image fun i => (x.1, i)) := by
    ext p
    constructor
    · intro hp
      have hpPred := (Finset.mem_filter.mp hp).2
      have hp' := (mem_taggedDegreeTwoSimplexEdge.1 hpPred)
      exact Finset.mem_image.mpr ⟨p.2, by simpa using hp'.2, by ext <;> simp [hp'.1]⟩
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨i, hi, hpi⟩
      have hfst : x.1 = p.1 := by simpa using congrArg Prod.fst hpi
      have hsnd : i = p.2 := by simpa using congrArg Prod.snd hpi
      exact Finset.mem_filter.mpr ⟨by simp,
        (mem_taggedDegreeTwoSimplexEdge).2 ⟨hfst, by simpa [hsnd] using hi⟩⟩
  rw [hfilter]
  rw [Finset.card_image_of_injective _ (by intro a b hab; exact congrArg Prod.snd hab)]

/-- The tagged disjoint union has maximum vertex degree at most `2`. -/
theorem degreeTwoSimplexUnion_maxVertexDegreeAtMost_two (s t : ℕ) (hs : 2 ≤ s) :
    MaxVertexDegreeAtMost (degreeTwoSimplexUnion s t) 2 := by
  intro x
  rw [vertexDegree_degreeTwoSimplexUnion s t hs x]
  exact completeGraphDualFamily_maxVertexDegreeAtMost_two (m := s + 1) (by omega) x.2

lemma disjoint_taggedDegreeTwoSimplexEdge_of_ne {s t : ℕ} {c d : Fin t}
    (hcd : c ≠ d) (i j : Fin (s + 1)) :
    Disjoint (taggedDegreeTwoSimplexEdge s t c i) (taggedDegreeTwoSimplexEdge s t d j) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hxc := (mem_taggedDegreeTwoSimplexEdge.1 hx).1
  have hxd := (mem_taggedDegreeTwoSimplexEdge.1 hy).1
  exact hcd (hxc.symm.trans hxd)

/-- The distinguished matching in the tagged disjoint union has one edge per copy. -/
theorem card_degreeTwoSimplexUnionMatching (s t : ℕ) (hs : 2 ≤ s) :
    (degreeTwoSimplexUnionMatching s t).card = t := by
  unfold degreeTwoSimplexUnionMatching
  rw [Finset.card_image_of_injective]
  · simp
  · intro c d hcd
    have hpair :
        ((c, (0 : Fin (s + 1))) : Fin t × Fin (s + 1)) = (d, 0) :=
      taggedDegreeTwoSimplexEdge_injective (s := s) (t := t) hs hcd
    exact congrArg Prod.fst hpair

/-- The distinguished matching is maximal in the tagged disjoint union. -/
theorem degreeTwoSimplexUnionMatching_isMaximalMatching (s t : ℕ) (hs : 2 ≤ s) :
    IsMaximalMatchingIn (degreeTwoSimplexUnion s t) (degreeTwoSimplexUnionMatching s t) := by
  refine
    { subset := ?_
      pairwiseDisjoint := ?_
      meets_every_edge := ?_ }
  · intro E hE
    rcases Finset.mem_image.mp hE with ⟨c, -, rfl⟩
    exact taggedDegreeTwoSimplexEdge_mem_union c 0
  · intro E F hE hF hne
    rcases Finset.mem_image.mp hE with ⟨c, -, rfl⟩
    rcases Finset.mem_image.mp hF with ⟨d, -, rfl⟩
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hne rfl
    exact disjoint_taggedDegreeTwoSimplexEdge_of_ne hcd 0 0
  · intro E hE
    rcases Finset.mem_image.mp hE with ⟨p, -, rfl⟩
    refine ⟨taggedDegreeTwoSimplexEdge s t p.1 0, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p.1, by simp, rfl⟩
    · have hm : 3 ≤ s + 1 := by omega
      have hnot :
          ¬ Disjoint (completeGraphStar (s + 1) p.2) (completeGraphStar (s + 1) 0) := by
        exact completeGraphDualFamily_pairwise_not_disjoint (m := s + 1) hm
          (by exact Finset.mem_image.mpr ⟨p.2, by simp, rfl⟩)
          (by exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩)
      rcases not_disjoint_iff.mp hnot with ⟨e, he_left, he_right⟩
      exact not_disjoint_iff.mpr ⟨(p.1, e),
        (mem_taggedDegreeTwoSimplexEdge).2 ⟨rfl, he_left⟩,
        (mem_taggedDegreeTwoSimplexEdge).2 ⟨rfl, he_right⟩⟩

/-- Disjoint unions of simplex kernels attain the degree-two bound with equality for every
matching size `t`. -/
theorem degreeTwoSimplexUnion_sharpness (s t : ℕ) (hs : 2 ≤ s) :
    IsRUniform (degreeTwoSimplexUnion s t) s ∧
      MaxVertexDegreeAtMost (degreeTwoSimplexUnion s t) 2 ∧
      IsMaximalMatchingIn (degreeTwoSimplexUnion s t) (degreeTwoSimplexUnionMatching s t) ∧
      (degreeTwoSimplexUnionMatching s t).card = t ∧
      (degreeTwoSimplexUnion s t).card =
        (s + 1) * (degreeTwoSimplexUnionMatching s t).card := by
  refine ⟨degreeTwoSimplexUnion_uniform s t,
    degreeTwoSimplexUnion_maxVertexDegreeAtMost_two s t hs,
    degreeTwoSimplexUnionMatching_isMaximalMatching s t hs,
    card_degreeTwoSimplexUnionMatching s t hs, ?_⟩
  rw [card_degreeTwoSimplexUnion s t hs, card_degreeTwoSimplexUnionMatching s t hs]
  ring

end FormalConjectures.Problems.Erdos.E20
