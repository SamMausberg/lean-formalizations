import FormalConjectures.Problems.Erdos.E20.Families.TransversalCounterexample
import FormalConjectures.Problems.Erdos.E20.Kernels.LeafStripping

namespace FormalConjectures.Problems.Erdos.E20

open Finset BigOperators

/-!
# Balanced Multislice Obstruction

This file records the formal core of the balanced-multislice obstruction from
`sunflower_selected_results.tex`.

The analytic estimates in the TeX note, such as Stirling asymptotics and the
`C_q / sqrt r` positive-density box upper bound, are not formalized here.  This
file records the exact finite object, its sunflower-free consequence, finite
degree/leaf-stripping facts, and a finite density-one obstruction for support
boxes.
-/

/-- Number of coordinates of a word carrying the symbol `a`. -/
def symbolCount {n q : ℕ} (x : Fin n → Fin q) (a : Fin q) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card

/-- A word is balanced if every symbol appears exactly `n / q` times. -/
def IsBalancedWord {n q : ℕ} (x : Fin n → Fin q) : Prop :=
  ∀ a : Fin q, symbolCount x a = n / q

instance instDecidableIsBalancedWord {n q : ℕ} (x : Fin n → Fin q) :
    Decidable (IsBalancedWord x) := by
  unfold IsBalancedWord
  infer_instance

/-- The balanced multislice in `[q]^n`. -/
def balancedWords (n q : ℕ) : Finset (Fin n → Fin q) :=
  Finset.univ.filter IsBalancedWord

@[simp] theorem mem_balancedWords {n q : ℕ} {x : Fin n → Fin q} :
    x ∈ balancedWords n q ↔ IsBalancedWord x := by
  simp [balancedWords]

/-- The transversal set family associated to the balanced multislice. -/
def balancedMultisliceFamily (n q : ℕ) : Finset (Finset (Fin n × Fin q)) :=
  transversalFamily (G := Fin q) (balancedWords n q)

@[simp] theorem card_balancedMultisliceFamily (n q : ℕ) :
    (balancedMultisliceFamily n q).card = (balancedWords n q).card := by
  simp [balancedMultisliceFamily]

/-- The balanced multislice is a subfamily of the full `q`-ary transversal code. -/
theorem balancedWords_subset_univ (n q : ℕ) :
    balancedWords n q ⊆ (Finset.univ : Finset (Fin n → Fin q)) := by
  intro x hx
  simp

/-- The trivial exponential upper bound behind the Stirling comparison:
the balanced slice is a subfamily of the full `q`-ary cube. -/
theorem card_balancedWords_le_univ (n q : ℕ) :
    (balancedWords n q).card ≤ q ^ n := by
  have hsubset :
      balancedWords n q ⊆ (Finset.univ : Finset (Fin n → Fin q)) :=
    balancedWords_subset_univ n q
  calc
    (balancedWords n q).card ≤ (Finset.univ : Finset (Fin n → Fin q)).card :=
      Finset.card_le_card hsubset
    _ = q ^ n := by simp

/-- The same ambient exponential bound for the transversal set family. -/
theorem card_balancedMultisliceFamily_le_pow (n q : ℕ) :
    (balancedMultisliceFamily n q).card ≤ q ^ n := by
  rw [card_balancedMultisliceFamily]
  exact card_balancedWords_le_univ n q

/-- The degree of a transversal vertex `(i,a)` in the balanced multislice is exactly the
number of balanced words whose `i`-th coordinate equals `a`. -/
theorem vertexDegree_balancedMultisliceFamily_eq_coordinateCount
    (n q : ℕ) (i : Fin n) (a : Fin q) :
    vertexDegree' (balancedMultisliceFamily n q) (i, a) =
      coordinateCount (G := Fin q) (balancedWords n q) i a := by
  classical
  have hfilter :
      (balancedMultisliceFamily n q).filter (fun e => (i, a) ∈ e) =
        ((balancedWords n q).filter fun x => x i = a).image transversalEdge := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨heC, hea⟩
      rcases Finset.mem_image.mp heC with ⟨x, hxC, rfl⟩
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hxC, mem_transversalEdge_iff.mp hea⟩, rfl⟩
    · intro he
      rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩,
          by simpa [mem_transversalEdge_iff] using (Finset.mem_filter.mp hx).2⟩
  unfold vertexDegree' coordinateCount
  calc
    ((balancedMultisliceFamily n q).filter (fun e => (i, a) ∈ e)).card
        = (((balancedWords n q).filter fun x => x i = a).image transversalEdge).card := by
          rw [hfilter]
    _ = ((balancedWords n q).filter fun x => x i = a).card := by
          exact Finset.card_image_of_injective _ transversalEdge_injective

/-- A finite sufficient condition for the balanced multislice to have no leaves:
if every coordinate-symbol fiber contains at least two balanced words, then every
ground vertex has degree at least two. -/
theorem nonLeafVertices_balancedMultisliceFamily_eq_univ_of_two_le_coordinateCount
    (n q : ℕ)
    (hdeg : ∀ i : Fin n, ∀ a : Fin q,
      2 ≤ coordinateCount (G := Fin q) (balancedWords n q) i a) :
    nonLeafVertices (balancedMultisliceFamily n q) = Finset.univ := by
  ext v
  constructor
  · intro _
    simp
  · intro _
    rcases v with ⟨i, a⟩
    have h : 2 ≤ vertexDegree' (balancedMultisliceFamily n q) (i, a) := by
      rw [vertexDegree_balancedMultisliceFamily_eq_coordinateCount]
      exact hdeg i a
    simpa [nonLeafVertices] using h

/-- Under the same finite no-leaf condition, one stripping round fixes every edge. -/
@[simp] theorem strippedEdge_balancedMultisliceFamily_of_two_le_coordinateCount
    (n q : ℕ)
    (hdeg : ∀ i : Fin n, ∀ a : Fin q,
      2 ≤ coordinateCount (G := Fin q) (balancedWords n q) i a)
    (e : Finset (Fin n × Fin q)) :
    strippedEdge (balancedMultisliceFamily n q) e = e := by
  rw [strippedEdge, nonLeafVertices_balancedMultisliceFamily_eq_univ_of_two_le_coordinateCount
    n q hdeg]
  simp

/-- Under the finite no-leaf condition, the balanced multislice is fixed by one-round
leaf stripping. -/
theorem strippedSupport_balancedMultisliceFamily_eq_of_two_le_coordinateCount
    (n q : ℕ)
    (hdeg : ∀ i : Fin n, ∀ a : Fin q,
      2 ≤ coordinateCount (G := Fin q) (balancedWords n q) i a) :
    strippedSupportFamily (balancedMultisliceFamily n q) = balancedMultisliceFamily n q := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, hfe⟩
    have hfe' : f = e := by
      simpa [strippedEdge_balancedMultisliceFamily_of_two_le_coordinateCount n q hdeg f]
        using hfe
    have hef : e = f := hfe'.symm
    simpa [hef] using hf
  · intro he
    exact Finset.mem_image.mpr
      ⟨e, he, strippedEdge_balancedMultisliceFamily_of_two_le_coordinateCount n q hdeg e⟩

/-- A coordinatewise support box in `[q]^n`, specified by allowed symbol sets `S i`. -/
def supportBoxWords (n q : ℕ) (S : Fin n → Finset (Fin q)) : Finset (Fin n → Fin q) :=
  Finset.univ.filter fun x => ∀ i, x i ∈ S i

@[simp] theorem mem_supportBoxWords {n q : ℕ} {S : Fin n → Finset (Fin q)}
    {x : Fin n → Fin q} :
    x ∈ supportBoxWords n q S ↔ ∀ i, x i ∈ S i := by
  simp [supportBoxWords]

/-- Live coordinates of a support box: coordinates with at least two available symbols. -/
def liveCoordinates {n q : ℕ} (S : Fin n → Finset (Fin q)) : Finset (Fin n) :=
  Finset.univ.filter fun i => 2 ≤ (S i).card

@[simp] theorem mem_liveCoordinates {n q : ℕ} {S : Fin n → Finset (Fin q)} {i : Fin n} :
    i ∈ liveCoordinates S ↔ 2 ≤ (S i).card := by
  simp [liveCoordinates]

/-- Exact cardinality of a finite support box. -/
noncomputable def supportBoxWordsEquiv {n q : ℕ} (S : Fin n → Finset (Fin q)) :
    ↥(supportBoxWords n q S) ≃ ((i : Fin n) → S i) where
  toFun x := fun i => ⟨x.1 i, (mem_supportBoxWords.mp x.2) i⟩
  invFun y := ⟨fun i => y i, by simp⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    funext i
    rfl

@[simp] theorem card_supportBoxWords {n q : ℕ} (S : Fin n → Finset (Fin q)) :
    (supportBoxWords n q S).card = ∏ i : Fin n, (S i).card := by
  classical
  rw [← Fintype.card_coe (supportBoxWords n q S)]
  simpa using Fintype.card_congr (supportBoxWordsEquiv S)

lemma symbolCount_update_ne {n q : ℕ} (x : Fin n → Fin q) (i : Fin n) (b : Fin q)
    (hb : b ≠ x i) :
    symbolCount (Function.update x i b) (x i) = symbolCount x (x i) - 1 := by
  classical
  let T : Finset (Fin n) := (Finset.univ.filter fun j => x j = x i)
  have hiT : i ∈ T := by simp [T]
  have hfilter :
      ((Finset.univ : Finset (Fin n)).filter fun j => Function.update x i b j = x i) =
        T.erase i := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [T, hb]
    · simp [T, hji]
  rw [symbolCount, hfilter, Finset.card_erase_of_mem hiT]
  rfl

lemma supportBoxWords.update_mem {n q : ℕ} {S : Fin n → Finset (Fin q)}
    {x : Fin n → Fin q} (hx : x ∈ supportBoxWords n q S) (i : Fin n) {b : Fin q}
    (hb : b ∈ S i) :
    Function.update x i b ∈ supportBoxWords n q S := by
  rw [mem_supportBoxWords] at hx ⊢
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using hb
  · simpa [hji] using hx j

/-- If a nonempty support box has a live coordinate and contains a balanced word, then it
also contains an unbalanced word.  This is the finite obstruction behind the stronger
`C_q / sqrt r` density estimate in the TeX note. -/
lemma supportBoxWords.exists_unbalanced_of_live {n q : ℕ} {S : Fin n → Finset (Fin q)}
    {x : Fin n → Fin q} (hxbox : x ∈ supportBoxWords n q S)
    (hxbal : x ∈ balancedWords n q) {i : Fin n} (hi : i ∈ liveCoordinates S) :
    ∃ y ∈ supportBoxWords n q S, y ∉ balancedWords n q := by
  classical
  have hcard : 1 < (S i).card := by
    have : 2 ≤ (S i).card := by simpa using hi
    omega
  rcases Finset.exists_mem_ne hcard (x i) with ⟨b, hbS, hbne⟩
  let y : Fin n → Fin q := Function.update x i b
  refine ⟨y, supportBoxWords.update_mem hxbox i hbS, ?_⟩
  intro hybal_mem
  have hxbal' : IsBalancedWord x := mem_balancedWords.mp hxbal
  have hybal' : IsBalancedWord y := mem_balancedWords.mp hybal_mem
  have hcount : symbolCount y (x i) = symbolCount x (x i) - 1 :=
    symbolCount_update_ne x i b hbne
  have hxcount : symbolCount x (x i) = n / q := hxbal' (x i)
  have hycount : symbolCount y (x i) = n / q := hybal' (x i)
  have hpos : 0 < symbolCount x (x i) := by
    rw [symbolCount]
    exact Finset.card_pos.mpr ⟨i, by simp⟩
  have hlt : symbolCount x (x i) - 1 < symbolCount x (x i) :=
    Nat.sub_one_lt (Nat.ne_of_gt hpos)
  rw [hycount, hxcount] at hcount
  have hlt' : n / q - 1 < n / q := by
    simpa [hxcount] using hlt
  rw [← hcount] at hlt'
  exact lt_irrefl _ hlt'

/-- No nonempty support box with a live coordinate can be contained in the balanced slice. -/
theorem supportBoxWords_not_subset_balancedWords_of_live {n q : ℕ}
    {S : Fin n → Finset (Fin q)}
    (hbox : (supportBoxWords n q S).Nonempty) (hlive : (liveCoordinates S).Nonempty) :
    ¬ supportBoxWords n q S ⊆ balancedWords n q := by
  rintro hsubset
  rcases hbox with ⟨x, hxbox⟩
  rcases hlive with ⟨i, hi⟩
  have hxbal : x ∈ balancedWords n q := hsubset hxbox
  rcases supportBoxWords.exists_unbalanced_of_live hxbox hxbal hi with ⟨y, hybox, hyNot⟩
  exact hyNot (hsubset hybox)

/-- Finite support-box obstruction: in any nonempty live support box, the balanced slice has
strictly smaller cardinality than the box. -/
theorem card_balancedWords_inter_supportBox_lt_card_supportBox_of_live {n q : ℕ}
    {S : Fin n → Finset (Fin q)}
    (hbox : (supportBoxWords n q S).Nonempty) (hlive : (liveCoordinates S).Nonempty) :
    ((supportBoxWords n q S).filter fun x => x ∈ balancedWords n q).card <
      (supportBoxWords n q S).card := by
  classical
  have hproper :
      ((supportBoxWords n q S).filter fun x => x ∈ balancedWords n q) ⊂
        supportBoxWords n q S := by
    rw [Finset.filter_ssubset]
    by_contra h
    push Not at h
    exact supportBoxWords_not_subset_balancedWords_of_live hbox hlive h
  exact Finset.card_lt_card hproper

/-- Rational-density version of the finite support-box obstruction: a nonempty live support
box cannot have balanced density `1`. -/
theorem balancedWords_supportBox_density_lt_one_of_live {n q : ℕ}
    {S : Fin n → Finset (Fin q)}
    (hbox : (supportBoxWords n q S).Nonempty) (hlive : (liveCoordinates S).Nonempty) :
    (((supportBoxWords n q S).filter fun x => x ∈ balancedWords n q).card : ℚ) /
        (supportBoxWords n q S).card < 1 := by
  have hlt :=
    card_balancedWords_inter_supportBox_lt_card_supportBox_of_live
      (S := S) hbox hlive
  have hboxpos : 0 < (supportBoxWords n q S).card := Finset.card_pos.mpr hbox
  have hboxpos_rat : (0 : ℚ) < (supportBoxWords n q S).card := by
    exact_mod_cast hboxpos
  have hlt_rat :
      (((supportBoxWords n q S).filter fun x => x ∈ balancedWords n q).card : ℚ) <
        (supportBoxWords n q S).card := by
    exact_mod_cast hlt
  rw [div_lt_one hboxpos_rat]
  exact hlt_rat

/-- Core sunflower-free fact for the balanced multislice obstruction.

If the alphabet has fewer than `k` symbols, every transversal family over that
alphabet is `k`-sunflower-free.  The balanced multislice is one such family,
with the intended specialization `q = k - 1`.
-/
theorem balancedMultislice_sunflowerFree_of_q_lt_k
    (n q k : ℕ) (hk : 2 ≤ k) (hqk : q < k) :
    SunflowerFree (balancedMultisliceFamily n q) k := by
  simpa [balancedMultisliceFamily] using
    (transversalFamily_sunflowerFree_of_card_lt
      (G := Fin q) (C := balancedWords n q) hk (by simpa using hqk))

/-- Specialization to the TeX notation `q = k - 1`. -/
theorem balancedMultislice_sunflowerFree
    (n k : ℕ) (hk : 2 ≤ k) :
    SunflowerFree (balancedMultisliceFamily n (k - 1)) k := by
  apply balancedMultislice_sunflowerFree_of_q_lt_k
  · exact hk
  · omega

end FormalConjectures.Problems.Erdos.E20
