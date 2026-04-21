import Mathlib
import FormalConjectures.Problems.Erdos.E20.Families.Counterexample

open Finset BigOperators

namespace FormalConjectures.Problems.Erdos.E20

/-!
# Transversal Counterexample Family

This file records the transversal obstruction from the E20 branch note:

* `σ` in the transversal world depends only on one-coordinate marginals;
* if the alphabet has size `< k`, every transversal family is automatically
  `k`-sunflower-free;
* the parity slice `Σ_i x_i = 0` is an exact minimizer for `σ`.
-/

section Transversal

variable {G : Type*} [DecidableEq G] [Fintype G]

/-- The transversal edge associated to a word `x : G^r`. -/
def transversalEdge {r : ℕ} (x : Fin r → G) : Finset (Fin r × G) :=
  Finset.univ.image fun i => (i, x i)

/-- The transversal family associated to a code `C ⊆ G^r`. -/
def transversalFamily {r : ℕ} (C : Finset (Fin r → G)) : Finset (Finset (Fin r × G)) :=
  C.image transversalEdge

/-- The number of codewords with coordinate `i` equal to `a`. -/
def coordinateCount {r : ℕ} (C : Finset (Fin r → G)) (i : Fin r) (a : G) : ℕ :=
  (C.filter fun x => x i = a).card

/-- The corresponding one-coordinate marginal. -/
noncomputable def coordinateMarginal {r : ℕ} (C : Finset (Fin r → G)) (i : Fin r) (a : G) : ℚ :=
  (coordinateCount C i a : ℚ) / C.card

/-- The transversal `σ` statistic, defined directly from one-coordinate marginals. -/
noncomputable def transversalSigma {r : ℕ} (C : Finset (Fin r → G)) : ℚ :=
  (1 / r) * ∑ i : Fin r, ∑ a : G, (coordinateMarginal C i a) ^ 2

@[simp] theorem mem_transversalEdge_iff {r : ℕ} {x : Fin r → G} {i : Fin r} {a : G} :
    (i, a) ∈ transversalEdge x ↔ x i = a := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨j, -, hj⟩
    have hij : j = i := by simpa using congrArg Prod.fst hj
    subst hij
    simpa using congrArg Prod.snd hj
  · intro h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [h]⟩

theorem transversalEdge_injective {r : ℕ} :
    Function.Injective (fun x : Fin r → G => transversalEdge x) := by
  intro x y hxy
  funext i
  have hmem : (i, x i) ∈ transversalEdge y := by
    simpa [hxy] using
      (show (i, x i) ∈ transversalEdge x by simp [mem_transversalEdge_iff])
  have hyx : y i = x i := by
    simpa [mem_transversalEdge_iff] using hmem
  exact hyx.symm

@[simp] theorem card_transversalFamily {r : ℕ} (C : Finset (Fin r → G)) :
    (transversalFamily C).card = C.card := by
  unfold transversalFamily
  exact Finset.card_image_of_injective _ transversalEdge_injective

theorem sum_coordinateCount_eq_card {r : ℕ} (C : Finset (Fin r → G)) (i : Fin r) :
    ∑ a : G, coordinateCount C i a = C.card := by
  classical
  have hdisj :
      ((Finset.univ : Finset G) : Set G).PairwiseDisjoint
        (fun a => C.filter fun x => x i = a) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.2 ?_
    intro x hxa hxb
    exact hab ((Finset.mem_filter.mp hxa).2.symm.trans (Finset.mem_filter.mp hxb).2)
  calc
    ∑ a : G, coordinateCount C i a
        = ∑ a : G, (C.filter fun x => x i = a).card := by simp [coordinateCount]
    _ = ((Finset.univ : Finset G).biUnion fun a => C.filter fun x => x i = a).card := by
        symm
        exact Finset.card_biUnion hdisj
    _ = C.card := by
        congr
        ext x
        simp

theorem sum_coordinateMarginal_eq_one {r : ℕ} (C : Finset (Fin r → G)) (hC : C.Nonempty)
    (i : Fin r) :
    ∑ a : G, coordinateMarginal C i a = 1 := by
  have hcard : (C.card : ℚ) ≠ 0 := by
    exact_mod_cast hC.card_ne_zero
  calc
    ∑ a : G, coordinateMarginal C i a
        = (∑ a : G, (coordinateCount C i a : ℚ)) / C.card := by
            simp [coordinateMarginal, Finset.sum_div]
    _ = 1 := by
        have hcount : (∑ a : G, (coordinateCount C i a : ℚ)) = C.card := by
          exact_mod_cast sum_coordinateCount_eq_card C i
        rw [hcount]
        field_simp [hcard]

theorem transversalFamily_sunflowerFree_of_card_lt {r k : ℕ}
    (C : Finset (Fin r → G)) (hk : 2 ≤ k) (hG : Fintype.card G < k) :
    SunflowerFree (transversalFamily C) k := by
  classical
  intro A hA hInj hSun
  let t0 : Fin k := ⟨0, by omega⟩
  let t1 : Fin k := ⟨1, by omega⟩
  choose x hxC hxA using fun t => Finset.mem_image.mp (hA t)
  have hcoord : ∀ i : Fin r, ∀ t : Fin k, x t i = x t0 i := by
    intro i t
    obtain ⟨u, v, huv, huvEq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun s : Fin k => x s i) (by simpa using hG)
    have ht0 : x t0 i = x u i := by
      by_cases ht0u : t0 = u
      · simpa [t0, ht0u] using huvEq.symm
      · have hmem_uv : (i, x u i) ∈ A u ∩ A v := by
          rw [← hxA u, ← hxA v]
          simp [mem_transversalEdge_iff, huvEq]
        have hEqInter0 : A u ∩ A v = A u ∩ A t0 := by
          exact hSun huv (by
            intro h
            exact ht0u h.symm)
        have hmem_u0 : (i, x u i) ∈ A u ∩ A t0 := by
          simpa [hEqInter0] using hmem_uv
        rw [← hxA u, ← hxA t0] at hmem_u0
        simpa [mem_transversalEdge_iff] using (Finset.mem_inter.mp hmem_u0).2
    by_cases htu : t = u
    · simpa [htu] using ht0.symm
    · have hmem_uv : (i, x u i) ∈ A u ∩ A v := by
        rw [← hxA u, ← hxA v]
        simp [mem_transversalEdge_iff, huvEq]
      have hEqInter : A u ∩ A v = A u ∩ A t := by
        exact hSun huv (by
          intro h
          exact htu h.symm)
      have hmem_ut : (i, x u i) ∈ A u ∩ A t := by
        simpa [hEqInter] using hmem_uv
      have hxt : x t i = x u i := by
        rw [← hxA u, ← hxA t] at hmem_ut
        simpa [mem_transversalEdge_iff] using (Finset.mem_inter.mp hmem_ut).2
      exact hxt.trans ht0.symm
  have hEq01 : A t0 = A t1 := by
    rw [← hxA t0, ← hxA t1]
    exact congrArg transversalEdge <| by
      funext i
      simpa [t1] using (hcoord i t1).symm
  have ht01 : t0 ≠ t1 := by
    intro h
    have : (0 : ℕ) = 1 := by
      exact congrArg Fin.val h
    omega
  exact ht01 (hInj hEq01)

end Transversal

section SumSlices

variable {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G]

/-- The affine slice of `G^r` cut out by a fixed coordinate sum. -/
def sumSlice {r : ℕ} (b : G) : Finset (Fin r → G) :=
  Finset.univ.filter fun x => ∑ i, x i = b

/-- The parity slice `Σ_i x_i = 0`. -/
def paritySlice {r : ℕ} : Finset (Fin r → G) :=
  sumSlice (r := r) 0

noncomputable def sumSliceEquiv (n : ℕ) (b : G) (p : Fin (n + 1)) :
    ↥(sumSlice (G := G) (r := n + 1) b) ≃ (Fin n → G) where
  toFun x := p.removeNth x.1
  invFun y :=
    ⟨p.insertNth (b - ∑ j, y j) y, by
      simp [sumSlice, Fin.sum_insertNth, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]⟩
  left_inv x := by
    have hxsum : ∑ i, x.1 i = b := by
      exact (Finset.mem_filter.mp x.2).2
    have hxcoord : x.1 p = b - ∑ j, p.removeNth x.1 j := by
      apply eq_sub_iff_add_eq.mpr
      simpa [hxsum, add_assoc] using (Fin.add_sum_removeNth p x.1)
    apply Subtype.ext
    calc
      p.insertNth (b - ∑ j, p.removeNth x.1 j) (p.removeNth x.1) =
          p.insertNth (x.1 p) (p.removeNth x.1) := by simp [hxcoord]
      _ = x.1 := by simpa using (Fin.insertNth_self_removeNth p x.1)
  right_inv y := by
    simp

@[simp] theorem card_sumSlice (n : ℕ) (b : G) :
    (sumSlice (G := G) (r := n + 1) b).card = Fintype.card G ^ n := by
  classical
  rw [← Fintype.card_coe (sumSlice (G := G) (r := n + 1) b)]
  simpa using Fintype.card_congr (sumSliceEquiv (G := G) n b 0)

/-- A sum-slice on an arbitrary finite index type is equivalent to the standard `Fin`-indexed
sum-slice. -/
noncomputable def sumSliceEquivType (ι : Type*) [DecidableEq ι] [Fintype ι] (b : G) :
    ↥(Finset.univ.filter fun x : ι → G => ∑ i, x i = b) ≃
      ↥(sumSlice (G := G) (r := Fintype.card ι) b) where
  toFun x := by
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let reindex : (ι → G) ≃ (Fin (Fintype.card ι) → G) :=
      Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => G) e
    refine ⟨reindex x.1, ?_⟩
    have hx : ∑ i : ι, x.1 i = b := by
      exact (Finset.mem_filter.mp x.2).2
    have hsum :
        ∑ i : Fin (Fintype.card ι), reindex x.1 i = ∑ i : ι, x.1 i := by
      simpa [reindex, e] using
        (Fintype.sum_equiv e (fun i : ι => x.1 i)
          (fun i : Fin (Fintype.card ι) => reindex x.1 i) fun i => by
            simp [reindex, e]).symm
    refine Finset.mem_filter.mpr ?_
    constructor
    · simp
    · rw [hsum, hx]
  invFun x := by
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let reindex : (ι → G) ≃ (Fin (Fintype.card ι) → G) :=
      Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => G) e
    refine ⟨reindex.symm x.1, ?_⟩
    have hx : ∑ i : Fin (Fintype.card ι), x.1 i = b := by
      exact (Finset.mem_filter.mp x.2).2
    have hsum :
        ∑ i : ι, reindex.symm x.1 i = ∑ i : Fin (Fintype.card ι), x.1 i := by
      simpa [reindex, e] using
        (Fintype.sum_equiv e.symm (fun i : Fin (Fintype.card ι) => x.1 i)
          (fun i : ι => reindex.symm x.1 i) fun i => by
            simp [reindex, e]).symm
    refine Finset.mem_filter.mpr ?_
    constructor
    · simp
    · rw [hsum, hx]
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- The cardinality of a total-sum slice on an arbitrary nonempty finite index type. -/
@[simp] theorem card_sumSlice_fintype (ι : Type*) [DecidableEq ι] [Fintype ι]
    (b : G) (hι : 0 < Fintype.card ι) :
    (Finset.univ.filter fun x : ι → G => ∑ i, x i = b).card =
      Fintype.card G ^ (Fintype.card ι - 1) := by
  classical
  let n : ℕ := Fintype.card ι - 1
  have hcard : Fintype.card ι = n + 1 := by
    subst n
    omega
  calc
    (Finset.univ.filter fun x : ι → G => ∑ i, x i = b).card
        = (sumSlice (G := G) (r := Fintype.card ι) b).card := by
            rw [← Fintype.card_coe (Finset.univ.filter fun x : ι → G => ∑ i, x i = b),
              ← Fintype.card_coe (sumSlice (G := G) (r := Fintype.card ι) b)]
            exact Fintype.card_congr (sumSliceEquivType (G := G) ι b)
    _ = Fintype.card G ^ n := by
        rw [hcard]
        simpa [n] using (card_sumSlice (G := G) n b)

/-- The fiber of a sum-slice after fixing the coordinates in a finset `S`.

This is the arbitrary-subset version of the prefix fiber: we pin every coordinate in `S` and
leave the complementary coordinates free, subject to the total-sum constraint. -/
def restrictionFiber {r : ℕ} (S : Finset (Fin r)) (b : G) (a : S → G) :
    Finset (Fin r → G) :=
  (sumSlice (G := G) (r := r) b).filter fun x => ∀ i : S, x i = a i

omit [DecidableEq G] [Fintype G] in
private theorem sum_univ_eq_sum_subtype_add_sum_compl {r : ℕ} (S : Finset (Fin r))
    (f : Fin r → G) :
    ∑ i : Fin r, f i = (∑ i : S, f i) + ∑ i : (Sᶜ : Finset (Fin r)), f i := by
  calc
    ∑ i : Fin r, f i = (∑ i ∈ S, f i) + ∑ i ∈ Sᶜ, f i := by
      rw [Finset.sum_add_sum_compl]
    _ = (∑ i : S, f i) + ∑ i : (Sᶜ : Finset (Fin r)), f i := by
      rw [Finset.sum_coe_sort, Finset.sum_coe_sort]

/-- After fixing an arbitrary coordinate set `S` in a sum-slice, the remaining fiber is
equivalent to a lower-dimensional sum-slice on the complement of `S`. -/
noncomputable def restrictionFiberEquiv {r : ℕ} (S : Finset (Fin r)) (b : G)
    (a : S → G) :
    ↥(restrictionFiber (G := G) S b a) ≃
      ↥(Finset.univ.filter fun y : (Sᶜ : Finset (Fin r)) → G =>
        ∑ i, y i = b - ∑ i, a i) where
  toFun x := by
    refine ⟨fun i => x.1 i, ?_⟩
    rcases Finset.mem_filter.mp x.2 with ⟨hxmem, hfixed⟩
    have hxsum : ∑ i : Fin r, x.1 i = b := by
      exact (Finset.mem_filter.mp hxmem).2
    have hSsum : ∑ i : S, x.1 i = ∑ i : S, a i := by
      exact Finset.sum_congr rfl (fun i _ => hfixed i)
    have hsplit := sum_univ_eq_sum_subtype_add_sum_compl (G := G) S x.1
    have htail : ∑ i : (Sᶜ : Finset (Fin r)), x.1 i = b - ∑ i : S, a i := by
      apply eq_sub_iff_add_eq.mpr
      calc
        (∑ i : (Sᶜ : Finset (Fin r)), x.1 i) + ∑ i : S, a i
            = (∑ i : S, a i) + ∑ i : (Sᶜ : Finset (Fin r)), x.1 i := by
              abel
        _ = (∑ i : S, x.1 i) + ∑ i : (Sᶜ : Finset (Fin r)), x.1 i := by
              rw [hSsum]
        _ = ∑ i : Fin r, x.1 i := by simpa [add_comm] using hsplit.symm
        _ = b := hxsum
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htail⟩
  invFun y := by
    let z : Fin r → G := fun i =>
      if h : i ∈ S then a ⟨i, h⟩ else y.1 ⟨i, Finset.mem_compl.mpr h⟩
    refine ⟨z, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · have hysum : ∑ i : (Sᶜ : Finset (Fin r)), y.1 i = b - ∑ i : S, a i := by
        exact (Finset.mem_filter.mp y.2).2
      have hSsum : ∑ i : S, z i = ∑ i : S, a i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [z, i.2]
      have hCsum :
          ∑ i : (Sᶜ : Finset (Fin r)), z i =
            ∑ i : (Sᶜ : Finset (Fin r)), y.1 i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        have hnot : (i : Fin r) ∉ S := Finset.mem_compl.mp i.2
        simp [z, hnot]
      have hsplit := sum_univ_eq_sum_subtype_add_sum_compl (G := G) S z
      have hzsum : ∑ i : Fin r, z i = b := by
        calc
          ∑ i : Fin r, z i = (∑ i : S, z i) + ∑ i : (Sᶜ : Finset (Fin r)), z i :=
            hsplit
          _ = (∑ i : S, a i) + ∑ i : (Sᶜ : Finset (Fin r)), y.1 i := by
              rw [hSsum, hCsum]
          _ = (∑ i : S, a i) + (b - ∑ i : S, a i) := by rw [hysum]
          _ = b := by abel
      simpa [sumSlice] using hzsum
    · intro i
      simp [z, i.2]
  left_inv x := by
    rcases Finset.mem_filter.mp x.2 with ⟨_, hfixed⟩
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [hi, (hfixed ⟨i, hi⟩).symm]
    · simp [hi]
  right_inv y := by
    apply Subtype.ext
    funext i
    have hnot : (i : Fin r) ∉ S := Finset.mem_compl.mp i.2
    simp [hnot]

/-- Fixing any proper coordinate subset of a sum-slice leaves exactly one affine constraint on
the complementary coordinates. -/
@[simp] theorem card_restrictionFiber {r : ℕ} (S : Finset (Fin r)) (b : G)
    (a : S → G) (hS : S.card < r) :
    (restrictionFiber (G := G) S b a).card = Fintype.card G ^ (r - S.card - 1) := by
  classical
  let T : Finset (Fin r) := Sᶜ
  have hTpos : 0 < Fintype.card ↥T := by
    change 0 < Fintype.card ↥(Sᶜ : Finset (Fin r))
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  have hTcard : Fintype.card ↥T = r - S.card := by
    change Fintype.card ↥(Sᶜ : Finset (Fin r)) = r - S.card
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  calc
    (restrictionFiber (G := G) S b a).card
        = Fintype.card ↥(restrictionFiber (G := G) S b a) := by
          rw [Fintype.card_coe]
    _ = Fintype.card ↥(Finset.univ.filter fun y : T → G =>
          ∑ i, y i = b - ∑ i, a i) := by
        exact Fintype.card_congr (restrictionFiberEquiv (G := G) S b a)
    _ = (Finset.univ.filter fun y : T → G => ∑ i, y i = b - ∑ i, a i).card := by
        rw [Fintype.card_coe]
    _ = Fintype.card G ^ (Fintype.card ↥T - 1) := by
        simpa using card_sumSlice_fintype (G := G) T (b - ∑ i : S, a i) hTpos
    _ = Fintype.card G ^ (r - S.card - 1) := by
        rw [hTcard]

/-- Every prescribed pattern on a proper coordinate subset occurs in the corresponding
sum-slice. -/
theorem restrictionFiber_nonempty_of_card_lt {r : ℕ} (S : Finset (Fin r)) (b : G)
    (a : S → G) (hS : S.card < r) :
    (restrictionFiber (G := G) S b a).Nonempty := by
  rw [← Finset.card_pos, card_restrictionFiber (G := G) S b a hS]
  exact Nat.pow_pos (Fintype.card_pos_iff.mpr ⟨0⟩)

/-- The projection of a sum-slice onto any proper coordinate subset is onto. -/
theorem sumSlice_restriction_surjective {r : ℕ} (S : Finset (Fin r)) (b : G)
    (a : S → G) (hS : S.card < r) :
    ∃ x ∈ sumSlice (G := G) (r := r) b, ∀ i : S, x i = a i := by
  rcases restrictionFiber_nonempty_of_card_lt (G := G) S b a hS with ⟨x, hx⟩
  rcases Finset.mem_filter.mp hx with ⟨hxsum, hfixed⟩
  exact ⟨x, hxsum, hfixed⟩

/-- The fiber of a sum-slice after fixing an initial block of `s` coordinates.

This is the prefix-specialized version of the higher-order marginal fibers discussed in the user's
informal parity-slice obstruction: we pin the first `s` coordinates and leave the remaining
`n + 1` coordinates free subject to the total-sum constraint. -/
def prefixFiber (s n : ℕ) (b : G) (a : Fin s → G) : Finset (Fin (s + (n + 1)) → G) :=
  (sumSlice (G := G) (r := s + (n + 1)) b).filter
    fun x => ∀ i : Fin s, x (Fin.castAdd (n + 1) i) = a i

/-- After fixing an initial block of `s` coordinates in a sum-slice, the remaining fiber is
equivalent to a lower-dimensional sum-slice on the remaining `n + 1` coordinates.

This is the formal finite-dimensional version of the user's statement that parity/code slices have
all low-order marginals equal to product: once a bounded set of coordinates is fixed, one free
coordinate still absorbs the remaining sum constraint. -/
noncomputable def prefixFiberEquiv (s n : ℕ) (b : G) (a : Fin s → G) :
    ↥(prefixFiber (G := G) s n b a) ≃
      ↥(sumSlice (G := G) (r := n + 1) (b - ∑ i, a i)) where
  toFun x := by
    refine ⟨fun j => x.1 (Fin.natAdd s j), ?_⟩
    rcases Finset.mem_filter.mp x.2 with ⟨hxsum_mem, hprefix⟩
    have hxsum : ∑ i, x.1 i = b := by
      exact (Finset.mem_filter.mp hxsum_mem).2
    have hprefixSum :
        ∑ i : Fin s, x.1 (Fin.castAdd (n + 1) i) = ∑ i : Fin s, a i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [hprefix i]
    have htail :
        ∑ j : Fin (n + 1), x.1 (Fin.natAdd s j) = b - ∑ i : Fin s, a i := by
      apply eq_sub_iff_add_eq.mpr
      calc
        (∑ j : Fin (n + 1), x.1 (Fin.natAdd s j)) + ∑ i : Fin s, a i
            = (∑ i : Fin s, a i) + ∑ j : Fin (n + 1), x.1 (Fin.natAdd s j) := by
                  abel
        _ = (∑ i : Fin s, x.1 (Fin.castAdd (n + 1) i)) +
                ∑ j : Fin (n + 1), x.1 (Fin.natAdd s j) := by
                  rw [hprefixSum]
        _ = (∑ i : Fin (s + (n + 1)), x.1 i) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Fin.sum_univ_add (fun i : Fin (s + (n + 1)) => x.1 i)).symm
        _ = b := hxsum
    simpa [sumSlice] using htail
  invFun y := by
    refine ⟨Fin.append a y.1, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · have hy : ∑ i : Fin (n + 1), y.1 i = b - ∑ i : Fin s, a i := by
        exact (Finset.mem_filter.mp y.2).2
      have happ :
          ∑ i : Fin (s + (n + 1)), Fin.append a y.1 i =
            (∑ i : Fin s, a i) + ∑ j : Fin (n + 1), y.1 j := by
        simpa [Fin.append_left, Fin.append_right] using
          (Fin.sum_univ_add (fun i : Fin (s + (n + 1)) => Fin.append a y.1 i))
      have hsum : ∑ i : Fin (s + (n + 1)), Fin.append a y.1 i = b := by
        calc
          ∑ i : Fin (s + (n + 1)), Fin.append a y.1 i
              = (∑ i : Fin s, a i) + ∑ j : Fin (n + 1), y.1 j := happ
          _ = (∑ i : Fin s, a i) + (b - ∑ i : Fin s, a i) := by rw [hy]
          _ = b := by abel
      simpa [sumSlice] using hsum
    · intro i
      simp [Fin.append_left]
  left_inv x := by
    rcases Finset.mem_filter.mp x.2 with ⟨_, hprefix⟩
    apply Subtype.ext
    calc
      Fin.append a (fun j => x.1 (Fin.natAdd s j))
          = Fin.append (fun i => x.1 (Fin.castAdd (n + 1) i))
              (fun j => x.1 (Fin.natAdd s j)) := by
                congr
                funext i
                exact (hprefix i).symm
      _ = x.1 := by
            simpa using (Fin.append_castAdd_natAdd (f := x.1))
  right_inv y := by
    apply Subtype.ext
    funext j
    simp [Fin.append_right]

/-- The cardinality of a prefix fiber in a sum-slice.

This is the prefix-block version of the user's "all proper-coordinate marginals are uniform"
count for parity/code slices. -/
@[simp] theorem card_prefixFiber (s n : ℕ) (b : G) (a : Fin s → G) :
    (prefixFiber (G := G) s n b a).card = Fintype.card G ^ n := by
  classical
  rw [← Fintype.card_coe (prefixFiber (G := G) s n b a)]
  simpa using Fintype.card_congr (prefixFiberEquiv (G := G) s n b a)

noncomputable def sumSliceFiberEquiv (n : ℕ) (b : G) (p : Fin (n + 2)) (a : G) :
    ↥({x ∈ sumSlice (G := G) (r := n + 2) b | x p = a}) ≃
      ↥(sumSlice (G := G) (r := n + 1) (b - a)) where
  toFun x := by
    refine ⟨p.removeNth x.1, ?_⟩
    rcases Finset.mem_filter.mp x.2 with ⟨hxsum_mem, hxp⟩
    have hxsum : ∑ i, x.1 i = b := by
      exact (Finset.mem_filter.mp hxsum_mem).2
    have hremoved : ∑ j, p.removeNth x.1 j = b - a := by
      apply eq_sub_iff_add_eq.mpr
      simpa [hxsum, hxp, add_assoc, add_comm, add_left_comm] using (Fin.add_sum_removeNth p x.1)
    simpa [sumSlice] using hremoved
  invFun y := by
    have hy : ∑ i, y.1 i = b - a := by
      exact (Finset.mem_filter.mp y.2).2
    refine ⟨p.insertNth a y.1, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · simpa [sumSlice, hy, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (Fin.sum_insertNth p a y.1)
    · simp
  left_inv x := by
    rcases Finset.mem_filter.mp x.2 with ⟨_, hxp⟩
    apply Subtype.ext
    calc
      p.insertNth a (p.removeNth x.1) = p.insertNth (x.1 p) (p.removeNth x.1) := by
        simp [hxp]
      _ = x.1 := by simpa using (Fin.insertNth_self_removeNth p x.1)
  right_inv y := by
    apply Subtype.ext
    simp

@[simp] theorem card_sumSlice_filter_eq (n : ℕ) (b : G) (p : Fin (n + 2)) (a : G) :
    ({x ∈ sumSlice (G := G) (r := n + 2) b | x p = a}).card = Fintype.card G ^ n := by
  classical
  rw [← Fintype.card_coe ({x ∈ sumSlice (G := G) (r := n + 2) b | x p = a})]
  simpa using Fintype.card_congr (sumSliceFiberEquiv (G := G) n b p a)

@[simp] theorem card_paritySlice (n : ℕ) :
    (paritySlice (G := G) (r := n + 1)).card = Fintype.card G ^ n := by
  simpa [paritySlice] using card_sumSlice (G := G) n (0 : G)

/-- Cardinality of a nonzero-dimensional parity slice, indexed by the actual dimension. -/
@[simp] theorem card_paritySlice_of_pos {r : ℕ} (hr : 0 < r) :
    (paritySlice (G := G) (r := r)).card = Fintype.card G ^ (r - 1) := by
  have hrw : r = (r - 1) + 1 := by omega
  calc
    (paritySlice (G := G) (r := r)).card
        = (paritySlice (G := G) (r := (r - 1) + 1)).card := by
          exact congrArg (fun m => (paritySlice (G := G) (r := m)).card) hrw
    _ = Fintype.card G ^ (r - 1) := card_paritySlice (G := G) (r - 1)

/-- The arbitrary proper-subset fiber count for the parity slice. -/
@[simp] theorem card_paritySlice_restrictionFiber {r : ℕ} (S : Finset (Fin r))
    (a : S → G) (hS : S.card < r) :
    (restrictionFiber (G := G) S 0 a).card = Fintype.card G ^ (r - S.card - 1) := by
  simpa using card_restrictionFiber (G := G) S (0 : G) a hS

/-- The projection of the parity slice onto any proper coordinate subset is all of `G^S`. -/
theorem paritySlice_restriction_surjective {r : ℕ} (S : Finset (Fin r))
    (a : S → G) (hS : S.card < r) :
    ∃ x ∈ paritySlice (G := G) (r := r), ∀ i : S, x i = a i := by
  simpa [paritySlice] using sumSlice_restriction_surjective (G := G) S (0 : G) a hS

/-- Every proper-coordinate marginal of the parity slice is exactly uniform. -/
theorem paritySlice_restriction_uniform {r : ℕ} (S : Finset (Fin r))
    (a : S → G) (hS : S.card < r) :
    ((restrictionFiber (G := G) S 0 a).card : ℚ) /
        (paritySlice (G := G) (r := r)).card =
      1 / (Fintype.card G : ℚ) ^ S.card := by
  let q : ℚ := Fintype.card G
  have hq : q ≠ 0 := by
    norm_num [q]
  have hr : 0 < r := by omega
  rw [card_paritySlice_of_pos (G := G) hr, card_paritySlice_restrictionFiber (G := G) S a hS]
  have hpow : r - 1 = S.card + (r - S.card - 1) := by omega
  have hratio : q ^ (r - S.card - 1) / q ^ (r - 1) = 1 / q ^ S.card := by
    rw [hpow, pow_add]
    field_simp [hq, pow_ne_zero _ hq]
  simpa [q, Nat.cast_pow] using hratio

@[simp] theorem paritySlice_coordinateCount (n : ℕ) (p : Fin (n + 2)) (a : G) :
    coordinateCount (paritySlice (G := G) (r := n + 2)) p a = Fintype.card G ^ n := by
  unfold coordinateCount paritySlice
  simpa [sumSlice] using card_sumSlice_filter_eq (G := G) n (0 : G) p a

theorem paritySlice_coordinateMarginal (n : ℕ) (p : Fin (n + 2)) (a : G) :
    coordinateMarginal (paritySlice (G := G) (r := n + 2)) p a =
      1 / Fintype.card G := by
  let q : ℚ := Fintype.card G
  have hq : q ≠ 0 := by
    norm_num [q]
  rw [coordinateMarginal, paritySlice_coordinateCount, card_paritySlice]
  norm_num [q, Nat.cast_pow]
  rw [pow_succ]
  field_simp [hq]

/-- Fixing the first `s` coordinates of the parity slice leaves a fiber of cardinality
`|G|^n` in dimension `s + n + 1`.

This is a proved higher-order version of the user's parity-slice obstruction: every bounded
prefix marginal is exactly uniform. -/
@[simp] theorem card_paritySlice_prefixFiber (s n : ℕ) (a : Fin s → G) :
    (prefixFiber (G := G) s n 0 a).card = Fintype.card G ^ n := by
  simpa [paritySlice] using card_prefixFiber (G := G) s n (0 : G) a

/-- The prefix marginal of the parity slice is uniform: fixing the first `s` coordinates to any
pattern has probability `|G|^{-s}`.

This is the formal prefix-block analogue of the user's statement that parity slices have all
bounded-order marginals equal to the ambient product marginal. -/
theorem paritySlice_prefix_uniform (s n : ℕ) (a : Fin s → G) :
    ((prefixFiber (G := G) s n 0 a).card : ℚ) /
        (paritySlice (G := G) (r := s + (n + 1))).card =
      1 / (Fintype.card G : ℚ) ^ s := by
  let q : ℚ := Fintype.card G
  have hq : q ≠ 0 := by
    norm_num [q]
  rw [card_paritySlice, card_paritySlice_prefixFiber]
  have hs : q ^ s ≠ 0 := pow_ne_zero _ hq
  have hn : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hpow : q ^ n / q ^ (s + n) = 1 / q ^ s := by
    rw [pow_add]
    field_simp [hq, hs, hn]
  simpa [q, Nat.cast_pow] using hpow

theorem paritySlice_transversalSigma (n : ℕ) :
    transversalSigma (paritySlice (G := G) (r := n + 2)) =
      1 / Fintype.card G := by
  unfold transversalSigma
  simp_rw [paritySlice_coordinateMarginal]
  rw [Finset.sum_const, Finset.card_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  let q : ℚ := Fintype.card G
  have hq : q ≠ 0 := by
    norm_num [q]
  field_simp [q, hq]
  rw [nsmul_eq_mul, Fintype.card_fin]
  have hmul : q * (q * (q ^ 2)⁻¹) = 1 := by
    field_simp [q, hq]
  have htwo : (↑(n + 2) : ℚ) = (n : ℚ) + 2 := by norm_num
  rw [htwo]
  calc
    ((n : ℚ) + 2) * ↑(Fintype.card G) * (↑(Fintype.card G) * (1 / ↑(Fintype.card G) ^ 2))
        = ((n : ℚ) + 2) * (q * (q * (q ^ 2)⁻¹)) := by
            simp [q, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = ((n : ℚ) + 2) * 1 := by rw [hmul]
    _ = (n : ℚ) + 2 := by ring

end SumSlices

end FormalConjectures.Problems.Erdos.E20
