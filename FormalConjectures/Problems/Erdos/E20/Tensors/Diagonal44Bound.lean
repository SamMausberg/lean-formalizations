import Mathlib
import FormalConjectures.Problems.Erdos.E20.Tensors.CharacterTensors

open Finset BigOperators Matrix Module

namespace FormalConjectures.Problems.Erdos.E20

section SupportLemma

variable {K α : Type*} [Field K] [DecidableEq K] [DecidableEq α] [Fintype α]

/-- Any `d`-dimensional subspace of functions on a finite set contains a function whose support has
size at least `d`. This is the linear-algebraic support lemma needed for the diagonal
slice-rank lower bound. -/
theorem exists_function_support_ge_finrank (W : Submodule K (α → K)) :
    ∃ h : W,
      Module.finrank K W ≤
        (Finset.univ.filter fun a : α => ((h : α → K) a ≠ 0)).card := by
  classical
  let β := Module.Free.ChooseBasisIndex K W
  let b : Basis β K W := Module.Free.chooseBasis K W
  by_cases hβ : IsEmpty β
  · refine ⟨0, ?_⟩
    have hfin : Module.finrank K W = 0 := by
      simp [β, Module.finrank_eq_card_chooseBasisIndex, hβ]
    simp [hfin]
  let M : Matrix β α K := fun i a => ((b i : W) : α → K) a
  have hrows' : LinearIndependent K (fun i : β => ((b i : W) : α → K)) :=
    b.linearIndependent.map' (Submodule.subtype W) (LinearMap.ker_eq_bot.mpr W.injective_subtype)
  have hrows : LinearIndependent K M.row := by
    simpa [M] using hrows'
  have hrank : M.rank = Fintype.card β := by
    simpa using (LinearIndependent.rank_matrix (R := K) (M := M) hrows)
  let c : α → (β → K) := M.col
  obtain ⟨κ, a, ha_inj, hspan, hli⟩ := exists_linearIndependent' K c
  letI : Finite κ := Finite.of_injective a ha_inj
  letI : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = Fintype.card β := by
    calc
      Fintype.card κ = (Set.range (c ∘ a)).finrank K := by
        exact linearIndependent_iff_card_eq_finrank_span.mp hli
      _ = (Set.range c).finrank K := by
        simpa [Set.finrank] using
          congrArg (fun S : Submodule K (β → K) => Module.finrank K S) hspan
      _ = M.rank := by
        simpa [Set.finrank, c] using (rank_eq_finrank_span_cols (R := K) (A := M)).symm
      _ = Fintype.card β := hrank
  have hcardκ' : Fintype.card κ = Module.finrank K (β → K) := by
    simpa [Module.finrank_fintype_fun_eq_card] using hcardκ
  have hκpos : 0 < Fintype.card κ := by
    rw [hcardκ]
    exact Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp hβ)
  letI : Nonempty κ := Fintype.card_pos_iff.mp hκpos
  let bcol : Basis κ K (β → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcardκ'
  let L : (β → K) →ₗ[K] K := ∑ j : κ, bcol.coord j
  let h : W := ∑ i : β, (L ((Pi.basisFun K β) i)) • b i
  have hL :
      ∀ x : β → K, L x = ∑ i : β, x i * L ((Pi.basisFun K β) i) := by
    intro x
    have hx := congrArg L ((Pi.basisFun K β).sum_repr x).symm
    simpa [Pi.basisFun_repr, map_sum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hx
  have hbcol : ⇑bcol = c ∘ a :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcardκ'
  have hone : ∀ j : κ, ((h : W) : α → K) (a j) = 1 := by
    intro j
    calc
      (((h : W) : α → K) (a j))
          = ∑ i : β, (L ((Pi.basisFun K β) i)) * (((b i : W) : α → K) (a j)) := by
              simp [h, mul_comm]
      _ = ∑ i : β, ((c ∘ a) j) i * L ((Pi.basisFun K β) i) := by
            simp [c, M, mul_comm]
      _ = L ((c ∘ a) j) := (hL ((c ∘ a) j)).symm
      _ = L (bcol j) := by
            simp [hbcol]
      _ = 1 := by
            simp [L]
  have hsub :
      Finset.univ.image a ⊆ Finset.univ.filter fun x : α => (((h : W) : α → K) x ≠ 0) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, -, rfl⟩
    simp [hone j]
  refine ⟨h, ?_⟩
  calc
    Module.finrank K W = Fintype.card β := by
          simpa [β] using (Module.finrank_eq_card_chooseBasisIndex (R := K) (M := W))
    _ = Fintype.card κ := hcardκ.symm
    _ = (Finset.univ.image a).card := by
          symm
          simpa using Finset.card_image_of_injective (s := (Finset.univ : Finset κ)) ha_inj
    _ ≤ (Finset.univ.filter fun x : α => (((h : W) : α → K) x ≠ 0)).card :=
          Finset.card_le_card hsub

end SupportLemma

section DiagonalBase

variable {K α : Type*} [Field K] [DecidableEq K] [Fintype α] [DecidableEq α]

abbrev Tensor2 (α : Type*) (K : Type*) := α → α → K

/-- The weighted diagonal `2`-tensor. -/
def weightedDiagonal2 (w : α → K) : Tensor2 α K :=
  fun x y => if y = x then w x else 0

/-- A rank decomposition of a `2`-tensor. -/
structure RankDecomp2 (T : Tensor2 α K) where
  ι : Type*
  fintype_ι : Fintype ι
  f : ι → α → K
  g : ι → α → K
  eval_eq : ∀ x y, T x y = ∑ i : ι, f i x * g i y

attribute [instance] RankDecomp2.fintype_ι

namespace RankDecomp2

def size {T : Tensor2 α K} (D : RankDecomp2 (α := α) (K := K) T) : ℕ :=
  Fintype.card D.ι

def tensorMatrix {T : Tensor2 α K} (_ : RankDecomp2 (α := α) (K := K) T) : Matrix α α K :=
  fun x y => T x y

def leftMatrix {T : Tensor2 α K} (D : RankDecomp2 (α := α) (K := K) T) : Matrix α D.ι K :=
  fun x i => D.f i x

def rightMatrix {T : Tensor2 α K} (D : RankDecomp2 (α := α) (K := K) T) : Matrix D.ι α K :=
  fun i y => D.g i y

theorem tensorMatrix_eq_mul {T : Tensor2 α K} (D : RankDecomp2 (α := α) (K := K) T) :
    D.tensorMatrix = D.leftMatrix * D.rightMatrix := by
  ext x y
  simp [tensorMatrix, leftMatrix, rightMatrix, Matrix.mul_apply, D.eval_eq]

end RankDecomp2

def weightedDiagonal2Matrix (w : α → K) : Matrix α α K :=
  fun x y => weightedDiagonal2 (α := α) (K := K) w x y

theorem weightedDiagonal2_eq_diagonal (w : α → K) :
    weightedDiagonal2Matrix (α := α) (K := K) w = Matrix.diagonal w := by
  ext x y
  by_cases h : y = x
  · simp [weightedDiagonal2Matrix, weightedDiagonal2, Matrix.diagonal, h]
  · have hxy : ¬ x = y := by simpa [eq_comm] using h
    simp [weightedDiagonal2Matrix, weightedDiagonal2, Matrix.diagonal, h, hxy]

/-- The weighted diagonal matrix has rank equal to the number of nonzero weights. -/
theorem rank_weightedDiagonal2_matrix (w : α → K) :
    (weightedDiagonal2Matrix (α := α) (K := K) w).rank =
      Fintype.card {a // w a ≠ 0} := by
  rw [weightedDiagonal2_eq_diagonal]
  simpa using Matrix.rank_diagonal (R := K) w

/-- Any rank decomposition of a weighted diagonal `2`-tensor needs at least as many summands as
there are nonzero diagonal weights. -/
theorem card_nonzero_weights_le_rankDecomp2_size
    (w : α → K) (D : RankDecomp2 (α := α) (K := K) (weightedDiagonal2 (α := α) (K := K) w)) :
    Fintype.card {a // w a ≠ 0} ≤ D.size := by
  calc
    Fintype.card {a // w a ≠ 0}
        = (weightedDiagonal2Matrix (α := α) (K := K) w).rank := by
            symm
            exact rank_weightedDiagonal2_matrix (α := α) (K := K) w
    _ = D.tensorMatrix.rank := rfl
    _ = (D.leftMatrix * D.rightMatrix).rank := by
          rw [D.tensorMatrix_eq_mul]
    _ ≤ D.rightMatrix.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card D.ι := Matrix.rank_le_card_height _
    _ = D.size := rfl

theorem card_le_rankDecomp2_size_of_weightedDiagonal_nonzero
    (w : α → K) (hw : ∀ a : α, w a ≠ 0)
    (D : RankDecomp2 (α := α) (K := K) (weightedDiagonal2 (α := α) (K := K) w)) :
    Fintype.card α ≤ D.size := by
  calc
    Fintype.card α = Fintype.card {a // w a ≠ 0} := by
      classical
      exact Fintype.card_congr
        { toFun := fun a => ⟨a, hw a⟩
          invFun := fun a => a.1
          left_inv := fun _ => rfl
          right_inv := fun _ => by ext; rfl }
    _ ≤ D.size := card_nonzero_weights_le_rankDecomp2_size (α := α) (K := K) w D

end DiagonalBase

end FormalConjectures.Problems.Erdos.E20
