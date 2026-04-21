import FormalConjectures.Problems.Erdos.E20.Compendium.Models.CodeModels

open Finset

namespace FormalConjectures.Problems.Erdos.E20.Compendium

/-!
# Small Fixed- Alphabet Values

This file records small concrete code-model certificates from
`sunflower_selected_results.tex`.

The full Hall-theoretic upper bound `F_{5,5}(2) ≤ 16` is not formalized here.
The lower-bound construction `[4]^2 ⊂ [5]^2` is.
-/

/-- The inclusion `Fin 4 ↪ Fin 5`. -/
def fin4ToFin5 (a : Fin 4) : Fin 5 :=
  ⟨a.1, by omega⟩

/-- The `4 × 4` grid inside `[5]^2`. -/
def fourByFourGridInFive : Finset (Fin 2 → Fin 5) :=
  (Finset.univ : Finset (Fin 2 → Fin 4)).image fun x => fun i => fin4ToFin5 (x i)

theorem fourByFourGridInFive_card :
    fourByFourGridInFive.card = 16 := by
  unfold fourByFourGridInFive
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    funext i
    have h := congrArg (fun f : Fin 2 → Fin 5 => f i) hxy
    apply Fin.ext
    simpa [fin4ToFin5] using congrArg Fin.val h

theorem mem_fourByFourGridInFive_iff {x : Fin 2 → Fin 5} :
    x ∈ fourByFourGridInFive ↔ ∀ i : Fin 2, (x i).1 < 4 := by
  constructor
  · intro hx i
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    simp [fin4ToFin5]
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨fun i => ⟨(x i).1, hx i⟩, by simp, ?_⟩
    funext i
    apply Fin.ext
    simp [fin4ToFin5]

theorem fourByFourGridInFive_codeModelFree :
    CodeModelFree 5 5 2 fourByFourGridInFive := by
  intro f hfInj hfMem
  have hlt : ∀ t : Fin 5, ∀ j : Fin 2, (f t j).1 < 4 := by
    intro t j
    exact (mem_fourByFourGridInFive_iff.mp (hfMem t)) j
  have hcoord_not_inj :
      ∀ j : Fin 2, ¬ Function.Injective fun t : Fin 5 => f t j := by
    intro j hj
    let g : Fin 5 → Fin 4 := fun t => ⟨(f t j).1, hlt t j⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply hj
      apply Fin.ext
      simpa [g] using congrArg Fin.val hab
    have hcard := Fintype.card_le_of_injective g hg
    norm_num [g] at hcard
  by_contra hno
  have hall : ∀ j : Fin 2, ∀ a b : Fin 5, f a j = f b j := by
    intro j
    by_contra hnot
    exact hno ⟨j, hnot, hcoord_not_inj j⟩
  have h01 : f 0 = f 1 := by
    funext j
    exact hall j 0 1
  have hfin : (0 : Fin 5) = 1 := hfInj h01
  norm_num at hfin

/-- The lower-bound half of the paper statement `F_{5,5}(2)=16`. -/
theorem sixteen_le_codeModelNumber_5_5_2 :
    16 ≤ codeModelNumber 5 5 2 := by
  have h := card_le_codeModelNumber (C := fourByFourGridInFive)
    fourByFourGridInFive_codeModelFree
  simpa [fourByFourGridInFive_card] using h

end FormalConjectures.Problems.Erdos.E20.Compendium
