import FormalConjectures.Problems.Erdos.E61.Cutpoint

/-!
# Cutpoint-coded coloring packaging

This file formalizes the deterministic endpoint of
`thm:cutpoint-canonization`: once the ordered block has a single unary label and
all cutpoint comparison bits are independent of the chosen ordered pair, the
cutpoint-coded coloring is constant on increasing ordered tuples.
-/

namespace Erdos61

/-- A strictly increasing tuple of indices in an ordered finite block. -/
def StrictIncreasingTuple {h m : ℕ} (a : Fin h → Fin m) : Prop :=
  ∀ ⦃i j : Fin h⦄, i < j → a i < a j

/-- The comparison-bit object used by a cutpoint code on ordered `h`-tuples. -/
abbrev OrderedComparisonBits (h d : ℕ) :=
  (i j : Fin h) → i < j → Fin d → Fin d → Bool

/--
If a coloring is determined by unary labels and cutpoint comparison bits, then it
is constant on increasing tuples from any block where all labels agree and every
comparison bit is independent of the ordered pair.
-/
theorem cutpoint_canonical_block_color_constant
    {X Sigma κ : Type*} {h d m : ℕ}
    (χ : (Fin h → X) → κ)
    (label : X → Sigma) (cut : Fin d → X → ℕ)
    (decode : (Fin h → Sigma) → OrderedComparisonBits h d → κ)
    (y : Fin m → X)
    (hdet : ∀ x : Fin h → X,
      χ x = decode
        (fun i => label (x i))
        (fun i j _hij p q => decide (cut p (x i) ≤ cut q (x j))))
    (hlabel : ∀ i j : Fin m, label (y i) = label (y j))
    (hcmp : ∀ p q : Fin d, ∀ ⦃i j i' j' : Fin m⦄,
      i < j → i' < j' →
        (cut p (y i) ≤ cut q (y j) ↔ cut p (y i') ≤ cut q (y j'))) :
    ∀ a b : Fin h → Fin m,
      StrictIncreasingTuple a → StrictIncreasingTuple b →
        χ (fun i => y (a i)) = χ (fun i => y (b i)) := by
  intro a b ha hb
  rw [hdet, hdet]
  congr 1
  · funext i
    exact hlabel (a i) (b i)
  · funext i j hij p q
    have hab := hcmp p q (ha hij) (hb hij)
    by_cases hleft : cut p (y (a i)) ≤ cut q (y (a j))
    · have hright : cut p (y (b i)) ≤ cut q (y (b j)) := hab.mp hleft
      simp [hleft, hright]
    · have hright : ¬ cut p (y (b i)) ≤ cut q (y (b j)) := by
        intro h
        exact hleft (hab.mpr h)
      simp [hleft, hright]

end Erdos61
