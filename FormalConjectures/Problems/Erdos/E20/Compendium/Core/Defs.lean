import Mathlib

open scoped BigOperators Pointwise Classical
open Finset

set_option maxHeartbeats 8000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
namespace FormalConjectures.Problems.Erdos.E20.Compendium


/-!
# Core Definitions for the Sunflower Compendium

This file contains the fundamental definitions used throughout the formalization
of the research compendium "A Research Compendium on the Sunflower Problem"
(sunflower_compendium.pdf). These definitions correspond to the basic notions
introduced in Section 2 (Background and notation) and elsewhere in the paper.
-/

variable {α : Type*} [DecidableEq α]

/-- **Definition (k-sunflower, Section 2).**
A k-sunflower in a family `F` of finite sets is a subfamily of `k` distinct members
whose pairwise intersections are all equal (the common intersection is called the kernel).
We formalize this as: a function `petals : Fin k → Finset α` whose images are all in `F`,
are pairwise distinct, and have a common pairwise intersection (the kernel `Y`). -/
def IsSunflower (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ (petals : Fin k → Finset α) (Y : Finset α),
    (∀ i, petals i ∈ F) ∧
    Function.Injective petals ∧
    (∀ i j, i ≠ j → petals i ∩ petals j = Y)

/-- **Definition (k-sunflower-free, Section 2).**
A family `F` is k-sunflower-free if it contains no k-sunflower. -/
def SunflowerFree (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬ IsSunflower F k

/-- **Definition (n-uniform family, Section 2).**
A family `F` is n-uniform if every member has exactly `n` elements. -/
def IsUniform (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ A ∈ F, A.card = n

/-- **Definition (Link/restriction, Section 2).**
The link of a family `F` at a set `S` is `F_S := {A \ S : A ∈ F, S ⊆ A}`.
This corresponds to the "link" operation defined in Section 2. -/
noncomputable def familyLink (F : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  (F.filter (fun A => S ⊆ A)).image (fun A => A \ S)

/-- **Definition (Degree, Section 2).**
The degree of a set `B` with respect to a family `F` is
`d_F(B) := |{A ∈ F : B ⊆ A}|`. -/
noncomputable def familyDegree (F : Finset (Finset α)) (B : Finset α) : ℕ :=
  (F.filter (fun A => B ⊆ A)).card

/-- **Definition (Degree-one vertices / leaves, Definition 3.1).**
The set of leaves (degree-one vertices) of a family `F`:
`L(F) := {x : d_F({x}) = 1}`.
Formalized over a ground set `V`. -/
noncomputable def familyLeaves [Fintype α] (F : Finset (Finset α)) : Finset α :=
  Finset.univ.filter (fun x => familyDegree F {x} = 1)

/-- **Definition (One-round leaf stripping, Definition 3.1).**
`∂F := {A \ L(F) : A ∈ F}` with duplicates collapsed.
This is the one-round stripping operation from Definition 3.1. -/
noncomputable def stripOnce [Fintype α] (F : Finset (Finset α)) : Finset (Finset α) :=
  F.image (fun A => A \ familyLeaves F)

/-- **Definition (Support of a family, Section 2).**
`supp(F) := ⋃_{A ∈ F} A`. -/
noncomputable def familySupport (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

/-- **Definition (Support piece, Definition 4.1).**
`P` is a support piece of rank `r` for an `m`-uniform family `G` if
`P ⊆ supp(G)` and `|A ∩ P| = r` for every `A ∈ G`. -/
def IsSupportPiece (G : Finset (Finset α)) (P : Finset α) (r : ℕ) : Prop :=
  P ⊆ familySupport G ∧ ∀ A ∈ G, (A ∩ P).card = r

/-- **Definition (Trace family, Definition 4.1).**
The trace family of `G` on a support piece `P`:
`Tr_P(G) := {A ∩ P : A ∈ G}`. -/
noncomputable def traceFamily (G : Finset (Finset α)) (P : Finset α) : Finset (Finset α) :=
  G.image (fun A => A ∩ P)

/-- **Definition (Projected branch, Definition 4.1).**
For a trace `τ`, the projected branch is
`G_τ := {A \ P : A ∈ G, A ∩ P = τ}`. -/
noncomputable def projectedBranch (G : Finset (Finset α)) (P : Finset α)
    (τ : Finset α) : Finset (Finset α) :=
  (G.filter (fun A => A ∩ P = τ)).image (fun A => A \ P)

/-- **Definition (Γ_t, Section 2 / Section 5).**
`Γ_t(F) := ∑_{|B|=t} d_F(B)²`.
Formalized over a finite ground set. -/
noncomputable def gammaT [Fintype α] (F : Finset (Finset α)) (t : ℕ) : ℕ :=
  ∑ B ∈ (Finset.univ.powersetCard t), (familyDegree F B) ^ 2

/-- **Definition (Λ_t, Section 2 / Section 5).**
`Λ_t(F) := ∑_{|B|=t} d_F(B) = C(n,t) · |F|`. -/
noncomputable def lambdaT [Fintype α] (F : Finset (Finset α)) (t : ℕ) : ℕ :=
  ∑ B ∈ (Finset.univ.powersetCard t), familyDegree F B

/-- **Definition (M(n,k), Section 1).**
`M(n,k)` is the largest size of a k-sunflower-free n-uniform family.
Defined as a supremum over all finite types and families. -/
noncomputable def sunflowerNumber (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (α : Type) (_ : DecidableEq α) (_ : Fintype α)
    (F : Finset (Finset α)), IsUniform F n ∧ SunflowerFree F k ∧ F.card = m}

/-- **Definition (f(n,k), Section 1).**
`f(n,k) := M(n,k) + 1` is the least integer such that every n-uniform family
of that size contains a k-sunflower. -/
noncomputable def sunflowerThreshold (n k : ℕ) : ℕ :=
  sunflowerNumber n k + 1

/-- **Definition (Terminal-kernel extremal function, Definition 3.6).**
`Mker(n,k)` is the maximum size of a k-sunflower-free family of rank at most `n`
with no degree-one vertices. -/
noncomputable def terminalKernelNumber (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (α : Type) (_ : DecidableEq α) (_ : Fintype α)
    (F : Finset (Finset α)),
    (∀ A ∈ F, A.card ≤ n) ∧ SunflowerFree F k ∧
    familyLeaves F = ∅ ∧ F.card = m}

/-- **Definition (Fixed-alphabet transversal code model, Section 2).**
`F_{q,k}(m)` is the maximum size of a subset `C ⊆ [q]^m` such that no `k` distinct
codewords are coordinatewise all-equal-or-all-distinct. -/
noncomputable def codeModelNumber (q k m : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ (C : Finset (Fin m → Fin q)),
    C.card = c ∧
    ∀ (f : Fin k → Fin m → Fin q),
      Function.Injective f →
      (∀ i, f i ∈ C) →
      ∃ j : Fin m, ¬(∀ a b : Fin k, f a j = f b j) ∧
                    ¬(Function.Injective (fun a => f a j))}

/-- **Definition (Normalized correlation, Definition 6.1).**
For an r-uniform family H,
`σ(H) := (1/(r·|H|²)) · ∑_x d_H(x)²`.
We store the unnormalized version `∑_x d_H(x)²` and normalize in theorem statements. -/
noncomputable def sumDegreesSq [Fintype α] (H : Finset (Finset α)) : ℕ :=
  ∑ x : α, (familyDegree H {x}) ^ 2

/-- **Definition (Matching number).**
The matching number `ν(H)` is the maximum number of pairwise disjoint members of `H`. -/
noncomputable def matchingNumber (H : Finset (Finset α)) : ℕ :=
  sSup {m : ℕ | ∃ (M : Finset (Finset α)), M ⊆ H ∧ M.card = m ∧
    ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B}
end FormalConjectures.Problems.Erdos.E20.Compendium
