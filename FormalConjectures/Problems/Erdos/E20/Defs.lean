/-
# Core Definitions for Hypergraph Decomposition Theory

This file contains the foundational definitions for the canonical support/trace
decomposition of r-uniform hypergraphs with bounded matching number.

## Informal references

The definitions here correspond to:
- **r-uniform hypergraph**: a collection of sets each of cardinality r
- **Matching**: a set of pairwise disjoint edges
- **Maximal matching**: a matching that cannot be extended
- **Support set** σ(e) = {i ∈ [t] : e ∩ E_i ≠ ∅}
- **Support class** H_I = {e ∈ H : σ(e) = I}
- **Trace class** H_S^= = {e ∈ H : e ∩ U = S}
- **Profile class** H_α = {e ∈ H : |e ∩ E_i| = α_i ∀ i}
- **Cone piece** C * G = {C ∪ g : g ∈ G}
-/
import Mathlib

open Finset

set_option maxHeartbeats 400000

variable {α : Type*} [DecidableEq α]

/-! ## Basic hypergraph definitions -/

/-- **r-uniform hypergraph** (§1, Definitions).
A hypergraph (finite set of finite sets) is r-uniform if every edge has exactly r vertices. -/
def IsRUniform (H : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- **Matching** (§2, Proof setup).
A family of edges indexed by `Fin t` forms a matching if they are pairwise disjoint and
all belong to the hypergraph H. -/
structure IndexedMatching (H : Finset (Finset α)) (t : ℕ) where
  /-- The matching edges E_1, ..., E_t -/
  edges : Fin t → Finset α
  /-- Each matching edge belongs to H -/
  edges_mem : ∀ i, edges i ∈ H
  /-- Matching edges are pairwise disjoint -/
  pairwise_disjoint : Pairwise (fun i j => Disjoint (edges i) (edges j))

namespace IndexedMatching

variable {H : Finset (Finset α)} {t : ℕ} (M : IndexedMatching H t)

/-- **U = E_1 ∪ ⋯ ∪ E_t** (§2, Proof setup).
The union of all matching edges, written U in the informal statement. -/
def union [Fintype α] : Finset α :=
  Finset.univ.biUnion M.edges

/-- **Maximal matching** (§2, Proof of (A)).
A matching is maximal if every edge of H intersects at least one matching edge.
Equivalently, no edge can be added to extend the matching. -/
def IsMaximal : Prop :=
  ∀ e ∈ H, ∃ i : Fin t, ¬Disjoint e (M.edges i)

end IndexedMatching

/-! ## Support, trace, and profile functions -/

/-- **Support set** σ(e) (§2, Proof of (A)).
For an edge e and matching edges M, the support set σ(e) = {i ∈ [t] : e ∩ E_i ≠ ∅}. -/
def supportSet (M : Fin t → Finset α) (e : Finset α) : Finset (Fin t) :=
  Finset.univ.filter (fun i => ¬Disjoint e (M i))

/-- **Support class** H_I (§1, Theorem (A)).
For a nonempty I ⊆ [t], the support class H_I = {e ∈ H : σ(e) = I}. -/
def supportClass (H : Finset (Finset α)) (M : Fin t → Finset α) (I : Finset (Fin t)) :
    Finset (Finset α) :=
  H.filter (fun e => supportSet M e = I)

/-- **Trace** e ∩ U (§2, Proof of (B)).
The trace of an edge e with respect to a set U is e ∩ U. -/
def edgeTrace (e : Finset α) (U : Finset α) : Finset α :=
  e ∩ U

/-- **Trace class** H_S^= (§1, Theorem (B)).
For a nonempty S ⊆ U, the trace class H_S^= = {e ∈ H : e ∩ U = S}. -/
def traceClass (H : Finset (Finset α)) (U : Finset α) (S : Finset α) :
    Finset (Finset α) :=
  H.filter (fun e => e ∩ U = S)

/-- **Profile vector** (§1, Theorem (C)).
For an edge e and matching edges M, the profile maps each index i to |e ∩ E_i|. -/
def profileVec (M : Fin t → Finset α) (e : Finset α) : Fin t → ℕ :=
  fun i => (e ∩ M i).card

/-- **Profile class** H_α (§1, Theorem (C)).
For a vector α : Fin t → ℕ, the profile class H_α = {e ∈ H : |e ∩ E_i| = α_i ∀ i}. -/
def profileClass (H : Finset (Finset α)) (M : Fin t → Finset α)
    (profile : Fin t → ℕ) : Finset (Finset α) :=
  H.filter (fun e => profileVec M e = profile)

/-! ## Cone piece definition -/

/-- **Cone piece** C * G (§1, Definitions).
A cone piece C * G = {C ∪ g : g ∈ G} where C is the fixed core and G is a family of sets.
This definition constructs the cone from a core C and petal family G. -/
def conePiece (C : Finset α) (G : Finset (Finset α)) : Finset (Finset α) :=
  G.image (fun g => C ∪ g)

/-- **Common core** C_I = ⋂_{e ∈ H_I} e (§1, Theorem (A)).
The intersection of all edges in a subfamily. Returns ∅ if the subfamily is empty. -/
noncomputable def commonCore [Fintype α] (F : Finset (Finset α)) : Finset α :=
  if h : F.Nonempty then F.inf' h id else ∅

/-! ## Support-bounded-alphabet piece -/

/-- **Support-bounded-alphabet piece** (§1, Definitions).
A family G ⊆ binom(V, r) is a support-bounded-alphabet piece if there is a partition
V = B_1 ⊔ ⋯ ⊔ B_t ⊔ R with t < k and a nonempty I ⊆ [t] such that every edge e ∈ G
satisfies e ∩ B_i ≠ ∅ ↔ i ∈ I. -/
def IsSupportBoundedAlphabet (G : Finset (Finset α)) (t : ℕ)
    (B : Fin t → Finset α) (I : Finset (Fin t)) : Prop :=
  ∀ e ∈ G, ∀ i : Fin t, (¬Disjoint e (B i) ↔ i ∈ I)

/-! ## Matching number and basic properties -/

/-- **Matching number** ν(H) (§1, setup).
The matching number is the supremum of sizes of matchings in H.
We define it as the supremum over all t such that an IndexedMatching of size t exists. -/
noncomputable def matchingNumber (H : Finset (Finset α)) : ℕ :=
  sSup {t : ℕ | ∃ M : IndexedMatching H t, True}

/-- **Excess** e(a) = Σ (a_i - 1) (§4, Definition).
The excess of a profile vector, measuring how far the profile is from having
all entries equal to 1. -/
def profileExcess (a : Fin t → ℕ) (J : Finset (Fin t)) : ℕ :=
  J.sum (fun i => a i - 1)

