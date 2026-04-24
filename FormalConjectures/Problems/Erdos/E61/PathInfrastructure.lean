import FormalConjectures.Problems.Erdos.E61.Defs

/-!
# Lightweight induced-path infrastructure

Mathlib has `SimpleGraph.pathGraph`.  For the local obstruction proofs in the
paper it is often most convenient to first verify that a concrete list of
vertices has exactly the path adjacencies.  This file provides that bridge.
-/

namespace Erdos61

/--
A list of vertices forms an induced path if it is duplicate-free and two listed
vertices are adjacent exactly when their positions differ by one.
-/
structure IsInducedPathList {V : Type*} (G : SimpleGraph V) (l : List V) : Prop where
  nodup : l.Nodup
  adj_iff :
    ∀ i j : Fin l.length,
      G.Adj (l.get i) (l.get j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

namespace IsInducedPathList

variable {V : Type*} {G : SimpleGraph V} {l : List V}

/--
A checked induced-path list gives an induced copy of the corresponding path
graph.
-/
noncomputable def toEmbedding (h : IsInducedPathList G l) :
    SimpleGraph.pathGraph l.length ↪g G where
  toFun := l.get
  inj' := h.nodup.injective_get
  map_rel_iff' := by
    intro i j
    rw [SimpleGraph.pathGraph_adj]
    exact h.adj_iff i j

theorem isIndContained (h : IsInducedPathList G l) :
    SimpleGraph.IsIndContained (SimpleGraph.pathGraph l.length) G :=
  ⟨h.toEmbedding⟩

end IsInducedPathList

end Erdos61
