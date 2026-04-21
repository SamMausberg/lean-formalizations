import Mathlib

namespace FormalConjectures.Problems.Erdos.E20.Kernels

/-- An abstract child-gluing context.

The missing local closure from the pasted child-gluing note is stored as the
`glue` field: if every indexed child witness is solved, then the parent is
solved.  The point of the structure is that the closure is an explicit
assumption, not a fabricated theorem. -/
structure ChildGluingContext (Parent : Type*) (Index : Type*) where
  ParentSolved : Parent → Prop
  ChildSolved : Parent → Index → Prop
  glue : ∀ {p : Parent}, (∀ i : Index, ChildSolved p i) → ParentSolved p

namespace ChildGluingContext

variable {Parent Index : Type*} (C : ChildGluingContext Parent Index)

/-- If all indexed children of a parent are solved, then the parent is solved. -/
theorem parent_solved_of_children {p : Parent}
    (h : ∀ i : Index, C.ChildSolved p i) :
    C.ParentSolved p :=
  C.glue h

end ChildGluingContext

end FormalConjectures.Problems.Erdos.E20.Kernels
