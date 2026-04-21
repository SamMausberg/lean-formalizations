import Mathlib
import FormalConjectures.Problems.Erdos.E20.Compendium.Recurrences.CapturePressure

namespace FormalConjectures.Problems.Erdos.E20

/-- An abstract exact-support pruning context.

The fields record exactly the local hypotheses from the pasted pruning note:
there is a well-founded strict descendant relation, a class of unresolved nodes,
and a hereditary-faithfulness predicate.  The `exactify` field is the missing
local lemma: failure of hereditary faithfulness produces a strict unresolved
descendant. -/
structure ExactSupportPruningContext (Node : Type*) where
  StrictDescendant : Node → Node → Prop
  wellFounded : WellFounded StrictDescendant
  Unresolved : Node → Prop
  HereditarilyFaithful : Node → Prop
  exactify : ∀ {x : Node}, Unresolved x → ¬ HereditarilyFaithful x →
    ∃ y : Node, StrictDescendant y x ∧ Unresolved y

namespace ExactSupportPruningContext

variable {Node : Type*} (C : ExactSupportPruningContext Node)

/-- A node is terminal if it has no unresolved strict descendants. -/
def Terminal (x : Node) : Prop :=
  ∀ y, C.StrictDescendant y x → ¬ C.Unresolved y

/-- Every nonempty unresolved region contains a terminal unresolved node. -/
theorem exists_terminal_unresolved
    (h : ∃ x : Node, C.Unresolved x) :
    ∃ x : Node, C.Unresolved x ∧ C.Terminal x := by
  classical
  let s : Set Node := {x | C.Unresolved x}
  have hs : s.Nonempty := by
    rcases h with ⟨x, hx⟩
    exact ⟨x, hx⟩
  rcases C.wellFounded.has_min s hs with ⟨x, hx, hmin⟩
  refine ⟨x, hx, ?_⟩
  intro y hyx hy
  exact (hmin y hy) hyx

/-- A terminal unresolved node must be hereditarily faithful, otherwise
`exactify` would produce a strict unresolved descendant. -/
theorem terminal_unresolved_hereditarilyFaithful
    {x : Node} (hx : C.Unresolved x) (hterm : C.Terminal x) :
    C.HereditarilyFaithful x := by
  by_contra hfaith
  rcases C.exactify hx hfaith with ⟨y, hyx, hy⟩
  exact hterm y hyx hy

/-- The pruning statement needed by the exact-support note:
some unresolved terminal node exists, and it is hereditarily faithful. -/
theorem exists_terminal_unresolved_and_faithful
    (h : ∃ x : Node, C.Unresolved x) :
    ∃ x : Node, C.Unresolved x ∧ C.Terminal x ∧ C.HereditarilyFaithful x := by
  rcases C.exists_terminal_unresolved (Node := Node) h with ⟨x, hx, hterm⟩
  exact ⟨x, hx, hterm, C.terminal_unresolved_hereditarilyFaithful hx hterm⟩

end ExactSupportPruningContext

end FormalConjectures.Problems.Erdos.E20
