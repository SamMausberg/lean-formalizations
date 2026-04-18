import Mathlib
import FormalConjectures.Util.Attributes

namespace FormalConjectures

/--
`answer P` is a light wrapper used in problem statements so that the conjectural answer can be
refined later without changing the overall theorem shape.
-/
abbrev answer (P : Prop) : Prop := P

syntax "answer(" term ")" : term

macro_rules
  | `(answer($p)) => `(FormalConjectures.answer $p)

end FormalConjectures
