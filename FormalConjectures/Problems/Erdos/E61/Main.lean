import FormalConjectures.Problems.Erdos.E61.ArityTwo
import FormalConjectures.Problems.Erdos.E61.ArityTwoFull
import FormalConjectures.Problems.Erdos.E61.Affine
import FormalConjectures.Problems.Erdos.E61.AffineCellFull
import FormalConjectures.Problems.Erdos.E61.Alternation
import FormalConjectures.Problems.Erdos.E61.Blockade
import FormalConjectures.Problems.Erdos.E61.BlockadeAsymptotic
import FormalConjectures.Problems.Erdos.E61.BooleanObstructions
import FormalConjectures.Problems.Erdos.E61.C5Semantic
import FormalConjectures.Problems.Erdos.E61.ChainQuotients
import FormalConjectures.Problems.Erdos.E61.CubeClosures
import FormalConjectures.Problems.Erdos.E61.Cutpoint
import FormalConjectures.Problems.Erdos.E61.CutpointFull
import FormalConjectures.Problems.Erdos.E61.CutpointPolynomial
import FormalConjectures.Problems.Erdos.E61.FirstSplitter
import FormalConjectures.Problems.Erdos.E61.PathInfrastructure
import FormalConjectures.Problems.Erdos.E61.PathProfiles
import FormalConjectures.Problems.Erdos.E61.PathPrimeness
import FormalConjectures.Problems.Erdos.E61.PairShadow
import FormalConjectures.Problems.Erdos.E61.RichTransversal
import FormalConjectures.Problems.Erdos.E61.RootedP4
import FormalConjectures.Problems.Erdos.E61.RootedP4Cubes
import FormalConjectures.Problems.Erdos.E61.SafeProfileFamily
import FormalConjectures.Problems.Erdos.E61.SafeProfiles
import FormalConjectures.Problems.Erdos.E61.SingletonCutFull
import FormalConjectures.Problems.Erdos.E61.StarCompress
import FormalConjectures.Problems.Erdos.E61.Substitution
import FormalConjectures.Problems.Erdos.E61.Terminal
import FormalConjectures.Problems.Erdos.E61.TerminalBlowup

/-!
# Erdős Problem 61 / Erdős-Hajnal notes

This module is the entry point for the fully checked formal material extracted
from `eh_forum_trimmed_v9.tex`.

The paper draft is a collection of local obstructions around the
Erdős-Hajnal conjecture, not a proof of the conjecture.  Accordingly, this file
records the conjectural target as a definition and imports rigorous local
lemmas from the submodules.
-/

open scoped SimpleGraph

namespace Erdos61

/--
The usual induced-subgraph Erdős-Hajnal statement, expressed as a proposition.
It is a definition, not asserted as a theorem in this repository.
-/
noncomputable def erdosHajnalStatement : Prop :=
  ∀ (W : Type) [Fintype W], ∀ H : SimpleGraph W,
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V], ∀ G : SimpleGraph V,
        ¬ SimpleGraph.IsIndContained H G →
          ∃ S : Finset V,
            (G.IsClique (S : Set V) ∨ Gᶜ.IsClique (S : Set V)) ∧
              Real.rpow (Fintype.card V : ℝ) c ≤ (S.card : ℝ)

end Erdos61
