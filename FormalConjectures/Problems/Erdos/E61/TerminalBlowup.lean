import FormalConjectures.Problems.Erdos.E61.PathPrimeness

/-!
# Terminal blow-up obstruction

This file packages the terminal safe bag from `prop:terminal-blowup`.  In the
local indexing, `pathGraph (n + 1)` is the fixed path `C`, the forbidden path is
`pathGraph (n + 2)`, and the terminal bag attaches to the last two vertices of
`C`.
-/

namespace Erdos61

open Finset

/-- The terminal profile: the last two vertices of a path on `n + 1` vertices. -/
def terminalBlowupProfile (n : ℕ) : Finset (Fin (n + 1)) :=
  {⟨n - 1, by omega⟩, ⟨n, by omega⟩}

theorem terminalBlowupProfile_not_left_endpoint (n : ℕ) (hn : 2 ≤ n) :
    terminalBlowupProfile n ≠ ({0} : Finset (Fin (n + 1))) := by
  intro h
  let last : Fin (n + 1) := ⟨n, by omega⟩
  have hlast : last ∈ terminalBlowupProfile n := by
    simp [terminalBlowupProfile, last]
  have hmem : last ∈ ({0} : Finset (Fin (n + 1))) := by
    simpa [h] using hlast
  rw [Finset.mem_singleton] at hmem
  have hval := congrArg Fin.val hmem
  simp [last] at hval
  omega

theorem terminalBlowupProfile_not_right_endpoint (n : ℕ) (hn : 2 ≤ n) :
    terminalBlowupProfile n ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))) := by
  intro h
  let prev : Fin (n + 1) := ⟨n - 1, by omega⟩
  let last : Fin (n + 1) := ⟨n, by omega⟩
  have hprev : prev ∈ terminalBlowupProfile n := by
    simp [terminalBlowupProfile, prev]
  have hmem : prev ∈ ({last} : Finset (Fin (n + 1))) := by
    simpa [h, last] using hprev
  rw [Finset.mem_singleton] at hmem
  have hval := congrArg Fin.val hmem
  simp [prev, last] at hval
  omega

theorem terminalBlowupProfile_safe (n : ℕ) (hn : 2 ≤ n) :
    terminalBlowupProfile n ≠ ({0} : Finset (Fin (n + 1))) ∧
      terminalBlowupProfile n ≠ ({⟨n, by omega⟩} : Finset (Fin (n + 1))) :=
  ⟨terminalBlowupProfile_not_left_endpoint n hn,
    terminalBlowupProfile_not_right_endpoint n hn⟩

/-- The base path plus one terminal-profile vertex is `P_{n+2}`-free. -/
theorem terminalBlowupProfile_oneVertexExtension_pathFree (n : ℕ) (hn : 2 ≤ n) :
    InducedFree (SimpleGraph.pathGraph (n + 2))
      (oneVertexExtension (terminalBlowupProfile n)) := by
  exact (oneVertexExtension_pathFree_iff_not_endpoint_singleton n hn
    (terminalBlowupProfile n)).mpr (terminalBlowupProfile_safe n hn)

/--
Formal terminal blow-up obstruction: substituting any `P_{n+2}`-free graph for
the terminal-profile vertex preserves `P_{n+2}`-freeness.
-/
theorem terminal_blowup_substitution_inducedFree
    (n : ℕ) (hn : 2 ≤ n) {VW : Type*} (W : SimpleGraph VW)
    (hW : InducedFree (SimpleGraph.pathGraph (n + 2)) W) :
    InducedFree (SimpleGraph.pathGraph (n + 2))
      (substituteVertex (oneVertexExtension (terminalBlowupProfile n)) W
        (none : Option (Fin (n + 1)))) := by
  exact singleton_safe_profile_substitution_for_paths n hn (terminalBlowupProfile n)
    (terminalBlowupProfile_safe n hn) W hW

end Erdos61
