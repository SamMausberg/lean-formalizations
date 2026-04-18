/- 
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports
import FormalConjectures.Problems.Erdos.E119.Findings

/-!
# Erdős Problem 119

*Reference:* [erdosproblems.com/119](https://www.erdosproblems.com/119)
-/

open Nat
open FormalConjectures

namespace Erdos119

/--
Is it true that, for every integer `t ≥ 1`, there is some integer `a` such that `Nat.choose n k = a`
with `1 ≤ k ≤ n / 2` has exactly `t` solutions?
-/
@[category research open_problem, AMS 11]
theorem erdos_119 : answer(sorry) ↔
    ∀ t ≥ 1, ∃ a : ℕ,
      {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t := by
  sorry

end Erdos119
