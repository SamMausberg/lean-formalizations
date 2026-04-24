# E61 formalization status

Source draft: `eh_forum_trimmed_v9.tex`.

This folder contains fully checked Lean formalizations of several local proof
cores from the draft:

- `ArityTwo.lean`: explicit graph realization of arbitrary arity-two shadow
  data, corresponding to the constructive half of `prop:arity-two`, plus the
  checked coordinate-line pullback cases for the first and second coordinates
  and the exact trace-class half-complete/half-anticomplete core used by the
  parity-line cases.
- `ArityTwoFull.lean`: the full finite affine-line pullback package for
  `prop:arity-two(a)`, including the parity trace and complement-trace cases,
  and the co-point universality statement of `prop:arity-two(b)`.
- `Affine.lean`: singleton-cut rows and the proof that their parity matrix has
  ladder size at most two, plus the two-coordinate projection behavior for
  disjoint and shared-left edge coordinates.  It also proves the no-affine-plane
  obstruction for four distinct singleton-cut rows, corresponding to the finite
  core of part (iv) of `thm:singleton-cut`, and the connected Boolean
  row-consistency lemma that edge parity determines a row up to global
  complement.
- `AffineCellFull.lean`: exact affine-cell linear algebra over `F₂`, including
  coset cardinality `2^dim`, two-functional fiber-as-cell packaging, trace-image
  compression, large four-fiber extraction, and the dual-functional ladder bound
  from `thm:affine-cell`.
- `SingletonCutFull.lean`: theorem-level packaging for `thm:singleton-cut`,
  including the row count, no-affine-plane obstruction, the
  `ceil((m+1)/2)` two-cell cover lower bound, and the ladder-size bound.
- `Alternation.lean`: the Boolean-word reconstruction and exact transition
  count behind `lem:bounded-alt`.
- `Blockade.lean`: finite counting cores behind `lem:failed-coordinate` and
  `prop:coordinate-synchronizes`.
- `BlockadeAsymptotic.lean`: power-threshold wrappers for the exponent forms of
  `lem:failed-coordinate` and `prop:coordinate-synchronizes`.
- `C5Semantic.lean`: the local `C5` semantic obstruction, including the
  alternating neighborhood construction, same-side patterns, complete cross
  matrix, and absence of an induced `C5`.
- `ChainQuotients.lean`: the chain-interface row-distinguishing obstruction
  behind `prop:chain-quotients`, proving side-respecting homogeneous quotients
  need at least `m` left classes.
- `Cutpoint.lean`: the suffix-row extraction core used in `lem:one-switch` and
  `thm:cutpoint-canonization`, including a checked ordered-block form of the
  one-switch extraction.
- `CutpointFull.lean`: the formal cutpoint-coded coloring package proving that
  canonical ordered blocks make the coloring constant on increasing tuples.
- `CutpointPolynomial.lean`: explicit square-root one-switch extraction on
  intervals and arbitrary ordered finsets, plus the iterated
  `m^(2^k) -> m` polynomial extraction bound and the `d^2` cutpoint-comparison
  bit extraction used after the monotone-core step of cutpoint canonization.
- `FirstSplitter.lean`: the exact first-splitter graph and profile model,
  induced-interface correctness, and the checked path-freeness equivalence
  between the first-splitter graph and its interface for `n ≥ 4`.
- `PathInfrastructure.lean`: a checked-list notion of induced paths and a bridge
  from such lists to mathlib induced copies of `SimpleGraph.pathGraph`.
- `PathProfiles.lean`: a concrete graph model for adding one vertex to a path
  with a prescribed path-neighborhood, with checked adjacency lemmas and the
  exact endpoint-singleton classification from `lem:one-vertex-extension` for
  paths on at least four vertices.
- `PathPrimeness.lean`: connectedness and neighborhood-cardinality lemmas for
  paths, the checked proof that every path on at least four vertices is prime,
  and the path-specialized singleton safe-profile substitution theorem with
  the prime hypothesis discharged.
- `PairShadow.lean`: a finite regularly spaced subsequence extraction for
  determinate ordered pair-shadows, corresponding to the core of
  `prop:determinate-pair-shadow`.
- `RichTransversal.lean`: an abstract finite backward-selection theorem for
  rich blockades, corresponding to the combinatorial core of
  `prop:rich-transversal`.
- `RootedP4.lean`: finite two-anchor defect extraction, its no-defect
  specialization, the average-weight edge selection used in
  `thm:two-anchor-extraction`, the three-edge rectangle obstruction from
  `thm:star-forest`, star, one-sided star-forest, and matching
  rectangle-shattering constructions, the powerset shattering core used by the
  Boolean examples, and the finite
  trace-count compression statement behind `prop:trace-count`.
- `StarCompress.lean`: the Sauer-Shelah / VC-dimension compression step used
  in `cor:star-compress`, stated as an explicit finite binomial-sum bound.
- `RootedP4Cubes.lean`: graph-level purified rooted-`P4` private-matching and
  Boolean-star cube constructions.  Their actual crossing-trace families
  shatter, respectively, a matching and a star of size `m`, with a combined
  graph-level Boolean obstruction theorem.
- `CubeClosures.lean`: explicit hereditary closures generated by the checked
  private-matching and Boolean-star cube template families, with `H`-free
  obstruction packages for graphs outside those closures, including the combined
  `H_specific_crossing_cube_obstruction` theorem.
- `SafeProfiles.lean`: the singleton safe-profile substitution direction,
  connecting `lem:one-vertex-extension` and `lem:substitution` under an
  explicit path-prime hypothesis.
- `SafeProfileFamily.lean`: a profile blow-up graph model and the exact
  safe-profile family classification from `thm:safe-profiles`: a safe family is
  empty or a singleton non-endpoint profile.
- `Substitution.lean`: the vertex-substitution graph construction, homogeneous
  set infrastructure, and a checked prime-graph substitution closure theorem
  matching `lem:substitution` for the local definitions.
- `BooleanObstructions.lean`: finite star and matching rectangle-trace
  obstructions from `prop:boolean-obstructions`, including the `2^m` one-sided
  trace count in the matching case.
- `Terminal.lean`: the concrete induced-path obstruction behind
  `prop:terminal-rigid`: the terminal `A` and `B` profiles with a missing
  cross-edge contain the displayed induced path, now also packaged as an
  ambient-graph embedding theorem.
- `TerminalBlowup.lean`: the terminal safe-bag version of
  `prop:terminal-blowup`, proving that substituting any `P_k`-free graph into
  the last-two-vertices profile of an induced `P_{k-1}` preserves
  `P_k`-freeness.
- `Main.lean`: imports the checked modules and records the Erdős-Hajnal target
  as a definition, not as a proved theorem.

The folder deliberately avoids placeholder theorem shells.  Proof blocks from
the TeX that are not listed above still need additional graph/path/substitution
infrastructure before they can be represented faithfully in Lean.
