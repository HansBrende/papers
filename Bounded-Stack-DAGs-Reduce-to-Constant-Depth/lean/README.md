# Lean library `BoundedStackDepth`

The formalization of *Bounded-Stack DAGs Reduce to Constant Depth* (Lean and Mathlib v4.34.1). It requires the eighth
paper's library `boundedNesting` and, for the corollaries, the eleventh paper's library `mergeDepth` by relative paths, and
through them the earlier libraries of the series, so the sibling directories of the repository must be in place. Declarations below are relative to the namespace `BoundedStackDepth`.

## Main results

- `tcpAt_direct` (`Main.lean`): for `k` walks, pauses allowed, and `ε > 0`, the walk DAG has a cut of at most `εT`
  edges and depth at most `K^P − 1`, with the explicit parameters `parH`, `parQ`, `parJ`, `parP`, `parK`.
- `tcp`: `TCP k` for every `k`; `main : MainStatement`, the same statement as stated in `Statement.lean`; and `sr`:
  `SR s` for every `s`, through the eighth paper's reduction.
- Corollary N (`DeepNesting.lean`, `Conjectures.lean`): `dnp_cut`, the deep-nesting pair `dnpPair` (built from the
  eleventh paper's `MergeDepth.dnpWalk`) has, for every nesting depth, shift and length, a cut of at most `εT` edges and
  depth at most `K^P − 1` for `k = 2`; `not_conjAprime` and `not_conjAsecond`: Conjectures A′ and A″, stated as
  `ConjAprime` and `ConjAsecond` on the cyclic covers of the eleventh paper's library, are false.
- Corollary O (`Machines.lean`), in the frozen machine model of the first paper, through the eleventh paper's
  library: `genie_of_trace` and `depthTCP` (genies of cost `εL` and bounded full depth for every trace), `crux_excludes`
  (the crux alone excludes oblivious linear-time transposers) and `linCrux_excludes` (the linear crux, for machines with a
  linear data path).
- Corollary HV (`Machines.lean`): `ballSystem_indexCode` and `ballSystem_minrank` (the ball systems of radius
  `genieDepth k β C ε` of oblivious transposers have index codes of at most `εL` bits, and minrank at most `εL`), and
  `hvStar`, `hvStar_linear`: the eleventh paper's Conjecture HV*, stated as `ConjHVStar` and `ConjHVStarLin`, holds.
- Corollary L (`LowAdaptivity.lean`): given `NativeBound` (the native half bound for the cone relations of the frozen traces of the
  machine, at scale `w` and at the widths assumed), `se_class_native` and `se_native` (the eleventh paper's Theorem SE without bounded entry), and
  `fSecond_native_class` and `fSecond_native` (the eighth paper's Corollary F″ without bounded entry: a linear-time
  transposer has trace entropy above `ηL` for every `η < 1/2`).
- Every declaration that the paper cites depends at most on `propext`, `Classical.choice` and `Quot.sound`:
  `lake env lean PaperAxioms.lean` prints them. `PaperAxioms.lean` is generated from the paper's LaTeX sources by
  `../tools/lean_index.py`.

## Modules

The root module `BoundedStackDepth.lean` imports all of them.

| layer | modules |
|---|---|
| statements and foundations | `Statement` (the main statement and its corollary for stack DAGs), `Assembly` (the probabilistic method for label cuts), `Basic` (bands, groups, floors), `Grid` (counting over the grid offsets), `BandSums` (Lemma E), `Choice` (parameter inequalities), `Walks`, `Prominence`, `TopProminence` |
| one walk (Theorem A) | `Decomposition` (tops and ladders), `Excursions` (structures and laminarity), `FramesU` (the frames of class U), `FrameSystem`, `FrameDynamics`, `FrameWeight` and `FrameWeightU` (Lemma W1), `LadderBands` (bands at ladder times, Lemma W2), `CostModel`, `HopData`, `Events` (validity), `PerExcursion` (the ladder sum), `TheoremA` |
| the label | `Label` (Lemma V), `Global` (the label of `k` walks) |
| displays | `Display` (the display as a least fixed point), `Revealing` (adaptive revealing), `DisplayTail` (Lemma D), `DisplayView` (the display above a group), `Entries`, `Composition` (the composed display), `ViewInvariance` (Proposition W), `Exposure` |
| accounting and the proof | `Budgets`, `EventWeight`, `Accounting` (counting facts), `Truncation`, `Wrap`, `WrapGlobal`, `CutDescents`, `CutHops`, `Totals`, `Main` |
| consequences | `DeepNesting` and `Conjectures` (Corollary N), `Machines` (Corollaries O and HV), `LowAdaptivity` (Corollary L) |

The paper names, for each numbered result, its declarations and file; its appendix indexes all of them by module.

## Building

From this directory: `lake exe cache get`, then `lake build`, then `lake env lean PaperAxioms.lean`. Locally,
`.lake/packages` may be a symbolic link to a sibling's packages at the same revisions; it is not committed.
