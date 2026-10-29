# lean-machine

Shared Lean machinery for the papers in this repository: results that more than one theorem could
use, and external Lean code we have pulled in. Results specific to one paper stay in that paper's
`lean/` library.

## What goes here

- General lemmas and constructions that are not tied to one paper.
- External Lean code that we reuse, ported to our Lean and Mathlib versions.
- Nothing with `sorry`, `admit`, `native_decide` or new axioms. Every exported theorem depends at
  most on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

- One Lake package, `leanMachine`, with the library `LeanMachine`. It uses Lean and Mathlib v4.34.1,
  the same versions as the papers.
- A single, relatively short proof goes in one file, `LeanMachine/<Name>.lean`.
- A larger topic, or one that mixes external code with our own additions, gets a folder,
  `LeanMachine/<Topic>/`, with its own `README.md`.
- `LeanMachine.lean` imports every module. `Axioms.lean` prints the axioms of every exported
  theorem. Add new modules and theorems to both.

## Contents

| Path | Contents | Origin |
|---|---|---|
| [`LeanMachine/TutteBerge/`](LeanMachine/TutteBerge/) | Berge's augmenting-path theorem, the Tutte–Berge formula, the matching number, and the components of G − U as barrier blocks | external ([jtraverso/berge-matching](https://github.com/jtraverso/berge-matching) at `f01d042`), plus our additions |
| [`LeanMachine/RankCertificate.lean`](LeanMachine/RankCertificate.lean) | Arbitrary-field finite-dimensional rank identity from an intertwining defect | this repository |
| [`LeanMachine/ColorOrder.lean`](LeanMachine/ColorOrder.lean) | Ordered recovery and a nonlinear half-size record from port colors | this repository |
| [`LeanMachine/IncidenceTrimming.lean`](LeanMachine/IncidenceTrimming.lean) | Double counting and paid degree reduction for finite directed incidence | this repository |
| [`LeanMachine/MatrixRankCertificate.lean`](LeanMachine/MatrixRankCertificate.lean) | Tensor-product and block-rank inequalities, matrix-label certificates, and invariance under scalar extension | this repository |
| [`LeanMachine/LinearRecovery.lean`](LeanMachine/LinearRecovery.lean) | Linearization of arbitrary deterministic recovery on directed block codes and dimension bounds from matrix labels | this repository |
| [`LeanMachine/BucketChains.lean`](LeanMachine/BucketChains.lean) | Finite coordinatewise chain bounds and monotone bucket images | this repository |
| [`LeanMachine/ThresholdCuts.lean`](LeanMachine/ThresholdCuts.lean), [`ThresholdPullback.lean`](LeanMachine/ThresholdPullback.lean) | Signed cuts through partial monotone injections and exact exceptional-row bounds for band words | this repository |
| [`LeanMachine/CanonicalBuckets.lean`](LeanMachine/CanonicalBuckets.lean) | Concrete monotone interval partitions with a guaranteed minimum bucket size | this repository |
| [`LeanMachine/GraphBall.lean`](LeanMachine/GraphBall.lean) | Actual extended-distance ball cardinalities from maximum degree | this repository |
| [`LeanMachine/FinitePacking.lean`](LeanMachine/FinitePacking.lean) | Maximal disjoint finite families with bounded size and overlap | this repository |
| [`LeanMachine/PathPacking.lean`](LeanMachine/PathPacking.lean) | Short-path multiplicity and odd-length packing bounds | this repository |
| [`LeanMachine/SmithRankLoss.lean`](LeanMachine/SmithRankLoss.lean) | Exact modular rank loss from unimodular integer diagonalization, excluding zero factors | this repository |
| [`LeanMachine/KernelRangeBound.lean`](LeanMachine/KernelRangeBound.lean) | Kernel-range dimension and quotient-deficit bounds, with a split-generator criterion | this repository |
| [`LeanMachine/HomogeneousInflation.lean`](LeanMachine/HomogeneousInflation.lean) | Exact homogenization over arbitrary sheet groups, kernel equivalence, and finite-dimensional rate preservation | this repository |
| [`LeanMachine/FiniteProjection.lean`](LeanMachine/FiniteProjection.lean) | Restriction kernels, coordinate capacity, and single-coordinate nullity costs for arbitrary-field linear codes | this repository |
| [`SubspaceDefect`](LeanMachine/SubspaceDefect.lean), [`SubspaceFamilies`](LeanMachine/SubspaceFamilies.lean), [`SubspaceGrowth`](LeanMachine/SubspaceGrowth.lean), [`SubspaceGains`](LeanMachine/SubspaceGains.lean) | Exact subspace deficits, quotient dimensions, tight intersections, and coordinate-gain budgets | this repository |
| [`SubspaceRecovery`](LeanMachine/SubspaceRecovery.lean), [`LinearCodeRecovery`](LeanMachine/LinearCodeRecovery.lean) | Explicit recovery maps on images and closed restrictions; intrinsic coordinate-dual recovery preserving port ranks | this repository |
| [`SparseProjection`](LeanMachine/SparseProjection.lean), [`BlockRankSparsity`](LeanMachine/BlockRankSparsity.lean) | Actual-generator support counting and block-column rank payment from sparse block rows | this repository |
| [`CoordinateSplitting`](LeanMachine/CoordinateSplitting.lean), [`ProjectionFamilies`](LeanMachine/ProjectionFamilies.lean) | Exact coordinate capacity splitting for orthogonal idempotents and a weighted residual bound | this repository |
| [`InvariantKernel`](LeanMachine/InvariantKernel.lean) | Kernel-dimension transport through an injective intertwiner covering the entire kernel | this repository |
| [`IntervalCover`](LeanMachine/IntervalCover.lean) | Equal-size subcover and packing certificates for order-connected sets, and lossless fractional-cover rounding | this repository |
| [`FiniteIncidence`](LeanMachine/FiniteIncidence.lean) | Exact weighted multiplicity sums for indexed families and overlap bounds from disjoint color classes | this repository |
| [`MonotonePatches`](LeanMachine/MonotonePatches.lean) | Metric path variation from threshold crossings; sharp factor-three bounds for successful words and disjoint interval patches | this repository |
| [`ScheduledExcursion`](LeanMachine/ScheduledExcursion.lean) | Constructed unit-step excursions with arbitrary pauses, exhaustive nonadjacent returns, and the canonical first peak | this repository |
| [`ThinIntervals`](LeanMachine/ThinIntervals.lean) | Triangle-free interval forests, nonleaf component ranks, and periodic cuts bounding every surviving simple path | this repository |
| [`PeriodicPhases`](LeanMachine/PeriodicPhases.lean) | Unit-step chain bounds and protected phase averaging with exact residue counts and actual payment unions | this repository |
| [`FiniteOrbits`](LeanMachine/FiniteOrbits.lean) | Exact finite action orbits, removal of inactive actions, relabeling, and cardinality bounds for deterministic continuation | this repository |
| [`IntervalComponents`](LeanMachine/IntervalComponents.lean) | Component interval hulls equal their unions; distinct components have disjoint hulls | this repository |
| [`SourceBank`](LeanMachine/SourceBank.lean) | Finite lists of time maps, summed path variation, composition, and ordered-exception recurrences | this repository |
| [`PackedWords`](LeanMachine/PackedWords.lean) | Exact uniform banks for interval-supported actions on forests, packed by unordered component labels | this repository |
| [`ShiftedGrid`](LeanMachine/ShiftedGrid.lean) | Exact capped-diameter counts for separating grid shifts and same-block coordinate bounds | this repository |
| [`ShiftedGridUnion`](LeanMachine/ShiftedGridUnion.lean) | Distinct clipped raw-block unions and their all-shifts cardinality bound | this repository |
| [`IntervalOscillation`](LeanMachine/IntervalOscillation.lean) | Lifetime extrema and oscillation bounds preserving the exact interval overlap profile | this repository |
| [`GridPayment`](LeanMachine/GridPayment.lean) | Finite lifetime payments from capped oscillation, overlap, and variation; constant labels on unpaid lifetimes | this repository |
| [`CausalRecovery`](LeanMachine/CausalRecovery.lean) | Complete surviving source cones and functional recovery from local determinism and paid records | this repository |
| [`OrderedRecovery`](LeanMachine/OrderedRecovery.lean) | Reverse recovery from one helper and a coordinate complement along well-founded dependencies | this repository |
| [`FrozenBank`](LeanMachine/FrozenBank.lean) | Entire-block freezing by maximum slot oscillation, with exact window-overlap and variation bounds | this repository |
| [`GapErosion`](LeanMachine/GapErosion.lean) | Finite squared-gap area loss and selection-weight budget after integer erosion | this repository |
| [`CyclicGapUpper`](LeanMachine/CyclicGapUpper.lean) | Circular gap and area upper bounds from successor witnesses; ceiling bounds for floor-grid increments | this repository |
| [`QueryMovement`](LeanMachine/QueryMovement.lean) | Query-type counting from a movement clock in any pseudometric space; arbitrary partition width, maximum-slot charge and exact floor factor | this repository |
| [`CircleGridCapacity`](LeanMachine/CircleGridCapacity.lean) | Regular-grid capacity of circular balls and banks, via integer lifts; circle distance bounded by line distance | this repository |
| [`CyclicSelection`](LeanMachine/CyclicSelection.lean), [`CyclicArcSelection`](LeanMachine/CyclicArcSelection.lean) | Actual consecutive circular gaps, disjoint eroded arcs, and safe common cut-and-orientation counts | this repository |
| [`PeriodicStripe`](LeanMachine/PeriodicStripe.lean), [`PeriodicStripeSum`](LeanMachine/PeriodicStripeSum.lean) | Sharp circular stripe discrepancy and exact reindexing by transpose columns | this repository |
| [`SelectionAverage`](LeanMachine/SelectionAverage.lean), [`CyclicStripeAverage`](LeanMachine/CyclicStripeAverage.lean) | Finite selection double counting and actual stripe selection bounds from eroded circular gaps | this repository |
| [`FractionalCover`](LeanMachine/FractionalCover.lean) | Attained minimum finite fractional covers, capped optimal weights, and exact infeasibility at infinity | this repository |
| [`FractionalCoverBounds`](LeanMachine/FractionalCoverBounds.lean) | Feasible-weight upper bounds and finite ordinary covers as unit-weight fractional covers | this repository |
| [`TimeComponents`](LeanMachine/TimeComponents.lean) | Canonical finite path components, disjoint edge partitions, and raw-range variation charged once | this repository |
| [`OrbitLabelBudget`](LeanMachine/OrbitLabelBudget.lean) | Label counts from decreasing budgets along deterministic continuations, with a shared branching root | this repository |
| [`IntervalGapArea`](LeanMachine/IntervalGapArea.lean), [`FractionalIntervalGap`](LeanMachine/FractionalIntervalGap.lean) | Actual circular-gap energy from interval covers and minimum fractional weights, retaining weighted component incidence | this repository |
| [`PartitionEnergy`](LeanMachine/PartitionEnergy.lean) | Squared fibre masses, partition coarsening, and paid-set energy loss with the quadratic saving | this repository |
| [`WeightedCircularGap`](LeanMachine/WeightedCircularGap.lean), [`CircularSubdivision`](LeanMachine/CircularSubdivision.lean) | Actual gap partitions with arbitrary real edge lengths, pair-energy identities, and real-displacement/unit-weight adapters | this repository |
| [`AnchoredCircularCover`](LeanMachine/AnchoredCircularCover.lean), [`AnchoredGapErosion`](LeanMachine/AnchoredGapErosion.lean) | Anchored arcs preserve uncovered gap pairs; their union pays once for a sharper normalized area loss | this repository |
| [`CircularRefinement`](LeanMachine/CircularRefinement.lean) | Exact raw-coordinate gap area under a real subdivision, including the circle seam | this repository |
| [`IndexedSourceBank`](LeanMachine/IndexedSourceBank.lean) | List banks as finite families, preserving distinct value sets and summed slot variation | this repository |
| [`PaidAveraging`](LeanMachine/PaidAveraging.lean) | Signed credit and cost averaged together, with an optional mean-cost budget | this repository |
| [`ProfileCompactness`](LeanMachine/ProfileCompactness.lean) | Common subsequences for countable bounded profiles, inherited finite-sum budgets, summability and finite-tail limits | this repository |
| [`PrefixError`](LeanMachine/PrefixError.lean) | Finite payment normalization and limits of rounded widths and omitted-family budgets | this repository |
| [`TailMoments`](LeanMachine/TailMoments.lean) | Sorted summability gives decay faster than reciprocal rank; summable majorants control scaled tails, and positive tail floors force moment divergence | this repository |
| [`UniformGap`](LeanMachine/UniformGap.lean) | Excluding sequences with increasing dimension and two vanishing nonnegative costs gives a uniform positive gap | this repository |
| [`TailLiminf`](LeanMachine/TailLiminf.lean) | Zero extended-nonnegative lower limits are equivalent to arbitrarily late small values | this repository |
| [`PowerEnvelope`](LeanMachine/PowerEnvelope.lean) | Summable power-law moments and vanishing scaled tails; balanced power scales for covering and residual costs | this repository |
| [`BoundedLimsup`](LeanMachine/BoundedLimsup.lean) | Bounded real upper limits, converging-coefficient inequalities, and nonnegative scaling | this repository |
| [`InverseSquareTail`](LeanMachine/InverseSquareTail.lean) | Summable inverse-square envelopes and exact shifted-tail bounds from finite sum estimates | this repository |
| [`PowerTail`](LeanMachine/PowerTail.lean) | Quantitative real-power tail estimates and decay under sub-power multipliers, reusing integral comparison | this repository |
| [`CausalClosure`](LeanMachine/CausalClosure.lean) | Finite regressive transitive closures; maximal suppliers preserve the whole closure | this repository |
| [`ContinuationSuppliers`](LeanMachine/ContinuationSuppliers.lean) | Ordered-extension decompositions, actual supplier counts and maximal remaining landings | this repository |
| [`IntervalClusterErosion`](LeanMachine/IntervalClusterErosion.lean) | Anchored observable ranges over overlapping intervals, with a quadratic movement penalty | this repository |
| [`FiniteHullVariation`](LeanMachine/FiniteHullVariation.lean) | Finite time hulls, degenerate empty sets and complete-bank movement accounting | this repository |
| [`BoundedLiminf`](LeanMachine/BoundedLiminf.lean) | Explicit real lower-limit bounds, comparisons and converging lower bounds | this repository |
| [`VanishingTradeoff`](LeanMachine/VanishingTradeoff.lean) | Quadratic credit bounds and vanishing two-term tradeoffs on arbitrarily late good indices, including zero cost coefficients | this repository |
| [`ExtendedTradeoff`](LeanMachine/ExtendedTradeoff.lean) | Quantitative tradeoffs with unbounded nonnegative observables, extended lower limits, rate normalization and zero-cost divergence | this repository |
| [`RawIntervalCover`](LeanMachine/RawIntervalCover.lean) | Attained minimum closed-real-interval covers of finite raw coordinates; sharp two-block payment per short interval at every grid shift | this repository |

## External code

Each external file keeps its copyright header and gets a provenance comment below it. Each folder
that contains external code has a README. Both record:
- the source URL, the commit, the original path, and the SHA-256 of the original file;
- the licence, which must be Apache 2.0 or compatible, and the copyright holder;
- every change made, however small.

Before an external file is built here:
- fetch it at a pinned commit;
- read all of it;
- check that it runs no code at build time: no `#eval`, `run_cmd`, `initialize`, custom syntax or
  elaborators, `@[extern]`, `implemented_by` or I/O.

Keep changes to external files minimal, and put our own additions in separate files.

## Using it from a paper

In the paper's `lean/lakefile.toml`:

```toml
[[require]]
name = "leanMachine"
path = "../../lean-machine"
```

Readers then need the whole repository with its sibling directories in place, as for the papers'
dependencies on each other.

## Building and checking

In this directory:

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean Axioms.lean
```

`.lake/` is not committed. Locally, `.lake/packages` may be a symbolic link to a sibling paper's
packages at the same Mathlib revision, which avoids a second Mathlib download.

## License

Apache 2.0 ([`LICENSE`](LICENSE)). External files keep the copyright notices of their authors.
