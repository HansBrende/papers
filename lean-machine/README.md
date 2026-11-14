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
| [`LeanMachine/LastRowSupport.lean`](LeanMachine/LastRowSupport.lean) | One adjoined row leaves at most one new column under a four-arc exclusion; localized span/diagonal hypotheses over semirings without zero divisors | this repository |
| [`LeanMachine/OrderedRowRank.lean`](LeanMachine/OrderedRowRank.lean) | Exact prefix-rank and new-column accounting; supplied-order bound N ≤ a + h(rank − 2) + 1 | this repository |
| [`LeanMachine/ClosedCutRank.lean`](LeanMachine/ClosedCutRank.lean) | Rank lower bound across a closed principal cut; reusable induction for hereditary matrix classes; rank-one boundary under the four-arc exclusion | this repository |
| [`LeanMachine/SupportTraversal.lean`](LeanMachine/SupportTraversal.lean) | Rooted ordering of a finite directed relation from its root-containing cut condition | this repository |
| [`LeanMachine/SparseRankBounds.lean`](LeanMachine/SparseRankBounds.lean) | Every-field bound N ≤ k rank for nonzero diagonal, outgoing width k ≥ 2 and the four-arc exclusion; sharper reachable bound N + k ≤ k rank + 2 | this repository |
| [`LeanMachine/ThreeHelperRank.lean`](LeanMachine/ThreeHelperRank.lean) | Every-field half rank for nonzero diagonal, the four-arc exclusion, three outgoing helpers and one-way arcs entering rows with at most two; sharper charge retaining the chosen root's degree | this repository |
| [`LeanMachine/SparseAffineCodes.lean`](LeanMachine/SparseAffineCodes.lean) | Information-set bound for finite-alphabet subsets of affine fibres over any field, allowing coordinate-dependent embeddings; sparse-rank cardinality corollaries | this repository |
| [`LeanMachine/InvolutionCompletion.lean`](LeanMachine/InvolutionCompletion.lean) | Complete a partial matching on an even finite type while preserving every existing pair | this repository |
| [`LeanMachine/MatchingSeed.lean`](LeanMachine/MatchingSeed.lean) | Hall selection of one endpoint per pair meeting every loopless one-helper trap, with any one prescribed endpoint retained | this repository |
| [`LeanMachine/MatchingRecovery.lean`](LeanMachine/MatchingRecovery.lean) | Exact floor(N/2) generating set for a partial matching plus one loopless extra helper; arbitrary nonlinear codes and attained boundary-record cost | this repository |
| [`LeanMachine/CosetRecords.lean`](LeanMachine/CosetRecords.lean) | Exact attained-record count for a subgroup-invariant set, requiring coset separation only on that set; reuses Mathlib's saturation count | this repository |
| [`LeanMachine/DisjointSumsExtension.lean`](LeanMachine/DisjointSumsExtension.lean) | Exact partial-assignment extension criterion for arbitrary disjoint target sums; kernel shifts and coordinatewise additive-automorphism weights, with no finite alphabet or coordinate-type premise | this repository |
| [`LeanMachine/DisjointSumsRecords.lean`](LeanMachine/DisjointSumsRecords.lean) | Recovery-view separation of ordinary parity sums and exact attained-record counting; a chosen view per unrecorded block suffices, with compatibility supplied explicitly | this repository |
| [`LeanMachine/DisjointSumsCompatibility.lean`](LeanMachine/DisjointSumsCompatibility.lean) | Derives block compatibility and the free-coordinate condition from recovery and kernel invariance; local extraction needs no finite block index, and global separation/counting no longer assume compatibility | this repository |
| [`LeanMachine/RankCertificate.lean`](LeanMachine/RankCertificate.lean) | Arbitrary-field finite-dimensional rank identity from an intertwining defect | this repository |
| [`LeanMachine/ColorOrder.lean`](LeanMachine/ColorOrder.lean) | Ordered recovery and a nonlinear half-size record from port colors | this repository |
| [`LeanMachine/IncidenceTrimming.lean`](LeanMachine/IncidenceTrimming.lean) | Double counting and paid degree reduction for finite directed incidence | this repository |
| [`LeanMachine/SymmetricHelpers.lean`](LeanMachine/SymmetricHelpers.lean) | Symmetric/reflexive normalization of finite helper relations, reverse-degree budget and exact fixed-row/column overlap | this repository |
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
| [`RecoveryTrace`](LeanMachine/RecoveryTrace.lean), [`RecoveryFrobenius`](LeanMachine/RecoveryFrobenius.lean), [`RecoverySign`](LeanMachine/RecoverySign.lean) | Recovery-matrix bounds: weighted trace control on a fixed subspace's orthogonal complement, trace–rank–Frobenius inequality, and opposite eigenspaces under injective anticommuting maps | this repository; [backlog B1–B3](../lean-backlog/B-recovery-matrix.md) |
| [`RecoveryAlgebra`](LeanMachine/RecoveryAlgebra.lean), [`RecoveryTransfer`](LeanMachine/RecoveryTransfer.lean) | Arbitrary-field rank-defect and bipartite recovery bounds; trace limitations in positive characteristic; B1–B2 transferred through real or complex field embeddings | this repository; [backlog B field-scope review](../lean-backlog/B-recovery-matrix.md#field-extensions-and-algebraic-alternatives) |
| [`BoundedWeight/`](LeanMachine/BoundedWeight/) | Odd-word trace bounds; tensor-contraction closure; dimension, spectral and polynomial bounds; uniform asymptotic half-rate bound for all weights below a fixed bound | this repository; [backlog A1–A4](../lean-backlog/A-bounded-weight.md) |
| [`HermitianSpectrum`](LeanMachine/HermitianSpectrum.lean), [`SpectralCounting`](LeanMachine/SpectralCounting.lean) | Hermitian spectral moments and subspace dimensions at arbitrary thresholds; polynomial certificates for finite spectral counts | this repository; shared machinery for backlog A3 |
| [`OddPolynomialApproximation`](LeanMachine/OddPolynomialApproximation.lean) | Odd polynomial approximation of continuous odd functions on symmetric intervals, reusing Mathlib's Weierstrass theorem | this repository; shared machinery for backlog A4 |
| [`WholeRow/`](LeanMachine/WholeRow/) | Whole-row recovery codes: joint frontier-rank bound, invertible-block second rule, and a local-invertibility refinement | this repository; [backlog C1–C2](../lean-backlog/C-second-rule.md) |
| [`SequentialDimension`](LeanMachine/SequentialDimension.lean) | Code dimension from conditional coordinate spaces when all earlier coordinates vanish | this repository; shared machinery for backlog C |
| [`LeanMachine/HomogeneousInflation.lean`](LeanMachine/HomogeneousInflation.lean) | Exact homogenization over arbitrary sheet groups, kernel equivalence, and finite-dimensional rate preservation | this repository |
| [`LeanMachine/FiniteProjection.lean`](LeanMachine/FiniteProjection.lean) | Restriction kernels, coordinate capacity, single-coordinate nullity costs, and capacity of injective observations with known zero coordinates | this repository |
| [`SubspaceDefect`](LeanMachine/SubspaceDefect.lean), [`SubspaceFamilies`](LeanMachine/SubspaceFamilies.lean), [`SubspaceGrowth`](LeanMachine/SubspaceGrowth.lean), [`SubspaceGains`](LeanMachine/SubspaceGains.lean) | Exact subspace deficits, quotient dimensions, tight intersections, and coordinate-gain budgets | this repository |
| [`FiniteCodimension`](LeanMachine/FiniteCodimension.lean) | Relative codimension bounds for finite intersections and sums, and separately charged images of two joint observations | this repository |
| [`SubspaceRecovery`](LeanMachine/SubspaceRecovery.lean), [`LinearCodeRecovery`](LeanMachine/LinearCodeRecovery.lean) | Explicit recovery maps on images and closed restrictions; intrinsic coordinate-dual recovery preserving port ranks | this repository |
| [`SparseProjection`](LeanMachine/SparseProjection.lean), [`BlockRankSparsity`](LeanMachine/BlockRankSparsity.lean) | Actual-generator support counting and block-column rank payment from sparse block rows | this repository |
| [`CoordinateSplitting`](LeanMachine/CoordinateSplitting.lean), [`ProjectionFamilies`](LeanMachine/ProjectionFamilies.lean) | Exact coordinate capacity splitting for orthogonal idempotents and a weighted residual bound | this repository |
| [`InvariantKernel`](LeanMachine/InvariantKernel.lean) | Kernel-dimension transport through an injective intertwiner covering the entire kernel | this repository |
| [`IntervalCover`](LeanMachine/IntervalCover.lean) | Equal-size subcover and packing certificates for order-connected sets, and lossless fractional-cover rounding | this repository |
| [`FiniteIncidence`](LeanMachine/FiniteIncidence.lean) | Exact weighted multiplicity sums for indexed families and overlap bounds from disjoint color classes | this repository |
| [`IncidenceSecondMoment`](LeanMachine/IncidenceSecondMoment.lean) | Finite occupancy second moments from marginal counts, and a real-exponent weight bound | this repository |
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
| [`IntervalQueries`](LeanMachine/IntervalQueries.lean) | Lost repeated query types charged to deleted occurrences; edge-disjoint interval bills and movement bounds with independent internal and grouping thresholds | this repository |
| [`DisjointSums`](LeanMachine/DisjointSums.lean) | Surjective sums on disjoint nonempty supports over finite abelian groups; exact fibres and ignored-coordinate independence counts | this repository |
| [`SubsetPlacement`](LeanMachine/SubsetPlacement.lean) | Explicit subset placement parities and full-input recovery from the specified raw rows, with arbitrary repetitions and abelian-group entries | this repository |
| [`CyclicGapTails`](LeanMachine/CyclicGapTails.lean) | Actual sorted squared gaps expressed as weighted counts of empty forward arcs | this repository |
| [`SubsetGapCounting`](LeanMachine/SubsetGapCounting.lean) | Exact fixed-size-subset gap moments and mean normalized gap area, including singletons and the full set | this repository |
| [`CyclicGapScaling`](LeanMachine/CyclicGapScaling.lean) | Positive integer scaling of sorted circular gaps preserves their normalized area | this repository |
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
| [`BoundedLiminf`](LeanMachine/BoundedLiminf.lean) | Explicit real lower-limit bounds, comparisons, converging lower bounds and affine upper bounds with vanishing errors | this repository |
| [`VanishingTradeoff`](LeanMachine/VanishingTradeoff.lean) | Quadratic credit bounds and vanishing two-term tradeoffs on arbitrarily late good indices, including zero cost coefficients | this repository |
| [`ExtendedTradeoff`](LeanMachine/ExtendedTradeoff.lean) | Quantitative tradeoffs with unbounded nonnegative observables, extended lower limits, rate normalization and zero-cost divergence | this repository |
| [`RawIntervalCover`](LeanMachine/RawIntervalCover.lean) | Attained minimum closed-real-interval covers of finite raw coordinates; sharp two-block payment per short interval at every grid shift | this repository |
| [`FixedSubsetLimits`](LeanMachine/FixedSubsetLimits.lean) | Fixed-size binomial ratios, rounded capped capacities and inverse-power divergence, reusing Mathlib asymptotics | this repository |
| [`CausalFields`](LeanMachine/CausalFields.lean) | Local deterministic fields on ranked networks, projected-support autonomy and complete entering-cut recovery | this repository |
| [`CausalCutCapacity`](LeanMachine/CausalCutCapacity.lean) | Joint support cardinality and bit-capacity bounds from causal cut recovery | this repository |
| [`CausalCollector`](LeanMachine/CausalCollector.lean) | Local output collection on a memory interval, exact prefix capacity and delay-sum volume, and sink-cut support bounds | this repository |
| [`FiniteFlow`](LeanMachine/FiniteFlow.lean) | Real-capacity max-flow/min-cut on finite directed multigraphs, preserving parallel edges; exact-demand flows from cut bounds | this repository |
| [`FlowPaths`](LeanMachine/FlowPaths.lean) | Weighted paths carrying a flow's full nonnegative source value, with traversal loads bounded by the flow and at most one path per positive edge | this repository |
| [`FlowPathMap`](LeanMachine/FlowPathMap.lean) | Incidence-preserving path maps and traversal counts; path lifting through an injective vertex map when all outgoing arrows lift | this repository |
| [`FlowWalks`](LeanMachine/FlowWalks.lean) | Undirected walks retaining physical edge identities, with both orientations charged; actual backward spine paths and exact traversal counts | this repository |
| [`FiniteWeightedFamily`](LeanMachine/FiniteWeightedFamily.lean) | Finite indexed weighted families, disjoint collection and probability mixtures; exact mass and observable sums retain multiplicity | this repository |
| [`FlowDistance`](LeanMachine/FlowDistance.lean) | Physical walk volume equals length; ordinary undirected distance bounds every walk, allowing parallel edges, loops and repeated traversals | this repository |
| [`LogarithmicRadius`](LeanMachine/LogarithmicRadius.lean) | An explicit positive radius from `x >= A^4`, with `A^ell <= sqrt(x)` and `ell >= log(x)/(4 log(A))` | this repository |
| [`FreeGroupResiduallyP`](LeanMachine/FreeGroupResiduallyP.lean) | Free groups of finite rank are residually finite `p`-groups (a matrix form of the Magnus embedding), and strictly smaller normal subgroups of `p`-power index | this repository (*Lück Approximation Fails in Positive Characteristic*) |
| [`PackedMatrixCheck`](LeanMachine/PackedMatrixCheck.lean) | Kernel-evaluated checks of matrix identities over `𝔽₃` by Kronecker substitution (base-512 packed rows) | this repository (same paper) |
| [`KernelCertificate`](LeanMachine/KernelCertificate.lean) | Kernel bounds from an invertible minor, and injectivity of a connecting map into the cokernel | this repository (same paper) |
| [`CyclicBandedKernel`](LeanMachine/CyclicBandedKernel.lean) | The basis `uᵏ` of `K[C_N]` when `uᴺ = 0`, and kernels of banded operators `B₀ + u B₁ + u² B₂` | this repository (same paper) |
| [`FinitePartition`](LeanMachine/FinitePartition.lean) | Exact fibre-deficit moments and confidence tails from attained label counts, on arbitrary finite source subsets | this repository |
| [`BinomialTail`](LeanMachine/BinomialTail.lean) | Sharp exponential half-threshold bounds for finite binomial sums, derived from the geometric mean and the binomial theorem | this repository |
| [`OddPowerChoice`](LeanMachine/OddPowerChoice.lean) | Positive odd exponents under every power cap, with exact exponential-to-polynomial loss conversion | this repository |
| [`SlowIndex`](LeanMachine/SlowIndex.lean) | Diverging family indices with square-root size budgets, without monotone sizes; vanishing padding costs | this repository |
| [`BlockRanking`](LeanMachine/BlockRanking.lean) | Exact permutation counts for ranking disjoint block sets and LYM-type separation lower bounds | this repository |
| [`ThresholdRefinement`](LeanMachine/ThresholdRefinement.lean) | Common refinement of finite threshold sets into elementary intervals on which clamped comparisons are constant | this repository |
| [`PermutationFixedSpace`](LeanMachine/PermutationFixedSpace.lean) | Permutation-invariant coordinate spaces as functions on orbits, with a characteristic-free Burnside dimension formula | this repository |
| [`MonotoneNormalization`](LeanMachine/MonotoneNormalization.lean) | Reparametrization of a coordinatewise monotone real curve by its surjective coordinate sum, yielding normalized 1-Lipschitz coordinates and preserving every curve point | this repository |
| [`MonotoneChainEnvelope`](LeanMachine/MonotoneChainEnvelope.lean) | Continuous monotone interpolation of finite coordinatewise chains, with surjective coordinate sum and exact normalized knots | this repository |
| [`OrderConflictChart`](LeanMachine/OrderConflictChart.lean) | Exact finite order-conflict charts, coordinate-specific error allowances, and the converse twice-error bound | this repository |
| [`ProtectedIntervals`](LeanMachine/ProtectedIntervals.lean) | Strict integer cores, closed error fringes, coverage and disjointness, with exact cardinality bounds from floor and ceiling endpoints | this repository |
| [`BoundedTuples`](LeanMachine/BoundedTuples.lean) | Exact bounded-sum tuple counts, monotone counter menus, and signed sampled unit-path encodings | this repository |
| [`SparseRecords`](LeanMachine/SparseRecords.lean) | Exact support/value records and sparse dependent-tuple bounds, including input-dependent supports | this repository |
| [`SparseBinomial`](LeanMachine/SparseBinomial.lean) | Weighted sparse binomial menus, uniform small-density estimates and sublinear logarithmic rates | this repository |
| [`FiniteFieldOrbit`](LeanMachine/FiniteFieldOrbit.lean) | Generated-field degree as the actual Frobenius period, with exact conjugate counts | this repository |
| [`FiniteLinearHash`](LeanMachine/FiniteLinearHash.lean) | Exact collision fibres for finite-field linear hashes, common-input-set selection and local syndrome updates | this repository |
| [`OwnerProgram`](LeanMachine/OwnerProgram.lean), [`BlockProgram`](LeanMachine/BlockProgram.lean), [`BlockProgramExports`](LeanMachine/BlockProgramExports.lean) | Actual causal programs, full product transcript fibres, and exact switch-state/version records | this repository |
| [`BlockProgramCoarsen`](LeanMachine/BlockProgramCoarsen.lean), [`BlockSpan`](LeanMachine/BlockSpan.lean) | Evaluation-preserving owner grouping and one common grid paying actual state variation and writer/reader spans | this repository |
| [`ReadOnlyProgram`](LeanMachine/ReadOnlyProgram.lean) | Literal read-only state transitions and query-local recovery, with no transition access to emitted output | this repository |
| [`WeightedGrid`](LeanMachine/WeightedGrid.lean), [`GridPartition`](LeanMachine/GridPartition.lean) | Simultaneous nonnegative grid charges and exact finite row/column width bounds | this repository |
| [`PolynomialMenus`](LeanMachine/PolynomialMenus.lean), [`MonotoneSamples`](LeanMachine/MonotoneSamples.lean) | Uniform small polynomial-menu costs and exact recovery of monotone samples from their multiset | this repository |
| [`FiniteUniformProbability`](LeanMachine/FiniteUniformProbability.lean), [`FiniteBoundedDifferences`](LeanMachine/FiniteBoundedDifferences.lean), [`FiniteUniformWindows`](LeanMachine/FiniteUniformWindows.lean) | Actual finite-product averages/probabilities, bounded-differences tails and cyclic-window locality | this repository |
| [`ReadOnlyWindows`](LeanMachine/ReadOnlyWindows.lean), [`OrderedEmissionWindows`](LeanMachine/OrderedEmissionWindows.lean), [`OptionalReadSlices`](LeanMachine/OptionalReadSlices.lean) | Actual execution slices, designated output windows, and telescoping optional-read counts | this repository |
| [`FiniteTopSets`](LeanMachine/FiniteTopSets.lean), [`FiniteObservationTopSets`](LeanMachine/FiniteObservationTopSets.lean) | Actual largest atoms and one retained event controlling every attained conditional observation | this repository |
| [`FiniteTimeGrid`](LeanMachine/FiniteTimeGrid.lean), [`FiniteWeightedPigeonhole`](LeanMachine/FiniteWeightedPigeonhole.lean) | Exact preceding intervals and a heavy attained cell under an arbitrary finite law | this repository |
| [`FiniteTapeGraph`](LeanMachine/FiniteTapeGraph.lean), [`FiniteMaskFibres`](LeanMachine/FiniteMaskFibres.lean) | Literal one-write/unit-move tape graphs, bounded balls, and exact head/erasure fibre costs | this repository |
| [`FiniteSmallFibres`](LeanMachine/FiniteSmallFibres.lean), [`FiniteCoordinateFibres`](LeanMachine/FiniteCoordinateFibres.lean) | Strict small-fibre bounds and coordinate-agreement injections | this repository |
| [`BoundedTuplePadding`](LeanMachine/BoundedTuplePadding.lean) | Sum-preserving zero padding and recovery of bounded tuples | this repository |
| [`LogarithmicDensity`](LeanMachine/LogarithmicDensity.lean) | Positive densities meeting any explicit small logarithmic information budget, via Mathlib continuity | this repository |
| [`FiniteIntervalSelection`](LeanMachine/FiniteIntervalSelection.lean) | One common preceding interval and unordered coordinate set, selected under the original finite law | this repository |
| [`FiniteSourceEscape`](LeanMachine/FiniteSourceEscape.lean) | Exact uniform-source masses and the half-mass complement of an exponentially smaller bad set | this repository |
| [`BinaryBudgets`](LeanMachine/BinaryBudgets.lean) | Exact integer bit budgets for finite-state products, default states and polynomial record menus | this repository |
| [`FiniteOrdinalGuards`](LeanMachine/FiniteOrdinalGuards.lean) | Exact finite counts for delayed outputs, closed look-ahead intervals and terminal ordinals | this repository |
| [`LeanMachine/ShuffleShear/`](LeanMachine/ShuffleShear/) | Finite transition tables and `O(L)`-time execution proofs for Stone's `3`-work-tape perfect shuffle, `2`-work-tape inverse unshuffle, and `2`-work-tape within-row cyclic shear under row-major binary matrix encoding | this repository |

The shared module [`ContextPruning`](LeanMachine/ContextPruning.lean) supplies finite
weighted context pruning: one subset retains density in every attained context,
with a half-mass conditional bound independent of how many observed variables
share those contexts. It originates in *Macroscopic Information Transfer in
Adaptive Tape Transposition*.

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
