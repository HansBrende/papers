# Formalization plan

This records completed formalization and the remaining specification.
**Eighteen of the 32 numbered results are Lean-verified: Lemma 2.3, family
accounting; Lemma 2.5, shadow and successful-word variation; Lemma 2.6,
the Q2 overlap forest and protected phases; Theorem 2.7, the exact source
bank; Lemma 2.8, paid residual-source recovery; Theorem 2.9, cyclic freezing; Lemma 3.2,
fractional interval covers; Lemma 3.3, the fractional raw-source gap bound;
Lemma 3.4, anchored erosion; Theorem 3.5, complete covers with the full paid cost;
Corollary 3.6, counting terminal core orbits; Theorem 4.2, necessary hop tails;
Corollary 4.3, the uniform one-exception deficit; Corollary 4.4, common envelopes;
Corollary 4.5, the fixed finite skeleton; Theorem 4.6, necessary reciprocal-cover
complexity and its inverse-square probability consequence;
Corollary 4.7, both uniform mean-cover criteria;
and Lemma 8.3, the attached short-distance count.** Definitions 2.1, 2.2, 2.4,
3.1 and 4.1 are also formalized, including joint-profile existence, mass
bounds and vanishing tails. The other 14 results
retain complete written proofs.

The [statement index](FORMALIZATION-INDEX.md) is generated from the actual
manuscript in section order. It lists every numbered definition and result,
links to its statement, and records a fingerprint. Exact statements include
their surrounding model definitions and notation; the short descriptions
below do not replace those premises.

## Completed: complete families and family accounting

[`SourceCovers/FamilyAccounting.lean`](lean/SourceCovers/FamilyAccounting.lean)
uses Paper 8's canonical actual hops, first-maximum owners, family keys,
nesting, outer-span, height and unit-step distance results. No earlier
source is copied or modified. Complete families are formed before selection.
The finite walk extends constantly to the reused natural-time model, and
an explicit indexing lemma identifies span membership with elementary edges.

The family-size bound retains the owner's position:
`h_G <= min(o_G - p_G, U_G - o_G)`. Total hop mass is bounded by the actual
sum of boundary overlaps, and variation satisfies an exact weighted
overlap identity. The shared
[`FiniteIncidence`](../lean-machine/LeanMachine/FiniteIncidence.lean)
module proves that identity once for any additive commutative monoid.
It also bounds multiplicity from disjoint color classes, including empty
families and zero colors.

The boundary-lower set has an exact membership theorem: restricting its
union to active families omits no crossing hop. Its strongest bound keeps
the crossing-hop counts of those families, then derives `1 + N a` from
local overlap and size bounds without requiring unit steps or nesting.
The original Q2 mass and variation estimates are derived directly by
`q2_accounting`. The new profiles are retained for later payment estimates;
the downstream uniform exclusions still use the original special cases.
The admissible-geometry definition and its local-computation data are also
formalized. The exact source bank is verified below.

## Completed: clipped shadows and successful-word variation

[`SourceCovers/ClippedShadows.lean`](lean/SourceCovers/ClippedShadows.lean)
defines each shadow from its complete family's actual hop ends and starts.
The held value is initially the owner and changes to each ended hop's start,
then is clipped at the outer lower endpoint plus one. Nesting identifies
the value at every actual end; unpaid lowers are represented exactly.
The full finite-word orbit includes the empty word and does not gate paths
at other paid vertices.

The shared
[`MonotonePatches`](../lean-machine/LeanMachine/MonotonePatches.lean)
module supplies the reusable proof. A monotone patch of identity has at
most one downward crossing per threshold, hence at most three crossings.
Mathlib's finite-path triangle inequality and the existing shared incidence
identity turn this into a variation bound for every metric-valued path.
The stronger form keeps actual crossing multiplicities and allows different
source and target horizons. A single-patch bound only needs preservation of
the finite time range, not regression.

Disjoint packing preserves the factor three independently of the family
count. Mathlib's order-convex preimage lemmas show that a word's success
domain is an interval; composition preserves one monotonicity orientation.
The endpoint decreases time, and its identity extension has the same
factor-three bound independently of word length. Empty words, repeated
families and empty success domains are included. A finite regressive patch
attains the factor three; this is sharpness for the general patch class,
not a claim about an optimal source-bank constant or a new obstruction.

The original real-path statements are direct specializations at horizon
`T - 1`; no unit-step premise on the argument path is used. The finite walk
premise is needed to identify the concrete shadow with actual return hops,
not for the shared variation argument. No hypothesis was added to the
original lemma. Protected phases and complete core-orbit bounds are now
formalized below, as is packed-bank completeness. Full functional recovery
through residual dependencies is now verified separately below.

## Completed: fractional interval covers

[`SourceCovers/IntervalCover.lean`](lean/SourceCovers/IntervalCover.lean)
re-exports the general results from
[`LeanMachine/IntervalCover.lean`](../lean-machine/LeanMachine/IntervalCover.lean).
`exists_cover_packing` constructs a subcover and an equally large packing:
each original set contains at most one packing point.
`exists_subcover_le_weight` bounds a subcover by the total weight of any
feasible nonnegative fractional cover, using a shared finite double-counting
lemma. No linear-programming formalization or duplicated proof is needed.

The statement strengthens the original closed-real-interval formulation
to arbitrary order-convex sets in any linear order, allows an empty target,
and provides the unweighted packing certificate. Finite extrema and sums
reuse Mathlib. It does not assume boundedness, closedness, positive weights,
or a fractional optimum. These are standard interval-cover principles, not
claims of a new covering theorem. The later raw-source gap bound uses the
rounding conclusion unchanged and is now formalized below.

## Completed: minimum core covers and the fractional raw-source gap

[`CoreFractionalCover`](lean/SourceCovers/CoreFractionalCover.lean) uses every
root in `Fin T`, complete core orbits, and the shared
[`FractionalCover`](../lean-machine/LeanMachine/FractionalCover.lean) minimum.
Mathlib's extreme value theorem applies after capping weights at one; the
extended value is infinite exactly for infeasibility. A finite cover exists
if and only if all target coordinates were visited. Root membership gives
this without using the terminal-orbit decomposition, and the actual complete
source bank satisfies it at every computation time.

[`FractionalGap`](lean/SourceCovers/FractionalGap.lean) derives the actual
circular point-gap bound with denominator `2(2K+1) kappa`, improving the
original `4(K+1) kappa`. The stronger versions retain the actual weighted
component-incidence count and variation on the union of nondistinguished
original edges. No unit-speed premise on the raw path or rank-phase premise
is required: any retained subset of the actual Q2 core is allowed.

The proof reuses interval rounding, sorted circular gaps, finite incidence
accounting, path oscillation, and Mathlib's Cauchy--Schwarz inequality.
[`TimeComponents`](../lean-machine/LeanMachine/TimeComponents.lean) fixes
components before selecting covering orbits; their internal edges partition
the allowed edges in the horizon `T-1`. The
[`CoreCoverComponents`](lean/SourceCovers/CoreCoverComponents.lean) bound
counts the shared root once and charges each change to a disappearing
distinguished owner. It retains the smaller root-dependent owner count.
[`FractionalIntervalGap`](../lean-machine/LeanMachine/FractionalIntervalGap.lean)
transfers fractional weights to these shared intervals and rounds them;
[`IntervalGapArea`](../lean-machine/LeanMachine/IntervalGapArea.lean) counts
actual exposed circular gaps, including singleton and seam cases.

The statement is stronger than the original with no added hypothesis.
The manuscript propagates the improved factor through its dependent written
bounds. This is a finite constant improvement, not an enlargement of the
uniform impossibility classes or a decision of (T).

## Completed: anchored erosion with a quadratic saving

[`AnchoredErosion`](lean/SourceCovers/AnchoredErosion.lean) reuses the shared
[`AnchoredGapErosion`](../lean-machine/LeanMachine/AnchoredGapErosion.lean)
theorem and supplies real-coordinate and integer-coordinate adapters.
The original loss `E/L` is a direct consequence of the stronger
`e - e²/2`, where `e = min(E/L, 1)`. The bound uses the actual union of
covered elementary edges, not a sum that duplicates overlaps. It retains
all original cases, including omitted old anchors and singleton/full-circle
arcs. No disjointness or residual-gap certificate is assumed.

The formal representation is a common finite subdivision with arbitrary
nonnegative real edge lengths and positive circumference. All points and
arc endpoints are vertices. [`CircularSubdivision`](../lean-machine/LeanMachine/CircularSubdivision.lean)
identifies the weighted lengths with real lifted endpoint displacements;
unit weights give the existing `GapErosion.pointArea` exactly. The paper
states this representation explicitly. No intrinsic `AddCircle` or
Haar-measure conversion theorem is claimed.

[`WeightedCircularGap`](../lean-machine/LeanMachine/WeightedCircularGap.lean)
reuses the existing sorted gaps and proves that their elementary edges form
a partition. [`AnchoredCircularCover`](../lean-machine/LeanMachine/AnchoredCircularCover.lean)
proves from actual arc membership that two uncovered edges sharing an old
gap still share a new gap. [`PartitionEnergy`](../lean-machine/LeanMachine/PartitionEnergy.lean)
then bounds the energy loss by the mass of ordered pairs touching the paid
set: `2LC - C²`, where `C` is its actual length. Its reusable intermediate
bound retains the old partition energy on unpaid pairs. Nonnegativity of
partition energy holds even for signed weights; the loss bound requires
nonnegative lengths.

The manuscript's cover credit uses the stronger loss. Later estimates
using `E/L` remain valid relaxations. This improves finite geometric credit
without proving that arbitrary tape geometries have economical covers.

## Completed: attached short-distance count

[`SourceCovers/NativeShortCount.lean`](lean/SourceCovers/NativeShortCount.lean)
defines the attached short-bit set and proves its exact equivalence to a
ball cover without diagram-validity or positive-block-length assumptions.
The local union-count bound also needs no validity or block-length bound.

For valid diagrams with `1 <= r <= d b`, `card_rowSinkBits_le` sharpens the
first paper's per-row output-block count from `2b` to `b`.
`card_attachedShortBits_le_profile` retains the actual row and ball sizes;
`card_attachedShortBits_le` yields the `(2n-1)b` bound capped
by the total input length, including zero block length and zero radius.
The first-block correction uses the input head starting at zero and the
earlier unit-step distance lemma. Arbitrary entry width and explicit
exclusion of unattached rows are preserved.

Reuse includes the first paper's output interval and coordinate lemmas,
its ball and row counts, and Mathlib's injection and finite-union cardinality
bounds. The existing build adapter reads the first paper's original sources;
none are copied or changed. The [generated axiom audit](lean/PaperAxioms.lean)
reports only `propext`, `Classical.choice` and `Quot.sound` for the cited
declarations. The causal-group routing theorem and its asymptotic
corollary remain unformalized. The improved constant does not change that
corollary's asymptotic conclusion.

## Completed: Q2 overlap forest and protected phases

[`SourceCovers/ProtectedPhases.lean`](lean/SourceCovers/ProtectedPhases.lean)
instantiates three shared modules with the actual complete families:

- [`ThinIntervals`](../lean-machine/LeanMachine/ThinIntervals.lean) proves
  acyclicity for triangle-free interval overlap graphs, connectivity after
  removing original leaves, injective component ranks and consecutive ranks
  along nonleaf edges. The induced nonleaf graph has degree at most two.
  Cutting one residue of original nonleaf ranks bounds **every** surviving
  simple path by `M+1` vertices. No deletion of leaves is needed.
- [`PeriodicPhases`](../lean-machine/LeanMachine/PeriodicPhases.lean) proves
  the integer-chain and protected-payment bounds. The available-phase count
  is exactly `M-F`. The sharp sum charges only families in admissible phases;
  the paper's bound relaxes this to actual lower supports of unprotected
  nonleaves, then to their hop mass. Large protected sets are allowed when
  their nonleaves leave a residue unused.
- [`FiniteOrbits`](../lean-machine/LeanMachine/FiniteOrbits.lean) removes
  inactive actions without changing endpoints, preserves orbits under
  relabeling, and proves exact bounded-depth closure. A root with at most
  two first-step values and deterministic continuation has at most `2M+3`
  orbit values. This is an equality with the original finite-word orbit,
  not a replacement by an arbitrary overcover.

The source adapter proves successful words have distinct family names and
form simple overlap paths. Ranks and nonleaf status always refer to the
original core. No unit-speed-walk premise is needed for these results.
The previous all-family payment bound follows by enlarging the nonleaf
mass; `nonleaf_mass_le_total` records that comparison. The later bank proof
now explicitly treats uncut components of one or two vertices, preserving
its constants for `M >= 2`. The exact packed source bank is now verified separately below; its uniform
variation bound does not follow merely from pointwise orbit cardinality.

## Completed: the exact packed source bank

[`ExactSourceBank.lean`](lean/SourceCovers/ExactSourceBank.lean) assembles
Theorem 2.7 with all original constants, arbitrary upper bounds on the
exception count, exact complete orbits, complete-core-orbit covers, root
reads, raw cardinality, and closure across all originally selected unpaid
actual edges. Its variation bound holds for every pseudometric-valued path
and every finite horizon. The unit-speed specialization gives `C_q (T-1)`.
No bound on the core family count is needed; unit work walks enter only
when identifying shadows with actual hops.

The proof is split by mathematical obligation:

- Shared [`IntervalComponents`](../lean-machine/LeanMachine/IntervalComponents.lean)
  identifies component interval hulls and proves them disjoint, without
  thinness. [`PackedWords`](../lean-machine/LeanMachine/PackedWords.lean)
  uses unique forest paths, decreasing owners, and unordered endpoint
  labels to construct one packed map per label pair. The existing
  factor-three patch theorem supplies its uniform variation bound.
- [`SpineGeometry`](lean/SourceCovers/SpineGeometry.lean) labels surviving
  components injectively with the `M-1` nondeleted rank residues. Original
  isolated vertices stay in the leaf pack. One vertex of each two-vertex
  component joins the spine, making all remaining leaf spans disjoint.
- [`LeafSandwich`](lean/SourceCovers/LeafSandwich.lean) proves that internal
  successful-word vertices lie on the spine. The four endpoint-leaf
  choices give exact core orbits, `4` times the slots and `16` times the
  variation coefficient.
- Shared [`SourceBank`](../lean-machine/LeanMachine/SourceBank.lean) proves
  list composition and the ordered-exception count/variation recurrences.
  [`ExceptionalBank`](lean/SourceCovers/ExceptionalBank.lean) proves
  exactness for actual shadows and the terminal complete-core-orbit cover.
  Its list version even allows repeated exceptions and core overlap;
  constants count list entries. Finite exception sets are sorted once.
- [`RawBankRecovery`](lean/SourceCovers/RawBankRecovery.lean) proves that
  every actual lower of a deleted core family is paid. Consequently the
  closure statement quantifies over the **original** selected families,
  not merely survivors. Passing to raw coordinate images preserves
  inclusion and can only reduce cardinality.

No statement was weakened and no fixed-word representation of packed slots
was assumed. Maps are chosen from geometry before the root or argument
path. Core continuation is complete and is not truncated at other paid
vertices. These results verify the selected-family source engine. The next
completed lemma handles recovery through all remaining dependencies.

## Completed: paid residual-source recovery

[`ResidualRecovery.lean`](lean/SourceCovers/ResidualRecovery.lean)
assembles Lemma 2.8 in `paid_residual_recovery`: actual residual payments,
the strengthened cost chain, complete-cone containment and decoding of the
whole record at every root. The same payment set serves all roots. Selected
edges preserve value-set inclusion, allowing the matching slot to change;
every other parent edge is residual. A revealed root still retains its
direct read and all unpaid parents.

- [`ResidualGeometry`](lean/SourceCovers/ResidualGeometry.lean) defines
  the actual unpaid residual lowers and their latest successors. Its exact
  live-boundary characterization identifies lifetime multiplicity with
  distinct actual lowers. Vertices with no residual successor have zero
  oscillation, so the sum over all unpaid vertices equals the actual-lower sum.
- [`ResidualPayment`](lean/SourceCovers/ResidualPayment.lean) assembles the
  cost bounds. The cost and recovery proofs use four reusable shared modules.
  `ShiftedGrid` counts exactly `min(w, z)` separating
  shifts for a range of oscillation `z`, using Mathlib's residue permutation.
  `IntervalOscillation` reuses finite-path distance and incidence sums to
  retain the exact overlap profile. `GridPayment` supplies the union bound
  and an averaging witness. `CausalRecovery` uses strong induction and
  Mathlib's factorization theorem to construct a decoder on arbitrary
  correctness sets. No independence or linearity is assumed.

The original `H V / w` estimate follows from a stronger chain retaining
per-slot capped oscillations and the actual boundary profile. The initial
and new payments are disjoint. Time `n` is the last vertex, corresponding
to `T - 1` in the manuscript; closed lifetimes and elementary boundaries
therefore match exactly. Local determinism is a one-step premise, not an
assumption of global recovery. Bank anchors need not lie in the input range
in Lean, provided the direct reads do and belong to the bank. The output
decoder is a component of the stronger whole-record decoder. Its nonempty
record alphabet is automatic for the manuscript's actual computations.
No original hypothesis was strengthened or conclusion weakened.

## Completed: cyclic freezing

[`CyclicFreezing.lean`](lean/SourceCovers/CyclicFreezing.lean) verifies
Theorem 2.9 from the actual frozen anchor sets and transpose append times.
`cyclic_freezing` improves the additive error from `(W+1)/2` to
`(W-b+1)/2`. `cyclic_freezing_oscillation` retains the sum of the maximum
slot oscillations in each column window; this sum is at most the original
total bank variation. Its input-range premise is needed only at frozen
anchors. No original hypothesis is strengthened or conclusion weakened.

- Shared `CyclicSelection` constructs the actual sorted circular gaps and
  disjoint eroded arcs. `CyclicArcSelection` injects at least `a+1` safe
  cut-and-orientation choices for every point of an uncovered arc of length
  `a`. We only need this lower bound, not exact complement enumeration.
- `PeriodicStripe` proves the sharp discrepancy `b(1-1/d)` using periodic
  prefix counts. `SelectionAverage`, `PeriodicStripeSum`, `GapErosion`
  and `CyclicStripeAverage` supply finite double counting, exact column
  reindexing, area loss and the per-column estimate. Empty eroded arcs
  incur no discrepancy cost.
- `FrozenBank`, [`ColumnWindows`](lean/SourceCovers/ColumnWindows.lean)
  and [`FrozenSourceBank`](lean/SourceCovers/FrozenSourceBank.lean) cover
  entire clipped linear blocks in the circle. They reuse earlier interval
  variation bounds and the first paper's actual transpose-position formula.
- Shared `OrderedRecovery` gives reverse recovery along any well-founded
  dependency relation. [`OrderedRecoveryEntropy`](lean/SourceCovers/OrderedRecoveryEntropy.lean)
  reuses the second paper's entropy library for arbitrary laws and weighted
  selections. [`CyclicRecoveryEntropy`](lean/SourceCovers/CyclicRecoveryEntropy.lean)
  averages over one common order, with the same helper for all columns.

The main theorem charges the helper's actual entropy, not its range size.
Explicit corollaries cover real whole-record capacities and jointly revealed
raw coordinates, without independence assumptions. Time `n` means `T-1`;
inclusive column windows have disjoint elementary edge sets. Coincident
anchors are deduplicated, and singleton anchors and empty eroded arcs are
included. The proof uses standard axioms only, with no heartbeat override.

## Completed: complete covers with the full paid cost

[`PaidSourceCover`](lean/SourceCovers/PaidSourceCover.lean) verifies Theorem 3.5
from the actual computation, complete selected families, arbitrary cover
witnesses and the full paid cost. It averages each legal phase's entire signed
inequality, using the same bank, shift and whole-record transcript throughout
that phase. No final recovery or payment estimate is a theorem premise.

- [`PaidSourceGeometry`](lean/SourceCovers/PaidSourceGeometry.lean) identifies
  the full parent relation with the state predecessor and every actual long
  work hop. It explicitly includes all physical previous visits. Selected
  edges refer to the original families, before phase deletion. Actual source
  closure follows from paying deleted-family lowers and selected outer lowers;
  full-family coloring and outside hop sizes derive the residual live bound.
- [`IndexedSourceBank`](../lean-machine/LeanMachine/IndexedSourceBank.lean) and
  [`PaidSourceBank`](lean/SourceCovers/PaidSourceBank.lean) identify list slots
  with the finite-family recovery interface. Value sets deduplicate coincident
  slots, while variation retains their multiplicity.
- [`PaidBankRecovery`](lean/SourceCovers/PaidBankRecovery.lean) derives
  functional transpose recovery from local determinism and actual output
  correctness. The residual-payment theorem supplies one shift and its paid
  tuple for all outputs. [`PaidPhaseDeficit`](lean/SourceCovers/PaidPhaseDeficit.lean)
  derives the one-phase deficit, first retaining actual bank variation and then
  substituting the source-bank constant.
- [`SourceCoverCredit`](lean/SourceCovers/SourceCoverCredit.lean) allows an
  arbitrary set of genuine geometric witnesses, including empty sets and
  unattained suprema. Its score bound is derived, not a witness field.
  [`CircularRefinement`](../lean-machine/LeanMachine/CircularRefinement.lean)
  preserves the raw integer coordinates within an arbitrary real subdivision,
  proving equality with the existing point-gap area. The exact zero-arc
  witness is included.
- [`PaidAveraging`](../lean-machine/LeanMachine/PaidAveraging.lean) reuses
  Mathlib's finite expectation identities to average signed credit and cost.
  The final normalization gives precisely the manuscript's error, including
  the sharper stripe term `(W-b+1)/(2L)`.

The finite theorem does not need `T <= cL`. It permits upper budgets for
original variation and unprotected nonleaf hop mass; the paper's original
all-unprotected-family budget follows from `nonleaf_mass_le_total`. No
requirement that distinguished families be protected, nor disjointness of
the core and exception sets, is added. The actual phase count, deduplicated
outer payment and actual variation remain available before the uniform
relaxations. No hypothesis was strengthened or conclusion weakened.

## Completed: terminal core counts and reciprocal-cover credit

[`TerminalCoreCover`](lean/SourceCovers/TerminalCoreCover.lean) proves that
the exact bank is a union of complete core orbits rooted within the actual
computation: each covering root belongs to its own orbit, so completeness
and regression put it no later than the bank root. The shared
[`FractionalCoverBounds`](../lean-machine/LeanMachine/FractionalCoverBounds.lean)
then supplies unit weights, proving that the fractional minimum is bounded
by the actual finite cover cardinality and hence by `(2M+4)^|E|`.
Nonempty banks have cover weight at least one.

[`OrbitCountDeficit`](lean/SourceCovers/OrbitCountDeficit.lean) strengthens
Corollary 3.6 by retaining the mean reciprocal of the actual fractional
cover weights across phases and columns. That mean is between
`(2M+4)^(-|E|)` and one. The original corollary follows directly by relaxing
the actual exception count to its budget. A generic gap-credit theorem
extracted from Theorem 3.5 supplies both results with the same recovery,
transcript and payment calculation; its previous public statement is unchanged.

Actual output times satisfy `t < T`, as required by the original model;
no range premise on covering roots is added. The finite result still needs
no linear-runtime bound, permits arbitrary positive entry width, and retains
the nonleaf-only hop budget. No original hypothesis was strengthened or
conclusion weakened. The sharper mean can improve finite credit without
itself enlarging a uniform impossibility class.

## Completed: admissible geometries and joint profiles

[`AdmissibleGeometry`](lean/SourceCovers/AdmissibleGeometry.lean) packages the
actual walks, clamped raw path, output times, nonempty correctness set and
finite locally determined records. No source-cover, recovery or deficit
conclusion is a field. The finite orbit-count bound is derived from these
data for any selected subcore. This interface does not assert that every
such tuple is realizable by a native Turing machine.

[`CoreProfiles`](lean/SourceCovers/CoreProfiles.lean) sorts the complete core
by hop count, with arbitrary fixed ties. Hop and variation profiles use the
same list and are zero after its end. Exact prefix identities, a bound on
omitted families, and the Q2 mass bounds connect numerical coordinates to
actual finite selections. The variation uses all original edges in each
full family span.

[`JointProfiles`](lean/SourceCovers/JointProfiles.lean) formalizes Definition
4.1, proves a common subsequence exists, and preserves all three near-full
conditions under strictly increasing subsequences. Every joint profile is
nonnegative and summable, with hop mass at most `c` and variation mass at
most `2c`. Its hop profile remains nonincreasing and satisfies `h_i <= c/i`
in the paper's one-based indexing. Exact prefix-plus-tail identities and
finite-tail convergence identify the tails, which tend to zero.

The shared [`ProfileCompactness`](../lean-machine/LeanMachine/ProfileCompactness.lean)
module reuses Mathlib's compact products, subsequence theorem and bounded
partial sums. Its general form permits countably many coordinates with
separate bounds; finite-sum budgets pass to every coordinatewise limit
along a nontrivial filter. The paper needs only two profiles on the natural
numbers. No infinite sum is exchanged with a dimension limit, and no
convergence of finite geometries' tail masses or topology is assumed.
Positive entry width is arbitrary, so the original logarithmic case is
included. These are supporting compactness results, not a new impossibility
class or a novelty claim for compactness itself.

## Completed: necessary hop tails and critical-moment divergence

[`PrefixDeficit`](lean/SourceCovers/PrefixDeficit.lean) applies the finite
mean-reciprocal-cover bound to the first `J` actual complete core families. The first
`K` are distinguished and the first `R` protected, with no comparison between
`K` and `R`. Exact complement identities preserve full-span variation and
hop sums. The full unprotected hop sum bounds the rebuilt forest's nonleaf
payment; convergence of nonleaf membership is never assumed. The original
outside-family budget and the sorted omitted-family bound account for every
remaining family.

[`PrefixLimit`](lean/SourceCovers/PrefixLimit.lean) uses actual rounded widths
`ceil(lambda L)` and outside sizes `max(a0, ceil(c L/(J+1)))`. The shared
[`PrefixError`](../lean-machine/LeanMachine/PrefixError.lean) module normalizes
the complete error and reuses Mathlib's ceiling limits. With the cutoffs and
positive `lambda` fixed, a residual-bill upper bound tends to
`beta N C_q c²/(lambda (J+1))`. Runtime only needs its original bound, not
convergence. Capacity nonnegativity reuses the existing record-capacity
lemma, deleting a duplicated proof and a redundant analytic premise.

[`NecessaryCover`](lean/SourceCovers/NecessaryCover.lean) now sends
`J` to infinity with actual mean reciprocal covers retained and removes
the width error last. [`NecessaryHopTails`](lean/SourceCovers/NecessaryHopTails.lean)
derives its original inequality directly from that stronger result and the
terminal-orbit bound; its former separate cutoff-limit proof is deleted.
This verifies all of Theorem 4.2: the necessary inequality,
the explicit tail floor, and divergence of the critical moment's partial
sums to positive infinity. The main inequality permits every natural `q`
and independent natural `K,R`, subject only to `2 <= M` and `R < M`.
For positive capacity and `q >= 1`, the floor holds at every natural `R`,
including zero, and keeps the positive part when the variation tail is
at least one. These weaken the original cutoff conditions without adding
any hypothesis. The manuscript uses its standing positive constants and
`q >= 1`.

The shared [`TailMoments`](../lean-machine/LeanMachine/TailMoments.lean)
module derives a scaled-tail limit from a summable majorant, then applies
it to any fixed nonnegative polynomial shift. A separate summability
premise on the underlying sequence is unnecessary. Mathlib supplies the
conversion from nonsummability to divergence of nonnegative partial sums.
No infinite sum is exchanged with a dimension limit; the order is finite
certificate, dimension limit, cutoff limit, then vanishing width error.

The stronger cutoff freedom gives additional necessary profile constraints,
not a new asymptotic impossibility class by itself. The finite-section
convention now explicitly permits independent distinguished and protected
cutoffs, matching the verified finite theorem and its limit application.

## Completed: uniform one-exception correctness deficit

[`UniformDeficit`](lean/SourceCovers/UniformDeficit.lean) verifies all of
Corollary 4.3, including both the positive deficit and exponential
correctness-set bound. With one exception, a hypothetical near-full sequence
has a summable hop profile, whereas the verified critical-moment theorem at
`q = 1` says that same sequence is not summable. For nonpositive capacity,
the necessary-tail inequality directly gives a contradiction. The Lean
theorem therefore needs no separate positivity assumptions on `c,beta,N`;
the manuscript retains its standing physical bounds.

The shared [`UniformGap`](../lean-machine/LeanMachine/UniformGap.lean)
module turns exclusion of sequences with increasing dimension and two
vanishing nonnegative costs into a uniform gap. It chooses counterexamples
at thresholds `1/(n+1)` and reuses Mathlib's reciprocal limit and squeeze
theorem. It needs neither a topology nor nonemptiness on the instance type.
The geometry adapter applies it to `a0/L` and `Delta/L`, preserving any
additional class predicate on every selected geometry. This avoids repeating
the compactness-to-uniformity step for later envelope criteria.

Counting all input bitstrings gives `Delta >= 0`; the correctness set is
nonempty when taking logarithms. Mathlib's base-two logarithm equivalence
proves `epsilon L <= Delta` if and only if
`|C| <= 2^((1-epsilon)L)` for every real `epsilon`. The same uniform
constants work for all positive entry widths, alphabets and admissible
geometries at fixed `c,beta,N`. No core-size envelope is added, and no
numerical values of the constants are claimed.

## Completed: common envelopes and finite-prefix robustness

[`CommonEnvelopes`](lean/SourceCovers/CommonEnvelopes.lean) verifies the
general criterion and real power-law specialization of Corollary 4.4.
It strengthens the criterion: a fixed finite prefix, with a fixed positive
slack, suffices. The same `epsilon` controls outside size, normalized
envelope slack and the resulting relative deficit. One natural `m` serves
as both the required dimension threshold and the number of ranks checked.
Later ranks require no additional envelope bound. Constants are uniform
over all positive entry widths.

The proof applies `UniformGap.exists_gap` to approximations consisting of
an actual geometry, a cutoff `J`, nonnegative slack and a supplied sorted
order. Effective dimension is `min(d,J)` and the first cost is
`max(a0/L,slack)`. Thus a forbidden sequence has dimension and cutoff tending
to infinity, while both outside size and slack vanish. Retaining the
supplied orders directly gives a near-full sequence whose joint profile
obeys `h_i <= g_i` at every fixed rank. This eliminated separate proofs
of tie independence. The small [`HopEnvelope`](lean/SourceCovers/HopEnvelope.lean)
adapter relates the normalized, zero-padded envelope to exactly the original
finite family-size inequalities; for nonnegative envelopes padding adds
no premise. Only one sorted order is supplied per geometry.

`NecessaryHopTails.exists_scaled_tail_floor` now factors out the positive
floor already used by the critical-moment proof; that original proof is
derived directly from the helper. Both hop and envelope tails are summable
before comparison. The shared [`TailLiminf`](../lean-machine/LeanMachine/TailLiminf.lean)
module proves that a zero lower limit in the extended nonnegative reals
means arbitrarily late values below every positive threshold. This avoids
the default values of conditional real extrema; no boundedness of the
scaled tails is silently assumed.

The shared [`PowerEnvelope`](../lean-machine/LeanMachine/PowerEnvelope.lean)
module proves finite weighted moments using Mathlib's shifted `p`-series
test and real-power laws. The existing moment-to-tail theorem then gives
the envelope test. No integral estimate is needed. Real exponents `p > q`
and nonnegative amplitudes, including zero, are covered; the shared
summability lemmas even allow signed amplitudes. The generic formal
envelope theorem does not need a separate nonnegativity hypothesis on `g`,
although the manuscript retains it for its intended size envelopes.

## Completed: finite skeleton and necessary large-family count

[`FiniteSkeleton`](lean/SourceCovers/FiniteSkeleton.lean) verifies all of
Corollary 4.5, strengthens `q >= 1` to every natural `q`, and permits any
proposed skeleton independently of the previous core and exception labels.
For fixed ambient bounds and skeleton budget `q`, the constants precede
the original exception budget, geometry, chosen skeleton and outside
threshold. They cover every positive entry width.

`withSkeleton` keeps the complete computation, raw path, output times,
records, parent relation, correctness set and full-system span partition
definitionally unchanged. Only the classification changes: the selected
core is empty, the exceptions are the supplied skeleton, and its supplied
size bound replaces the old outside bound. Families and hops are not
removed. Restriction of the existing coloring certifies the empty core.

The empty-core exclusion supplies the zero joint profile with the identity
subsequence. The existing padding lemmas prove coordinate convergence.
The verified necessary-tail inequality at `K = R = 0, M = 2` then gives
the contradiction `1/(2*8^q) <= 0`. This includes `q = 0` and needs no
capacity-positivity premise. The uniform-gap adapter gives both the deficit
and exponential cardinality bounds; reclassification gives the original
corollary. No new compactness or envelope argument is introduced.

The construction-facing form is also verified: at sufficiently large
dimension, `Delta < epsilon L` forces more than `q` actual complete families
with hop count greater than `epsilon L`. Choose these families as the
proposed skeleton and use the threshold `floor(epsilon L)`; Mathlib's floor
inequalities handle the strict boundary exactly. This is a consequence of
the same exclusion, not a separate obstruction without the full-span
hypothesis. The constants may depend on `q` and are not given numerically.

## Completed: necessary reciprocal-cover complexity and small-cover probabilities

[`NecessaryCover`](lean/SourceCovers/NecessaryCover.lean) verifies all of
Theorem 4.6. The finite prefixes use actual complete banks, legal phases
and column output times along the supplied joint-profile subsequence.
The dimension upper limit is taken before the prefix upper limit, holding
both cutoffs and the modulus fixed. Every average and inner upper limit
has explicit bounds before a further real upper limit is taken.

The stronger weighted inequality retains `max(1-V_K,0)^2` and needs no
`V_K < 1` assumption. Only the divided version needs that assumption.
Both forms permit independent natural `K,R`, including `R = 0`, and any
fixed `M >= 2` with `R < M`. The original `M = 2R+2` bound follows directly.
The original cutoff requirement `R >= max(K,1)` is removed without adding
a hypothesis. All previous prefix and hop-tail theorem statements are
preserved as direct relaxations of the stronger proofs.

The probability bound allows any fixed real `s >= 0` and needs only the
limiting envelope `h_i <= H/i²`, for `H >= 0` and `R > 0`.
[`CoverDistribution`](lean/SourceCovers/CoverDistribution.lean) defines the
finite indicator average from the same actual covers and proves it is at
most `s` times their mean reciprocal. Empty averages are harmless, while
legal phases in the main application are proved nonempty. A common finite
envelope in the supplied original order passes to the limiting profile;
no tail convergence or alternative tie ordering is assumed.

Shared [`BoundedLimsup`](../lean-machine/LeanMachine/BoundedLimsup.lean)
reuses Mathlib's subsequence approaching the upper limit and its comparison
lemmas. Converging coefficients may vanish; positivity is needed only for
the final division. Shared
[`InverseSquareTail`](../lean-machine/LeanMachine/InverseSquareTail.lean)
reuses Mathlib's finite inverse-square sum bound and summability to obtain
`tau_R <= H/R`. No separate integral estimate is developed. The earlier
finite-error and rounding calculation is reused unchanged, and its former
standalone cutoff proof is removed.

The theorem constrains actual cover distributions in the same admissible
class. It does not assert economical covers for arbitrary tape geometries.

## Completed: uniform mean-cover criteria and a general envelope test

[`UniformCover`](lean/SourceCovers/UniformCover.lean) verifies all of
Corollary 4.7. Both original criteria retain their full geometry and class
quantifiers. Constants are common to every positive entry width and every
supplied sorted order witnessing the assumptions. Every natural exception
budget `q`, including zero, is covered.

[`CoverMeans`](lean/SourceCovers/CoverMeans.lean) defines the arithmetic mean
of the same actual cover weights used by the mean reciprocal. Mathlib's
`Finset.sq_sum_div_le_sum_sq_div` supplies finite Cauchy directly; no new
convexity or probability development is needed. The prefix adapter proves
`1/f(R) <= meanReciprocal` from the mean-cover bound and infers positivity
from the actual covers being at least one. It works for arbitrary legal
moduli and even `R > J`; the uniform criteria use `J >= R >= 1`.

The existing bounded-upper-limit lemmas pass this credit first through the
dimension limit, then the prefix limit. The weighted necessary-cover theorem
then yields `A_K <= beta * tau_R * f(R)/(R+2)`, with `A_K > 0` after choosing
`V_K < 1`. For a linear budget `B(R+2)`, summability makes the right side
vanish without any envelope assumption.

The stronger general criterion allows any summable envelope `g` for which
`liminf ofReal(tail(g,R) * f(R)/(R+2)) = 0`. The lower limit is in the
extended nonnegative reals, so unbounded or irregular weighted tails do not
exploit a default real extremum. Arbitrarily late small values suffice;
ordinary convergence to zero is unnecessary. The finite geometry must
satisfy both the size and cover bounds in the same supplied original order.
The formal statement needs no separate sign assumptions on `g,f`: the
existence of an admitted geometry forces `g >= 0` and `f(R) >= 1` for
positive cutoffs. The paper states the nonnegative specialization.

Shared [`PowerTail`](../lean-machine/LeanMachine/PowerTail.lean) reuses
Mathlib's monotone sum/integral comparison and improper power integral to
prove `tail(H/i^p,R) <= H R^(1-p)/(p-1)` for every real `p > 1` and `R > 0`.
It proves summability before comparing totalized infinite sums. A sub-power
factor `f(R)/R^p -> 0` then makes the weighted tail vanish, also with any
fixed nonnegative denominator shift. The original power criterion is a
direct specialization. Zero amplitude and nonnegative rather than positive
budgets are allowed; a zero budget at a positive cutoff admits no geometry.

The new ordered uniform-gap adapter reuses
`uniform_deficit_of_no_nearFull`. It chooses the order witnessing each
class predicate and retains that order in the extracted sequence. No
compactness, geometry, deficit/cardinality or uniform-gap proof is copied.
No earlier mathematical source is changed for this item.

The **next target is Proposition 3.7, complete continuation suppliers**:
verify the exact two-exception/older-closure decomposition, maximal-seed
reductions and the cluster movement bound. These are prerequisites for
Corollary 4.8 and the later global-sharing criteria. Reuse the exact source
bank, finite reachability and strengthened anchored-erosion results; retain
all older continuations rather than only immediate input coordinates.
The general transposition question remains open.

## Dependency order and proof obligations

| Stage | Targets | Obligations to preserve |
|---|---|---|
| 1. Full geometry | `def:complete-families`, `def:admissible-geometry`, `lem:family-accounting` | Actual previous visits; complete families before cuts; fixed full-span partition; all physical and state parents; whole-step capacity; nonempty correctness set on one geometry. |
| 2. Exact bank | `def:clipped-shadow`, `lem:shadow-variation`, `lem:protected-phase`, `thm:exact-source-bank` | Strict clipping; arbitrary-argument-path variation; original ranks and protected residues; complete ordered exceptional closure; packed maps with constants independent of the selected core-family count at fixed M and q. |
| 3. Paid recovery | `lem:residual-source-recovery`, `thm:cyclic-freezing` | Raw-block shift paid for the same bank; revealed-root parents retained; cyclic ordering shared by every output; actual column stripes; arbitrary deterministic entropy-bounded helper. |
| 4. Fractional certificate | `def:fractional-core-cover`, `lem:interval-rounding`, `lem:fractional-gap`, `lem:anchored-erosion`, `thm:paid-source-cover`, `cor:orbit-count-deficit` | Witnesses may use any computation time; complete raw source inclusion; shared time components charge each original edge once; approximation intervals anchored in the witness set; same-phase signed deficit and payment. |
| 5. Uniform tails | `def:joint-profile`, `thm:necessary-hop-tail`, `cor:one-exception`, `cor:common-envelope`, `cor:finite-skeleton` | Both profiles use the original hop order; absent entries zero; finite certificates before dimension limits; no convergence of tail mass or geometry assumed; uniform constants obtained by contradiction. |
| 6. Cover refinements | `prop:continuation-covers`, `thm:necessary-cover`, `cor:uniform-cover`, `cor:necessary-exposure` | Complete older reachability; absent exceptions padded by identity; older bank fixed before widths and shifts; precisely ordered limsup/liminf; common bounds for first-J selections. |
| 7. Global sharing | `prop:finite-sharing`, `thm:uniform-sharing`, `cor:sharing-density`, `prop:metric-sharing`, `cor:covering-exponents` | All actual output roots; maximal seeds in complete older reachability; raw union paid once; cost valid for every grid shift; residual bill retained; density limits along the same joint-profile subsequence. |
| 8. Native limitation | `prop:serial-quadratic-cover` | Eight legal work-head walks; exhaustive family enumeration; actual payments; physical paths distinguished from ordinary clipped sources; fractional lower bound against arbitrary-time witnesses; one root and phase only. |
| 9. Query movement | `thm:movement`, `cor:movement-interval`, `prop:subset-calibration`, `cor:subset-movement` | Arbitrary query order and coherent matching; within-column movement charged; the exact specified helper and raw-query interface; dimension limit before radius limit; credit the existing coded-caching construction. |
| 10. Causal groups | `def:causal-group-typing`, `thm:causal-group-routing`, `lem:attached-short-count`, `cor:causal-group-obstruction` | Fibrewise functional autonomy, not output purity; joint conditional support; paid collector capacity; partial bit flows; actual native attachment/volume assumptions; correlated helper fibres allowed. |

Stages 8–10 are companion branches, not premises of the uniform exclusion
theorems. Stage 7 depends on stages 1–6. The roadmap in the paper identifies
the additional native-geometry and computation questions that remain open.

## Reuse before new proofs

Inspect the exact types in the first, fourth, fifth and eighth papers, and in
`../lean-machine/`, before choosing imports. The native metric section names
the first paper's existing declarations. The earlier owner-order,
dependency and entropy libraries are candidates for reuse; this is not a
claim that they already prove the new statements.

Keep the repository's existing Lean/Mathlib pins. Require sibling packages
through relative paths rather than copying source. Preserve the first
paper's frozen statements. General reusable lemmas belong in the shared
library. No future declaration name is reserved by this document.

## Acceptance criteria for the later Lean pass

1. Match each full Lean type against the paper, including inherited premises,
   endpoint conventions, quantifier order and the intended conclusion.
2. Explain any strengthening, weakening or change of scope before updating
   the manuscript. In particular, a conditional geometric criterion must not
   become a claimed property of every linear-time machine.
3. Follow the repository's standard-axiom policy. Generate an axiom audit and
   declaration index from the declarations actually cited in the paper.
4. Replace each unformalized marker only when its exact claim is covered.
   Written arguments remain complete for any part not yet formalized.

Regenerate the current structural index with `python3 tools/statement_index.py`
and check it with `python3 tools/statement_index.py --check`. Neither command
verifies a mathematical proof.
