# Formalization plan

This records completed formalization and the remaining specification.
**Six of the 32 numbered results are Lean-verified: Lemma 2.3, family
accounting; Lemma 2.5, shadow and successful-word variation; Lemma 2.6,
the Q2 overlap forest and protected phases; Theorem 2.7, the exact source
bank; Lemma 3.2,
fractional interval covers; and Lemma 8.3, the attached short-distance
count.** Definitions 2.1 and 2.4 are also formalized. The other 26 results
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
The full admissible-geometry definition remains unformalized. The exact
source bank is now verified below.

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
through residual dependencies remains the next formalization item.

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
rounding conclusion unchanged and remains unformalized.

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
vertices. These results verify the selected-family source engine; they do
not yet prove recovery through state and unselected work dependencies.
The **next target is Lemma 2.8, paid residual-source recovery**.

## Dependency order and proof obligations

| Stage | Targets | Obligations to preserve |
|---|---|---|
| 1. Full geometry | `def:complete-families`, `def:admissible-geometry`, `lem:family-accounting` | Actual previous visits; complete families before cuts; fixed full-span partition; all physical and state parents; whole-step capacity; nonempty correctness set on one geometry. |
| 2. Exact bank | `def:clipped-shadow`, `lem:shadow-variation`, `lem:protected-phase`, `thm:exact-source-bank` | Strict clipping; arbitrary-argument-path variation; original ranks and protected residues; complete ordered exceptional closure; packed maps with constants independent of the selected core-family count at fixed M and q. |
| 3. Paid recovery | `lem:residual-source-recovery`, `thm:cyclic-freezing` | Raw-block shift paid for the same bank; revealed-root parents retained; cyclic ordering shared by every output; actual column stripes; arbitrary deterministic entropy-bounded helper. |
| 4. Fractional certificate | `def:fractional-core-cover`, `lem:interval-rounding`, `lem:fractional-gap`, `lem:anchored-erosion`, `thm:paid-source-cover`, `cor:orbit-count-deficit` | Witnesses may use any computation time; complete raw source inclusion; overlapping time hulls merged before charging variation; approximation intervals anchored in the witness set; same-phase signed deficit and payment. |
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
