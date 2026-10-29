# Source Covers and Barriers to Tape Transposition

**Hans Brende and GPT-6 Astra (OpenAI)** — October 2026

**Draft with partial Lean formalization and complete written proofs for the remaining results.**

- [PDF](paper/main.pdf) and [LaTeX sources](paper/), licensed under [CC BY 4.0](paper/LICENSE).
- [Lean library](lean/), licensed under [Apache 2.0](lean/LICENSE).
- [Formalization plan](FORMALIZATION.md) and [generated statement index](FORMALIZATION-INDEX.md).

## The question

Does one deterministic multitape Turing machine transpose every square
matrix with dimension `d` and entry width `b(d) = max(1, ceil(log₂ d))` in
time `O(L)`, where `L = d² b(d)`? This is question (T) in the series.

## What is proved

Every numbered result has a precise statement and an explicit proof status.
**Lemma 2.3, family accounting, is Lean-verified**, using Paper 8's actual
hops, first-maximum owners and complete families. The hop count satisfies
`h_G <= min(o_G - p_G, U_G - o_G)`. Exact overlap counts control total hop
mass and variation. At a time boundary, the lower-endpoint bill is at most
one plus the actual crossing-hop counts of the active families; `1 + N a`
follows from uniform overlap and size bounds. The original Q2 conclusions
are direct specializations. The formalization also covers Definition 2.1
and its finite-time indexing conventions.

**Lemma 2.5, shadow and successful-word variation, is Lean-verified**, along
with the clipped shadows and finite-word orbits in Definition 2.4. The same
factor-three bound applies to every metric-valued path, independently of
the successful word's length or the number of disjointly packed families.
A stronger estimate keeps each threshold's actual crossing count. Success
means every concrete action is nonidentity; its domain is an interval.
Every actual hop with an unpaid lower endpoint is represented exactly.
The shared library proves the crossing argument once for arbitrary monotone
interval patches. A verified finite example attains three in that general
class. These results supply the variation component of the exact source bank.

**Lemma 2.6, the Q2 overlap forest and protected phases, is Lean-verified.**
Only original nonleaves need to be deleted. Leaves and components of one
or two vertices can survive without increasing the `M+1` bound on simple
paths or the `2M+3` bound on complete shadow orbits. Protected leaves
forbid no residues; the exact denominator is `M-F`, where `F` counts the
distinct residues used by protected nonleaves. Actual lower supports bound
the total payment before relaxing to unprotected-nonleaf hop mass.
The full orbit is identified with a finite set, including inactive actions
and intermediate stopping points. This supplies the core-orbit component
of the exact source bank with a potentially smaller bill. Its three shared
modules separate interval geometry, phase counting and finite action orbits.

**Theorem 2.7 (Theorem S), the exact source bank, is Lean-verified.**
One geometry-fixed list represents the complete retained-core and exceptional
orbit at every time, with the original slot, variation and core-orbit-cover
bounds. The variation estimate holds for every pseudometric-valued path and
every finite horizon. Disjoint component packing reuses the factor-three
patch bound; a four-map leaf sandwich and an ordered-exception recurrence
assemble the bank. Across every originally selected unpaid actual edge,
the lower endpoint's value set is contained in the upper endpoint's set;
every lower of a deleted core family is paid.
The root read and the `C_q (T-1)` raw variation bound are included.
Paid residual recovery now completes this dependency argument.

**Lemma 2.8, paid residual-source recovery, is Lean-verified.**
One payment per grid shift supports every output root in the complete
causal dependency graph. Selected edges preserve bank value sets; every
other dependency is treated as residual. The proof retains a paid root's
direct read and unpaid parents and recovers the whole step record on an
arbitrary correctness set, without linearity or independence assumptions.
Each actual unpaid residual lower is charged once. The mean bill retains
oscillations capped at the block width and the exact live-boundary overlap
profile before yielding the original `H V / w` bound. These are finite
refinements of the same certificate, not a new uniform impossibility result.

**Theorem 2.9 (Theorem F), cyclic freezing, is Lean-verified.**
The actual frozen anchors, transpose demand stripes, and one common circular
ordering give a correctness-deficit bound for arbitrary nonlinear recovery
on a correlated correctness set. The same helper is charged by its entropy.
The additive error improves from `(W+1)/2` to `(W-b+1)/2`; a sharper version
replaces total bank variation by the sum of maximum slot oscillations in
the actual column windows. Whole-step genies and jointly revealed raw bits
are explicit corollaries. This completes the link from the paid source
bank to a finite deficit; it does not establish the later source-cover
hypotheses for arbitrary machines.

**Lemma 3.2, fractional interval covers, is Lean-verified:** a finite target
in any linear order covered by order-convex sets has a subcover and an
equally large set of witness points, with at most one witness in each
original set. Thus a fractional cover rounds to a subcover of cardinality
at most its total weight. The target may be empty, and the intervals need
not be closed or bounded. This is the rounding step used by the later
raw-source gap bound. The shared library proves the result once; this
paper re-exports it without copying proofs.

**Lemma 3.3, the fractional raw-source gap bound, is Lean-verified**, along
with the minimum-cover definition. The bound is
`gapArea(S) >= max(1-alpha,0)^2 / (2(2K+1) kappa(S))`, improving the former
denominator `4(K+1) kappa(S)` by counting the common orbit root once.
Canonical time components charge each original nondistinguished edge once;
sharper versions retain union variation and actual weighted component counts.
The estimate applies to any retained subset of a Q2 core. Cover roots range
over exactly the computation times, and a minimum is attained whenever the
target consists of visited coordinates. This completes the geometric credit
from fractional covers. The later written bounds use the improved
constant, with no change to their asymptotic classes.

**Lemma 3.4, anchored erosion, is Lean-verified and strengthened:** if the
covering arcs have union length at most `E`, put `e = min(E/L, 1)`. Then
`gapArea(S) >= gapArea(S₀) - (e - e²/2)`, which directly implies the original
loss bound `E/L`. Overlaps are charged once; old anchors need not remain in
the target. Singleton and full-circle arcs are included. The formal model is
a common finite circular subdivision with arbitrary real elementary lengths,
with verified adapters to real endpoint displacements and the earlier integer
gap-area definition. It uses finite sums rather than an intrinsic
`AddCircle`/Haar-measure development. The cover credit now retains the
quadratic saving.

**Theorem 3.5 (Theorem C), complete covers with the full paid cost, is
Lean-verified.** It combines the actual parent relation, exact bank, residual
payment, common whole-record transcript, fractional-cover credit and cyclic
freezing into `Δ/L >= mean(H) - E_q`. Credit and payment are averaged over
the same legal phases. Arbitrary witness families, including empty families
and unattained suprema, are allowed; fractional arc endpoints preserve the
actual raw gap area through a verified subdivision adapter.

The finite statement needs no linear-runtime premise. Its phase-deletion
budget can count only unprotected original nonleaves, strengthening the
original all-unprotected-family budget. Intermediate bounds retain actual
bank variation, distinct paid times and the exact legal-phase count before
using the displayed constants. Recovery and the full payment bound are
derived from local computation; neither is an assumed certificate. This
verifies the finite criterion but does not prove economical covers for
arbitrary tape geometries.

**Corollary 3.6, counting terminal core orbits, is Lean-verified.**
Its stronger form retains the mean reciprocal of the actual fractional
cover weights across legal phases and columns. Replacing this mean by
`(2M+4)^(-q)` recovers the original bound directly. The terminal cover is
exactly the complete raw bank; all its roots lie inside the computation.
The proof reuses the full paid theorem's averaging and recovery, with no
additional economical-cover premise. This completes the finite input to
the necessary hop-tail theorem, now also formalized below.

**Definitions 2.2 and 4.1, admissible geometries and joint profiles, are
Lean-verified.** The model supplies actual locally determined records;
its finite deficit is derived, not assumed. The core's hop and variation
profiles use the same sorted complete families. One common subsequence
converges in every coordinate. Every joint profile is nonnegative and
summable, with masses at most `c` and `2c`; its hop coordinates remain
nonincreasing and satisfy `h_i <= c/i`. Exact prefix-plus-tail identities
and finite-tail convergence give vanishing tails. Mathlib supplies the
compactness and summability machinery. These proofs allow arbitrary
positive entry widths and do not assume convergence of finite geometries'
tail masses.

**Theorem 4.2 (Theorem U), necessary hop tails, is Lean-verified.**
Actual finite prefixes, rounded widths and omitted-family budgets give the
finite-prefix limit. The proof then takes the numerical cutoff limit and
removes the width error, in that order. It proves the necessary inequality,
its explicit tail floor and divergence of the critical moment's partial
sums. The cutoff restriction `R >= K` is removed: the distinguished and protected
cutoffs may be chosen independently, and the floor also holds at `R = 0` with a positive
part in its numerator. Mathlib supplies the ceiling, series and limit tools;
the existing record-capacity lemma eliminates a duplicated proof. This
strengthens profile constraints but does not itself enlarge the uniform
impossibility classes or settle the general transposition question.

**Corollary 4.3, the uniform one-exception correctness deficit, is
Lean-verified.** For fixed runtime, capacity and full-span class bounds,
there are a common `epsilon > 0` and dimension threshold `d0` such that every
admissible geometry with `d >= d0`, a Q2 core, at most one exceptional
family and outside size `a0 <= epsilon L` has
`Delta >= epsilon L` and `|C| <= 2^((1-epsilon)L)`.
The same constants cover every positive entry width, record alphabet and
geometry satisfying the stated bounds; no core-size envelope is needed.
The proof reuses the verified `q = 1` moment contradiction. A short shared
lemma turns the exclusion of near-full sequences into uniform constants;
its geometry adapter preserves any additional class predicate for later
applications. The cardinality bound is exactly equivalent to the deficit
bound. This verifies the restricted exclusion, without providing those
geometry hypotheses for arbitrary transposers or numerical values for the
uniform constants.

**Corollary 4.4, common size envelopes, is Lean-verified and strengthened.**
For any fixed summable nonnegative envelope whose scaled tails have lower
limit zero, there are common `epsilon > 0` and a finite cutoff `m` such
that `d >= m`, `a0 <= epsilon L` and the first `m` normalized hop sizes
bounded by `g_i + epsilon` force the same uniform correctness deficit.
No envelope bound is required at later ranks. This includes the original
exact all-family bound and every real power envelope `H/i^p` with `p > q`,
including `H = 0`. The constants are uniform over positive entry widths.
The proof retains each supplied family order for the joint profiles and
reuses the shared uniform-gap lemma on dimension `min(d,J)` and cost
`max(a0/L,slack)`. The power case follows from Mathlib's `p`-series and the
existing moment-to-tail bound. Lower limits use the extended nonnegative
reals, so unbounded scaled tails are handled correctly. These are stronger
exclusions within the stated admissible class, with no numerical cutoff
or constants supplied.

**Corollary 4.5, the fixed finite skeleton, is Lean-verified, including
`q = 0`.** With the same fixed runtime, capacity and full-span class bounds,
at most `q` exceptional complete families and size at most `a <= epsilon L`
for every remaining family force the uniform correctness deficit at large
dimension. The proposed skeleton need not match an earlier core or exception
classification, and the constants cover all positive entry widths.
Equivalently, a geometry with `Delta < epsilon L` must have more than `q`
complete families with more than `epsilon L` hops. The constant may depend
on `q`; this is not a bound uniform in the skeleton size.
The proof explicitly supplies the zero joint profile for an empty core and
reuses the necessary-tail inequality and uniform-gap lemma. Reclassification
preserves the complete computation and correctness set, with the supplied
size bound replacing the old outside bound. No new compactness proof or
shared library is needed.

**Theorem 4.6, necessary reciprocal-cover complexity, is Lean-verified.**
The dimension upper limit of the actual mean reciprocal cover, followed
by the prefix upper limit, satisfies
`Q* <= 2 beta (2K+1) tau_R / ((1-V_K)^2 (M-R))` when `V_K < 1`.
The cutoffs are independent, including `R = 0`; any fixed `M >= 2` with
`R < M` is allowed. A stronger weighted form needs no positive-credit
assumption. Setting `M = 2R+2` gives the original bound, and substituting
the terminal-orbit lower bound on `Q*` recovers Theorem 4.2 directly.

For a limiting inverse-square profile `h_i <= H/i²`, `V_K <= 1/2` and
`R > 0`, the two successive upper limits of the fraction of phase-column
pairs with cover at most `s` are bounded by
`8 beta (2K+1) H s / (R(R+2))`, for every fixed real `s >= 0`.
A finite common envelope in the supplied hop order suffices. The proof
reuses the existing prefix-error calculation, Mathlib's bounded-limit
subsequences and finite inverse-square sum bound. All old public statements
remain unchanged; their separate cutoff-limit proof is removed.
This is a necessary cover-distribution constraint within the admissible
class, not a small-cover theorem for arbitrary tape geometries.

**Corollary 4.7, both uniform mean-cover criteria, is Lean-verified.**
A common mean-cover bound `B(R+2)` gives a uniform correctness deficit
without a size envelope. Under a common original-order envelope `H/i^p`,
every real `p > 1` and mean budget `f(R) = o(R^p)` give the same conclusion.
The constants are uniform over positive entry widths and supplied family
orders; both restrictions must hold in the same order.

A stronger criterion covers any summable envelope `g` with
`liminf [tail(g,R) f(R)/(R+2)] = 0`, using the extended nonnegative reals.
Only arbitrarily late small weighted tails are required, allowing irregular
and non-power-law envelopes. All natural exception budgets are covered.
The proof reuses finite Cauchy, the verified reciprocal-cover bound,
Mathlib's real-power integral comparison, and the existing uniform-gap
machinery. It does not prove economical covers for arbitrary computations
or supply numerical uniform constants.

**Lemma 8.3, the attached short-distance count, is Lean-verified:**
`S_ell <= min(d²b, (2 n - 1) b (2 k + 3)^(ell - 1))` for valid diagrams,
every block length `0 <= r <= d b`, and every natural radius parameter `ell` (both subtractions are
truncated at zero). Zero radius or block length gives an empty short-bit set.
The entry width remains arbitrary. A stronger geometry-dependent form
retains the actual attached-row and graph-ball counts. Its underlying local
counting inequality needs neither diagram validity nor a block-length bound.

The new occupancy argument replaces the first paper's `2b` bound per row
and output block by `b`, reusing its output-interval theorem. The remaining
proof imports its ball and row counts and applies Mathlib's finite-union
bound. The initial block touches at most one row, saving one attachment
over the two-per-block estimate.

All cited declarations use only `propext`, `Classical.choice` and
`Quot.sound`. The other **14 numbered results remain unformalized**,
including the continuation suppliers, complete-observable movement,
global-sharing criteria and causal-group results. The paper's
verified finite criterion and remaining written proofs give the main chain:

1. The exact selected-family bank combines with paid residual recovery to
   retain actual state and work-tape dependencies, with explicit costs.
2. A finite correctness-deficit theorem uses fractional source covers and
   anchored approximation while preserving that complete recovery bank.
3. Under the fixed runtime, capacity and full-span class bounds, uniform
   impossibility follows for a two-class return core plus one arbitrary
   exceptional family, with sufficiently small outside families.
   For any fixed number of exceptions, near-full correctness imposes a
   quantitative lower bound on the limiting sorted hop tails.
4. Additional uniform exclusions follow from economical mean covers or raw
   support shared across all outputs and paid for once. Necessary cover,
   complete-observable movement and global-density bounds record what a
   surviving sequence would have to satisfy.

Three companion branches test the limits of those certificates: a native
quadratic pointwise cover example with serial exceptional spans; an
ordering-independent movement bound for a specified recovery interface;
and an almost-complete-helper requirement for causally autonomous groups
of `o(log d)` adjacent columns. The coded-caching code used to calibrate
the movement bound is credited to its original authors.

The manuscript develops the model and finite theorem first, derives their
uniform consequences next, and then presents these construction restrictions
and a roadmap. The generated index lists every numbered result and definition
as a reference for the later Lean phase.

## What is open

These are restricted full-geometry theorems, not a decision of (T). The
full-span partition and return-core hypotheses are not supplied for every
machine. Nor are the economical-cover or sharing conditions proved for
every admissible two-exception geometry. Selecting a common geometry in an
adaptive computation may lose entropy, which must be paid for separately.

The native counterexample concerns one root and phase and is itself excluded
by the finite-skeleton corollary. The movement bound retains its specified
helper and raw queries. The causal-group theorem requires local functional
separation, not just separated final outputs. No native strict separation
from the union of all prior certificates is claimed.

## Building and checking

From this directory:

```sh
python3 tools/statement_index.py
python3 tools/statement_index.py --check
```

From `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

From `lean/` (the cache command is needed only for missing dependencies):

```sh
lake exe cache get
lake build
lake env lean PaperAxioms.lean
```

The index generator checks labels, proof-status markers and following proof
or outline environments, and generates the axiom commands from the formal
citations. It does not execute those commands or check the mathematics.
Inspect the rendered PDF
and resolve reference/citation warnings. Follow the repository's
[public-path checks](../CONTRIBUTING.md#portable-files) before publishing.

The Lean package uses the existing v4.34.1 pins and the second paper's build
adapter, which reads the first paper's canonical sources without copying
them, Paper 8's `boundedNesting` package for actual families, and the shared
`lean-machine` package for interval covers, incidence sums, monotone
patches, interval forests, protected phases, finite orbits, packed source
banks, shifted-grid payment and causal recovery. Building
requires the whole repository with sibling folders in place.
The remaining plan is recorded in [FORMALIZATION.md](FORMALIZATION.md).
