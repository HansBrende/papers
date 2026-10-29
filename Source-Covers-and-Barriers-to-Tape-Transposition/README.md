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

**Proposition 3.7, complete continuation suppliers, is Lean-verified.**
Both maximal-seed reductions retain complete continuations. Their sharper
fractional-cover bounds use the actual core-orbit sizes; the original
`(ell+1)|F|` and `ell+1+s` estimates follow directly. Zero and one exception
are included by identity padding, and all covering roots are valid
computation times.

The movement estimate works with any fixed exact older bank and any finite
interval cover of the nonroot suppliers. Intervals can overlap, and their
representatives need not be suppliers. The improved loss is
`eta - eta^2/2`, where `eta = min(E/L,1)` and `E` counts the movement of every
complete older-bank slot on those intervals. The original `E/L` loss is a
corollary. These are sufficient certificates for the existing paid-deficit
criterion, not automatic small-cover or small-movement bounds for arbitrary
geometries.

**Corollary 4.8, necessary complete-observable movement, is Lean-verified.**
The mean movement of every older-bank slot over the nonroot suppliers' time
hull is retained through the dimension lower limit, then the prefix lower
limit on the same joint-profile subsequence. The stronger theorem bounds
the mean clipped quadratic penalty, which is at most the mean movement.
It permits independent `K,R >= 0` and any `M >= 2` with `R < M`.
For `M = 2R+2`, it gives
`e_R >= (1-V_K)_+²/[16(2K+1)(R+2)] - beta*tau_R/(R+2)`.
The final scaled lower limit allows infinity and excludes `e_R = o(1/R)`
when `V_K < 1`. These are necessary conditions on complete older
observables, not on immediate raw reads alone.

The proof fixes the exact older bank from Theorem 2.7 before choosing roots
or residual widths. Empty and singleton nonroot sets have zero movement;
explicit bank-variation bounds justify the real inner limits. The
reciprocal-cover and movement proofs share one paid-error limit, avoiding
another rounding and convergence argument.

**Proposition 5.1, the full shared-support payment, is Lean-verified.**
One raw-block union covers the newer support shared by all actual output
roots. Its cardinality is bounded for every grid shift, so the original
full two-exception bank still chooses and pays the residual cut. The older
bank then supplies the one-exception gap credit on the same correctness set
with the same joint record/raw transcript.

The stronger finite bound keeps the actual mean raw-support size and uses
the smaller one-exception constant for movement; the residual bill retains
the two-exception constant. The intermediate recovery theorem retains the
actual block union and both actual variations. The displayed maximal-seed
bound follows directly. Any legal modulus and independent protection and
distinguished-family budgets are allowed; no linear-runtime premise is
needed. This verifies the finite sharing certificate, not a small-sharing
property of arbitrary tape computations.

**Theorem 5.2 (Theorem H), uniform exclusion by global sharing, is
Lean-verified.** A common omitted-family rate `eta_J -> 0` and sharing
budgets with `liminf_J eta_J*g_R(J) = 0` force a uniform positive
correctness deficit, for any unbounded set of protected scales `R`.
Only arbitrarily late good cutoffs are needed, and the formal theorem
also permits common restricted cutoff sets and zero rates. The budgets
and cutoff sets must be fixed independently of dimension.

The no-envelope criterion uses the automatic rate `c/(J+1)`. The
power-envelope criterion now allows every `p > 0` and `H >= 0`; for
`p <= 1`, the no-envelope criterion already implies this case.
The proof reuses the full finite payment, rounding limits, joint-profile
tails and uniform-gap adapter. A short shared quadratic-tradeoff lemma
handles zero cost coefficients without a square-root minimizer.
It gives no automatic sharing bound for arbitrary tape computations.

**Corollary 5.3, necessary global continuation density, is Lean-verified
and strengthened.** On any joint-profile subsequence, let `g_low(J,R)`
be the dimension lower limit of the actual mean maximal-seed count.
For positive credit `mu_R`, any positive rate tending to zero that
eventually bounds the limiting omitted-hop coordinate satisfies
`liminf_J eta_J*g_low(J,R) >= mu_R²/(4*A_R*B_R)`.
A finite-dimensional common envelope is sufficient but no longer necessary.
The lower limits take values in `[0,infinity]`, with dimension first.

Sorted summability gives `(J+1)*h_(J+1) -> 0`. Applying the density bound
with every positive multiple of `1/(J+1)` proves the stronger no-envelope
conclusion `g_low(J,R)/(J+1) -> infinity`, improving the former positive
linear floor. This excludes dimension-uniform linear seed budgets at
arbitrarily large protected scales along a near-full sequence. A power-rate
bound on the limiting profile gives an explicit corresponding growth floor.
If a fixed omitted coordinate is zero and its finite-prefix credit is
positive, the inner lower limit is infinite. The formal bounds also allow
any legal modulus, independent cutoffs and positive-part credit.

The proof reuses the finite payment, rounding limits and shared quadratic
tradeoff; taking a convergent lower bound directly avoids another
subsequence extraction. These are requirements on complete continuation
counts, not information-capacity bounds or a decision of transposition.

**Proposition 5.4, the metric shared-support criterion, is Lean-verified.**
The actual minimum number of closed real intervals covering the shared raw
support is averaged over the original legal phases. Every interval of length
at most `delta*L` costs at most `2*ceil(delta*L)` raw bits at every shift,
improving the written factor three to the sharp factor two. Empty supports,
real endpoints, overlapping intervals and clipping at the input boundary
are included; the total payment is also capped by `L`.

The existing raw-payment proof now accepts any bound valid at every shift.
The original per-coordinate and maximal-seed statements are direct
specializations; the full two-exception residual bill is unchanged.
The metric proof reuses this payment, the rounded-width limit and the same
vanishing-tail contradiction. The three joint limits use a single common
unbounded cutoff set, fixed independently of dimension. More generally,
simultaneous smallness at arbitrarily late allowed cutoffs suffices, and
no separate upper bound `delta < 1` is needed. This verifies a sufficient
cover criterion without supplying it for arbitrary native computations.

**Corollary 5.5, sublinear raw covering exponents, is Lean-verified and
strengthened.** A mean raw-cover bound
`H_R*(J+1)^u_R*delta^(-s_R)` with `0 <= s_R < 1` gives a uniform deficit
without a size envelope whenever `0 <= u_R < 1-s_R`. This includes
cutoff-independent covers and permits positive cutoff growth. Under a
power envelope with any `p > 0`, the corresponding condition is
`u_R < p*(1-s_R)`; the earlier restriction `p > 1` is unnecessary.

Both cases reuse the metric criterion and one shared power-balancing
lemma. All constants and common unbounded cutoff sets are fixed before
dimension. The original `J^u_R` budget implies the shifted budget by a
verified monotonicity comparison. These are sufficient conditions on
actual raw supports, not automatic consequences of low entropy or a
new exclusion of unrestricted transposers.

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

**Proposition 6.1, the native serial-exception example, is Lean-verified.**
For every `M ≥ 4` and `b ≥ 1`, eight legal work-head walks realize the
quadratic cover `Q = (M-1)^2` at an output root and the original paid
phase. The proof enumerates every actual family and verifies the full
ordinary orbit, both unrestricted and joint-orbit-restricted cover optima,
and the surviving physical grid. Its gap bound holds for every raw set
between that grid and the complete ordinary raw orbit. It also verifies
vanishing exceptional-only profiles on every nondistinguished core span.
This rules out the stated pointwise linear-cover claim; it does not
exclude general linear-time transposition or an averaged cover criterion.

**Theorem 7.1, movement to cover distinct query types, is Lean-verified.**
For any ordering and coherent source matching, the stronger bound is
`F <= (floor(4C/rho) + 1) B`, where `C` sums the largest slot movement at
each query step and `B` is the stated binomial capacity. The original
sum-of-all-slots bound and its lower bound follow directly, including
the line-distance version. The reusable counting argument permits any
positive partition width and any charge dominating each slot's movement;
the actual circle capacity is proved by lifting centres to an integer
lattice. This concerns the specified query interface, not every possible
decoder for the same code.

**Corollary 7.2, queries spread over intervals, is Lean-verified.**
It charges deleted types by their occurrence counts, then applies the
same clock argument to good interval starts. The stronger form uses
the maximum slot movement at each time step, retains the floor factor,
and only requires disjoint internal interval edges: endpoints may coincide
and the interval list need not be chronological. Empty families and no
surviving good intervals are included. The original bounds follow directly.

**Proposition 7.3, the exact helper and gap-area calibration, is Lean-verified.**
The explicit subset code recovers every column from the specified raw rows
and common helper, whose uniform law, entropy and every fibre are exact.
Unused entries are independent of the joint observation of the helper and
all other entries. The mean gap area is computed for the actual scaled
raw-circle points, including wraparound. The finite identities also hold
for `1 <= k <= N`; the limits allow arbitrary positive repetitions and
word widths. This is a formalization of the credited coded-caching example,
not a new code or an unrestricted tape construction.

**Corollary 7.4, the dimension-first movement obstruction, is Lean-verified.**
Both representative and interval queries now satisfy the sharper bound
`liminf(C_N/L) >= (lambda/4) [(5 m lambda/2)^(-k) - 1]`, for
`0 < lambda < 2/(5m)`. Here `C_N` sums the maximum slot movement at each
step, so the total-variation bound follows directly. An independent
internal-movement threshold tends to zero after the dimension limit;
this improves the interval constant from `3m` to `5m/2`. The more general
clock-width bound is retained. The proof counts the actual repeated columns,
allows arbitrary positive `h(N)` and `b(N)`, and verifies divergence as
radius tends to zero afterwards. It excludes uniformly bounded movement
for this specified interface at all sufficiently small fixed radii, without
assuming movement is bounded or claiming an unrestricted tape lower bound.

**Definition 8.1, causal group typing, is formalized.** The model retains
row attachments, the memory spine, ordered transpose outputs, nonempty
consecutive column groups, and separate real capacity allocations for
all group fields on every attained helper fibre. Local dependence is
expressed by Mathlib's function factorization, with verified actual local
functions on all tuples. No independence is assumed.

The supporting proofs verify autonomy of one group's fields, an evaluation
on its actual joint projected support, and the support-capacity bound for
cuts containing all its requested outputs. Every entering field is included,
even after a previous departure from the cut. The collector of Theorem 8.2
is also formalized on the actual memory interval. It carries only bits
already output, so its exact capacity is the prefix size and its total
cost is the sum of output-to-sink delays. Distinct groups have disjoint
collector edge intervals. The resulting cut bound requires only the last
output inside the cut and extends to every supersource/sink cut, paying
all row attachments explicitly. A shared real-capacity max-flow/min-cut
theorem and the exact augmentation now yield a flow of the projected-support
logarithm on each group fibre. Each row supplies at most `b g_a`, and
unattached rows supply zero. A finite weighted path family now carries that
exact value, with all traversal loads bounded by the flow and at most one
path per positive edge. The reusable extraction allows cycles and preserves
parallel-edge identities. The artificial source and attachment arcs are now
removed, retaining each path's actual row attachment. Uniform splitting among
that row's original group bits preserves every original and collector edge
load and gives each bit mass at most one. Actual backward memory walks now
complete those routes to each bit's own output. Collapsing collector copies
adds their loads to the original edges; both traversal directions are charged.
The verified extra cost is at most twice each prefix size, with volume at most
twice the sum of output delays. The group routings are now combined and
averaged over attained helper values, preserving the exact support-log mass,
unit bit caps and shared physical capacities. A support lemma verifies the
probabilistic interpretation when the declared domain is the law's exact
support. The conditional-entropy lower bound, nonnegative total correlation
and helper/deficit algebra are now verified using the existing entropy
library, even for unnormalized nonnegative weights. The metric consequence
remains unformalized, so the full theorem is still pending.

All cited declarations use only `propext`, `Classical.choice` and
`Quot.sound`. The other **2 numbered results remain unformalized**:
the causal-group routing theorem and its obstruction corollary. The paper's
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
