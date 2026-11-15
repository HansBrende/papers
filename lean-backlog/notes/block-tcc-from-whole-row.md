# A common whole-row deficit implies the block Tape Coding Conjecture

Hans Brende and GPT-6 Astra, 15 November 2026.
**Status: the robust implication and its adaptive-machine consumer are
Lean-verified.** The geometric refinement, finite counting and uniform
composition are checked in the modules mapped in Section 7. Section 8 gives
a less uniform, finite sufficient hypothesis for the adaptive exclusion,
also checked in Lean. Section 9 gives its sharper standalone target and
proves the implication from the original wall; strict non-equivalence for
actual capacities is not established. No capacity deficit is proved here.

The implication holds for the **robust** conjecture, not just its
all-input version:

> A common positive whole-row deficit along the canonical bit alphabets
> implies `RobustNoCode_TM`, hence `NoCode_TM` and, by the first paper's
> existing theorem, no adaptive linear-time transposer.

There is no converse in this argument. Static whole-row codes are not
compiled into causal block codes or machines. The bridge missing from the
step-level audit is a bounded-length refinement of the **block graph's
geometry**, followed by a capacity-priced cut. It does not refine its
arbitrary block gates into constant-width step gates.

## 1. Statement and sources

Put b=b(d)=entryBits(d), W=db and L=dW. The hypothesis is that there is
δ>0 such that, for each fixed window w and each ζ>0, every sufficiently
large d satisfies

    log₂ |C| ≤ (1−δ+ζ)L

for every whole-row code C on a d×d array of b-bit entries, with at most
w helper rows per column. This is
`UniformWholeRowRateCanonicalBits (1−δ)` in
[StatementsRowSpread.lean][WholeRow]. Bounds uniform over all finite
alphabets imply this hypothesis; separate bounds at each fixed alphabet
do not suffice.

Fix arbitrary natural-number constants k,G,c,C₀ with G≥1. The robust target forbids,
for all sufficiently large d, a causal code on the first paper's block
network of any valid k-tape diagram with T≤cL, correct on any set F with

    |F| ≥ 2^(L−C₀W),

at the profile capacities. The diagram, code and set F may vary with d.
These are exactly the quantifiers of `RobustNoCode_TM` in
[DefsCE.lean][BlockDefs]. The plain target takes F to be the full cube.

We use four previously proved facts, with their original scopes:

1. A slot's pair residency has at most three blocks; each tape has at
   most one chord entering and one leaving each slot. See
   `pairRes_subset`, `pairRes_admissible`,
   `pairRes_chord_source_unique` and `pairRes_chord_target_unique` in
   [Blocks.lean][Blocks].
2. For arbitrary k unit-speed walks, `genie_cost` supplies a set of at
   most θN vertices in a horizon of 12N whose removal leaves bounded
   path depth depending only on k,θ. Use β=1, source-length parameter N
   and time constant 12 in [Paper 14's Machines.lean][Depth].
3. A canonical block slot sees at most two whole input rows, and its
   outputs form an interval of at most r bits. See `card_rowsAt_le`,
   `out_add_le` and `outNode_spec` in [CECount.lean][Count], with
   `one_le_blockSize`, `blockSize_le` and `blockSize_mul_ge` in
   [MStarTM.lean][Grain].
4. `RobustNoCode_TM` implies `¬ LinearTimeTransposable`, including
   adaptive machines, by `not_linearTimeTransposable_of_robustNoCode`
   in [Statements/Coding.lean][Consumer]. This uses the first paper's
   trace-class extraction, not a converse from codes to machines.

## 2. Refining the block graph into walk dependencies

Set r=⌈W/G⌉ and N=⌈T/r⌉. For positive d, validity implies T≥L>0,
so r,N≥1. For one work tape write R_y for its pair residency in slot
y<N. Three elementary properties supplement fact 1:

- R_y is a nonempty integer interval of at most three points. Indeed it
  contains the current block at time yr and is contained in that block
  and its two neighbours by `pairRes_subset`.
- R₀ contains 0. The original walk starts at 0.
- Consecutive R_y and R_(y+1) intersect. The resident pair at time
  (y+1)r contains the current block at time (y+1)r−1: if the block
  changes it becomes the previous block, and otherwise it stays current.
  These two times belong to the respective nonempty slots. This is
  `residentPair_succ` in [Blocks.lean][Blocks].

Choose an anchor in each consecutive intersection. The initial anchor is
0; choose any final anchor in R_(N−1). Replace each slot by twelve time
vertices 12y,…,12y+11. On each tape construct a unit-speed walk inside R_y
from its entry anchor to its exit anchor as follows. Write l=min R_y and
u=max R_y, so u−l≤2.

- Travel entry→l→u→l, using at most six moves; pad at l until time
  12y+6. Every point of R_y has been visited by time 12y+4.
- From time 12y+6 travel l→u→exit, using at most four moves; pad at
  the exit through time 12y+11 and the next boundary.

Thus the walk visits exactly R_y in this slot, every point has a visit
before the **pivot** p_y=12y+6, and every point has a visit at or after
the pivot. The anchors make consecutive slots agree at their boundary.
Perform this construction on all k tapes with the same twelve-position
clock, allowing pauses, and extend the walks constantly after 12N.

Every memory edge y→y+1 lifts to the state-spine path p_y→p_(y+1).
Consider a chord x→z, on one tape and block β. By `IsChord`, x+1<z,
β∈R_x∩R_z, and β belongs to no intervening slot. Its last visit in
slot x is at or after p_x; its first visit in slot z is before p_z.
There is no visit between them. They are therefore a genuine consecutive-
visit hop of the refined walk, with a gap of at least two. The path

    p_x → last visit of β in x → first visit of β in z → p_z

uses state edges on its ends and that hop in the middle. All its vertices
belong to slots x or z. This is exactly the reverse of the dependency
orientation in `DepStep` in [ColdGenie.lean][DepStep]; the hop condition
is [OneWalk.IsHop][Hop]. Extra refined edges are harmless.

Consequently every directed block path lifts to a refined dependency path
in reverse order, visiting its distinct pivots and using only slots on
the original path. Apply `genie_cost` with horizon 12N. Discard cut
vertices outside that horizon and delete every macro slot containing a
remaining cut vertex. The resulting slot set Γ satisfies

    |Γ| ≤ θN.

Every path in the induced block graph outside Γ lifts to a path avoiding
the micro cut, so it has at most

    D = genieDepth(k,1,12,θ)

vertices. In particular its edge length is at most D. This bound is
independent of r,d,T and the diagram. The library's `GFree` permits a cut
root; here every vertex of the induced path is uncut, so no extra root
convention is needed. Outputs rooted at cut slots are recorded below.

This proves the required small-cut theorem on the **actual** block graph,
including all memory edges and all pair-residency chords. Merely sampling
the original walk at slot boundaries would not establish it.

## 3. Price the cut at block capacities

For every y∈Γ record all outgoing edge messages and all bits appended
in that slot. Messages need satisfy their capacity bounds only on F,
which is precisely the domain on which we count record values.

The outgoing memory edge costs at most 3krG bits. The sum of outgoing
chord capacities is at most krG: a tape contributes to at most one such
chord, even if several tapes share an edge. There are at most r appended
bits. Hence the tuple has at most 2^B values, where

    B ≤ (4k+1)rG|Γ|
      ≤ (4k+1)θG(T+r)
      ≤ (4k+1)θG(c+1/d)L.                         (1)

We used rN≤T+r, G≥1 and r≤W=L/d. Cut-slot output bits must be included:
outgoing messages alone need not determine those locally decoded bits.
The graph, cut and record positions are fixed independently of the input;
there is no input-dependent selector charge.

## 4. Reassemble whole output rows

Each uncut vertex has at most k+1 incoming neighbours. Its uncut ancestor
cone therefore contains at most

    K_D = Σ_(j=0)^D (k+1)^j

vertices. Inducting in causal order, its outgoing messages and outputs
are determined by the cut record and the whole input rows attached to
these ancestors. Each ancestor has at most two attached rows, so at most
2K_D input rows suffice. Initial data and absent incoming messages are
fixed; no shared transition table or linearity is used.

This is not yet one whole-row relation: an output row may be written in
many slots. The output schedule is monotone, and a slot writes at most
r≤W consecutive bits, meeting at most two output rows. Thus the total
number of output-row/producing-slot incidences is at most 2N. Moreover

    N ≤ T/r+1 ≤ cGd+1 ≤ (cG+1)d.

Given η>0, put M=⌈2(cG+1)/η⌉. At most ηd output rows meet more than M
producing slots. Let E be those row indices. Every other output row is
determined by the cut record and at most

    w = 2M K_D                                               (2)

whole input rows. Bits written at cut slots already belong to the record.
All these helper sets are chosen from the diagram, not from the input.
Freeze the **input columns** indexed by E, because those are the exceptional
rows of the transposed output. Their cost is W|E|≤ηL. No fractional row
or new entry alphabet is required.

## 5. One fibre and the robust implication

Partition F by the joint cut record and the exceptional input columns.
One nonempty fibre C satisfies

    log₂ |C| ≥ L−C₀W−B−W|E|
             ≥ [1−C₀/d−(4k+1)θG(c+1/d)−η]L.                (3)

Every nonexceptional column of C is a function of the at-most-w rows
in (2). Exceptional columns are constant, so give them empty helper
sets. Grouping each b-bit entry gives a whole-row code on the full d×d
array over exactly the canonical alphabet. The fibre need not be linear,
contain a full independent cube, or have correctness outside F.

The assumed whole-row bound and (3) imply

    δ ≤ ζ + η + C₀/d + (4k+1)θG(c+1/d).                    (4)

Choose ζ=η=δ/4 and θ>0 so that
(4k+1)θG(c+1)≤δ/4. This fixes D, M and w before d grows.
Apply the whole-row threshold for this w,ζ, and then increase d until
C₀/d<δ/8. The right side of (4) is at most 7δ/8, a contradiction.
This proves `RobustNoCode_TM`. Its plain version follows by F equal to
the full cube, and the first paper's existing consumer excludes adaptive
linear-time transposition.

The finite extraction (3) also works with any input co-entropy h(d) in
place of C₀W: replace C₀/d by h(d)/L. In particular it excludes these
block codes on sets of co-entropy o(L), for each fixed k,G,c. Only the
O(W) instance is needed for the named robust conjecture.

## 6. What this answers, and what remains open

The three proposed checks have affirmative answers with the following
qualifications:

1. **Depth and capacities.** The block graph is not asserted to be the
   dependency graph of the sampled coarse head positions. The twelve-step
   interval traversal embeds all its paths in genuine walk dependencies.
   The cut then has the capacity bill (1). Total capacity O(L) alone
   would not have justified a cheap arbitrary vertex cut; the per-slot
   bound and the uniform slot count are used.
2. **Grain.** The grain is compatible because r≤db, giving two attached
   input rows per slot, and N=O(d), allowing the separate paid grouping
   of entire output rows. Treating each output bit's bounded cone as
   automatically giving a whole-row window would miss that payment.
3. **Correctness domain.** All-input correctness suffices, but is more
   than needed. The same fibre count handles the robust large-subset
   domain, with its co-entropy charged explicitly.

The earlier [Paper 4 remark][OldRemark] recorded no implication between
its *depth-TCP plus native crux* pair and the plain block conjecture.
This proof uses the later general walk theorem of Paper 14 and the
stronger **universal whole-row deficit**, together with the block
refinement above. It does not identify the native crux with that deficit
or prove the reverse implication. The previous step-code audit remains
correct as an audit of B1 alone; this additional bridge supplies the
block-conjecture implication that it did not supply.

The common deficit, robust TCC and (T) all remain unresolved. The result
orders the sufficient statements; it does not establish their hypotheses.
The refinement, cut pricing, row grouping and robust/adaptive implication
are checked in Lean. The original B1 wrappers retain their oblivious
statements; the stronger endpoint is in [WholeRowTCC.lean](../WholeRowTCC.lean).


## 7. Lean declaration map and quantitative conventions

All declarations below are in `LeanBacklog.BlockTCC` and use only
`propext`, `Classical.choice` and `Quot.sound`. The open bound is a theorem
hypothesis, never an axiom. The code can be nonlinear and nonuniform.

| Step | Checked declaration | Scope |
|---|---|---|
| Twelve-position traversal | [BlockIntervalWalk](../BlockIntervalWalk.lean): `residentData`, `residentData_mem_iff`, `IntervalData.chord_hop` | The actual `pairRes` intervals, including the partial final slot; exact last-visit hop on the constructed unit-speed walk. |
| Projected depth cut | [BlockCut](../BlockCut.lean): `exists_block_cut` | Actual `Dg.edges r`; cut size at most θN and a rank at most D strictly increasing along every surviving edge. No code or correctness assumption. |
| Local determination | [BlockCodeLocal](../BlockCodeLocal.lean): `code_local`, `card_nodeRows` | Equal outgoing cut messages and equal visible input rows determine uncut outputs. No linearity, shared table or independence. |
| Capacity bill | [BlockCutPrice](../BlockCutPrice.lean): `cut_edge_price`, `card_cut_outputs` | At most 4krG bits in outgoing edges and r bits in cut-slot outputs per cut slot; arbitrary capacity function below `CapProfile`. |
| Grouping | [BlockRowGrouping](../BlockRowGrouping.lean): `badOutputRows_bill`, `card_blockHelpers` | M\|E\|≤2N; a common helper set for every nonexceptional output row. |
| Robust fibre | [BlockCodeTransfer](../BlockCodeTransfer.lean): `fibre_wholeRow` | Correctness and capacity bounds only on F; finite observations use residues outside F. |
| Finite invoice | [BlockCodeInvoice](../BlockCodeInvoice.lean): `robust_invoice_sharp`, `robust_invoice` | Arbitrary natural co-entropy bill h: L≤h+(4kG+1)r\|Γ\|+db\|E\|+b·a under whole-row exponent a. The original, slightly coarser invoice remains available. |
| Uniform conclusion | [WholeRowTCC](../WholeRowTCC.lean): `robustNoCode_of_commonDeficit`, `noCode_of_commonDeficit`, `not_linearTimeTransposable_of_commonDeficit` | Exactly the existing robust/plain block predicates and the frozen adaptive-machine target. Only δ>0 and `UniformWholeRowRateCanonicalBits (1−δ)` are assumed. |
| Normalized input | [WholeRowTCC](../WholeRowTCC.lean): `robustNoCode_of_normalizedTwoSidedDeficit` | Symmetric, reflexive, two-sided common deficit suffices via the existing factor-two transfer. |

For reuse of the existing ball-count theorem, Lean uses the larger helper
window `M·2·(2k+3)^D`, rather than (2)'s directed-cone window. The exported
cut theorem supplies path **edge length** at most D through its increasing
rank; that is exactly what the ball argument needs. These choices leave
the final common-deficit statement unchanged. Its arithmetic chooses all
four payments at most ε=δ/8 (capacity slack, cut, exceptional columns and
input co-entropy), after fixing M and θ before d. The sharper finite
`c+1/d` display and the directed-cone count remain the written estimates;
the checked endpoint uses `c+1`. The general asymptotic o(L) co-entropy
extension stated above remains written, while its arbitrary finite bill
is checked by `robust_invoice`. Section 8 checks the sharper final-slot
payment for the adaptive-only route.

Reproduce the full dependency and axiom check with:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py
```

The modules use the repository's existing Lean/Mathlib v4.34.1 pins and a
1,000,000-heartbeat budget for arithmetic proofs. No frozen file is changed.

## 8. The weakened adaptive-only hypothesis

**Lean-verified:** [BlockEndRows](../BlockEndRows.lean) and
[WeakWholeRowTCC](../WeakWholeRowTCC.lean). This is a sufficient condition
extracted from the existing reductions, not a claim to be a logically
weakest possible hypothesis. It implies the adaptive exclusion directly;
unlike the common-deficit theorem, it does not assert `RobustNoCode_TM`.

### The smaller machine consumer

Paper 1's [`codes_coentLinear_at`][Coarse] supplies, from any adaptive
linear-time transposer, block codes at every sufficiently large dimension
with these additional properties:

- all L output bits are appended in the last L steps;
- the solving set has coentropy at most Kd bits, not Kdb;
- k≥5, G≥1 and c≥4, and one explicit allowance suffices:
  K=coarseConst(k−4,c,G)=c+4+5(k−3)(cG+2).

Indeed the buffered diagram has k=M.k+5 and c=2c_machine+4; the state
count affects only the size threshold, which cofinality absorbs. No
obliviousness of the original machine is assumed.

For final continuous output,
outNode(r,o)=⌊(T−L+o)/r⌋. An output row's db consecutive bits meet at most
G+1 slots because db≤rG. Thus the exceptional-column set is empty.
Set

    D(k,θ) = blockDepth k θ = genieDepth k 1 12 θ,
    W(k,G,θ) = 2(G+1)(2k+3)^D(k,θ),
    B(k,G) = 4kG+1.

These are the existing explicit depth function and `endWindow`. More
literally, D=parK(k,θ/48)^parP(k,θ/48)·⌈48/θ⌉, with the fixed
`parK`, `parP` of [Paper 14][Depth]. The cut costs at most
Bθ(cL+db), retaining the final-slot overhead db and charging cut outputs
one bit each. Hence a whole-row bound of deficit ε at this W gives

    d · b(d)[dε − Bθ(cd+1)] ≤ coentropy.

This is `end_invoice`, for every finite d≥1, θ>0 and arbitrary solving
set and profile-bounded nonlinear block code. There is no asymptotic
error term.

### Exact sufficient hypothesis, in the normalized class

Write q_d=2^b(d). For **every** integer triple k≥5, G≥1, c≥4 and every
lower dimension threshold d₀, suppose there exist

    d≥max(d₀,1),  θ>0,  R∈ℕ,  δ∈ℝ

such that, writing W=W(k,G,θ) and σ=2W/(R+1), both conditions hold:

1. Every code C on d×d entries from the alphabet `{0,1}^b(d)`, with a
   **symmetric, reflexive** helper relation of width at most W+R+1 and
   **two-sided** whole-row recovery, satisfies

       |C| ≤ q_d^((1−δ)d²).

   Two-sided means column j is determined by rows ρ(j), and row j by
   columns ρ(j), with the same ρ. The code and recovery functions can be
   arbitrary nonlinear functions; no invariance under transpose or any
   other symmetry is assumed.

2. The finite savings exceed the explicit allowance:

       b(d) [ d(δ−σ)/2 − (4kG+1)θ(cd+1) ]
         > c+4+5(k−3)(cG+2).                         (5)

**Conclusion:** no adaptive machine transposes every matrix in linear
time. The exact Lean statements are `AdaptiveNormalizedCriterion` and
`not_linearTimeTransposable_of_normalizedCriterion`.

All choices may depend on the resource triple and the lower threshold.
In particular θ, R, W and δ may change with d; δ need not have a common
positive lower bound, and the tested dimensions need only be arbitrarily
large. The cardinality bound is required for all indicated codes at the
chosen dimension, so the choices do not depend on a particular code or
diagram. No bounds at other alphabets are required.

For general one-sided codes at width W, omit R and σ and replace
(δ−σ)/2 by δ in (5). This is `AdaptiveWholeRowCriterion`. The
normalized-to-one-sided transfer is exactly the existing paid symmetry
normalization followed by translated intersection; its factor two and
payment have not been discarded.

### A simpler fixed-window sufficient form

`criterion_of_fixedWindow` proves the following convenient stronger
premise sufficient: for each k,G,c choose one θ>0 and ε>Bcθ such that,
at arbitrarily large d, **all** one-sided codes at W(k,G,θ) have rate at
most 1−ε. The finite overhead and Kd are then absorbed by increasing d.
There need be no common ε across resource triples. In the normalized
form the analogous margin is δ>2W/(R+1)+2Bcθ.

For comparison, a written asymptotic consequence is enough to permit a
deficit function tending to zero. Suppose normalized bounds of rate
1−f(w)+o_d(1) hold at each fixed window and along the canonical alphabets,
with the error uniform over all indicated relations and codes at that
window, and

    f(w)(log log w)^a → ∞  for every a>0.

Then the fixed-window margin above can be met. For fixed k,G, the literal
depth parameters give
log log W=O_{k,G}(θ^(−(4k²+1))log(1/θ)); choose R=⌈2W/θ⌉ so
the symmetry payment is at most θ. Thus f(W+R+1)/θ→∞. For example, eventual
f(w)=1/log log log w is sufficient. This growth estimate and asymptotic
corollary are **written, reviewed, not formalized**; the finite criterion
(5), with its exact quantifiers, is formalized. Merely f(w)>0 at every
fixed w is not enough for this argument: the deficit must beat its own
depth-cut cost.

## 9. Standalone target and the precise comparison

**Lean-verified:** [Wall.lean](../Wall.lean) is the entry point for agents
trying to prove or refute `LeanBacklog.Wall.Conjecture`. The file states the
quantifiers, alphabet, helper relation and both recovery conditions. The
target is a `Prop` definition, not an admitted theorem, so importing it
cannot assume the open problem. Its conditional adaptive exclusion and
the comparison arrows are fully proved.

### What “weaker” has been verified to mean

Let P be the original statement of `wall.md`:
there exists δ>0 with `UniformWholeRowRateCanonicalBits (1−δ)`.
Let Q be Section 8's `AdaptiveNormalizedCriterion`, and H the new
`Wall.Conjecture`. The checked implications are

    P → Q → H → ¬ LinearTimeTransposable.

`Wall.commonDeficit_implies_previous` proves the first arrow, not just
that P and Q have the same machine consumer. With common deficit δ₀,
choose θ=δ₀/[16(4kG+1)c], then a fixed R making the normalization payment
less than δ₀/4, and use the common bound with slack δ₀/2. The effective
deficit exceeds δ₀/8 while the asymptotic cut price is δ₀/16. A sufficiently
large dimension meets the finite allowance, for every requested threshold.
`Wall.of_previous` proves the second arrow using the smaller payments below.

**Strict non-equivalence for actual code capacities remains open.**
P→H does not establish that H→P is false. In classical logic a proof of
¬(H→P) for these fixed propositions would prove both H and ¬P: it would
exclude adaptive machines and refute the original common-deficit
conjecture. An abstract numerical rate profile with a slowly vanishing
deficit illustrates the relaxation of the numerical requirements, but is
not a family of whole-row codes realizing such a separation. No assertion
of strict separation, or of the converse, is made here.

### Further finite weakening

Keep k,G,c,d,θ,R,δ and W as in Section 8. Put

    L=d²b(d),       r=⌈db(d)/G⌉,
    Nmax=⌈cL/r⌉,    K=c+4+5(k−3)(cG+2),
    M=(4kG+1)r⌊θNmax⌋,
    h=0 if R≥d, otherwise min(d,⌊Wd/(R+1)⌋),
    X=2dh−h².

The standalone target uses the same normalized code bound
`|C|≤2^((1−δ)L)` at width W+R+1, but only requires

    δL > 2(Kd+M) + b(d)X.                           (6)

The improvement retains three facts lost in Section 8's envelopes:
the number of grain slots is an integer ceiling; the cut cardinality is
an integer floor; and the h×h overlap of the fixed rows and columns is
paid once. If R≥d there are no heavy rows at all. These are finite
quantitative improvements, not a new asymptotic mechanism or a proof of
strict separation between the open propositions.

[FiniteWholeRowPayments.lean](../FiniteWholeRowPayments.lean) proves
M≤(4kG+1)θ(cL+db) and X≤[2W/(R+1)]d², so every witness to (5) is a
witness to (6). It also proves the smaller payments directly on the
actual diagram and normalization. A normalized bound of exponent a
gives one-sided exponent (d²+a+X)/2; the record invoice then yields
L≤Kd+M+b(d)(d²+(1−δ)d²+X)/2, contrary to (6).

No resource quantifier, capacity hypothesis or machine premise has been
hidden in the standalone file. In particular the choices precede the
tested code and relation, the alphabet remains dimension-dependent, and
the conclusion concerns adaptive machines. No full robust TCC follows
from this weaker target in the present proof.

## 10. What a cut fibre retains: the row-factor proposal

**Written audit; not Lean.** The source check below uses
`BlockCodeLocal.code_local`, `BlockCodeTransfer.observe` and
`fibre_wholeRow`, and `BlockCodeInvoice.robust_invoice_sharp`. It supplies
no new capacity bound and does not weaken `Wall.Conjecture` further.

### Literal locality versus a fixed transcript

An outgoing cut message is generally a function of earlier cut messages
and local raw rows, not just of boundedly many raw rows. A running parity
already distinguishes these statements. Fixing a proposed transcript z
repairs locality: replace every outgoing cut edge by its prescribed value,
then evaluate the surviving acyclic graph. For each cut vertex v the
computed outgoing values must equal z. Their raw inputs lie in the
backward cone from v stopped at earlier cut vertices. The bounded depth
places that cone in a radius D+1 ball, so the existing degree/row counts
give the safe arity bound 2(2k+3)^(D+1), rather than asserting the output
window W is automatically the same arity bound.

Let G_z be the set of **all** inputs satisfying these exact consistency
equations and the prescribed source bits for cut-root outputs. Induction
in time proves that their actual outgoing cut values equal z, and the
converse follows by evaluating the same gates. Thus G_z is the intersection
of one bounded-row constraint per cut slot, plus unary-row pin constraints.
The functions in its factors depend on z. The uniform law on a nonempty
G_z has the global Markov property for the resulting row hypergraph:
conditioning on a separating set of rows factors the remaining finite
counting measure into a product. Zeros of the factors cause no difficulty.
This is a finite combinatorial argument, not an assertion about positivity
of a Gibbs density.

Two distinctions matter for the actual bridge. First, its solving set F
is arbitrary apart from correctness, capacities and coentropy; the fibre
used in the proof is C_z = F ∩ G_z. The current adaptive extraction gives
coentropy at most Kd, but no row-factor description of F. Intersecting
with F need not preserve the Markov property. Second, `observe` uses
residues outside F. Its unrestricted fibres can include out-of-capacity
messages with the same residues. G_z here fixes the actual messages,
whose bounded values on F are known; it is not the unrestricted residue
fibre. Exact-message fibres for admissible z are disjoint, but need not
cover the full cube. That suffices for the counting argument below.

Fixing extra raw coordinates preserves row factorization. The subsequent
intersection with a translated transposed code introduces column factors,
so it does not preserve this rows-only class. A structured consumer should
therefore be stated before that normalization.

### The common-function lemma and a failed crossing bill

If Y is determined both by U and by V, then, for any Z,

    H(Y | Z) ≤ I(U; V | Z).

Conditional data processing proves this directly. Hence on a genuine
G_z, a cell bundle recoverable on opposite sides of a row separator is
a function of that separator. This proves the proposed shell statement
for the unconditioned row-factor set when recovery holds there.

A selected fibre's mutual information need **not** be at most the number
of crossing-message bits. Even static local constraints give a control.
Take independent U,V uniform on eight values; let a(u)=0 on {0,1,2,3}
and give each remaining value its own label. Record a(U), a(V), and the
one crossing bit [U=V]. The fibre (0,0,1) has four equiprobable pairs and
I(U;V)=2 bits. There are 26 attained records, so it is larger than the
average fibre 64/26; only one crossing bit was recorded. Adding unused
independent coordinates makes its rate arbitrarily close to one. This
control refutes the asserted fibre inequality, not a whole-row capacity
bound.

With transcript-dependent local factors even choosing a largest fibre
is insufficient. First record [U=V] for independent n-bit U,V. On the
equality branch record zeros; otherwise record U and V in separate local
slots. For n≥2 the equality transcript is the unique largest fibre, has
I(U;V)=n, and still has only one crossing bit. The local slots depend on
the earlier crossing message; this is allowed by causal determination.

For static, non-adaptive local constraint maps on independent rows, the
**averaged** inequality does hold:
I(R_B;R_Bc | all records) ≤ H(crossing records | noncrossing records)
≤ crossing capacity. After fixing the noncrossing records the two sides
are independent; conditioning on the crossing records increases their
mutual information by at most their entropy. This does not establish the
pointwise claim or its use on an arbitrary solving set F.

### A paid Markov repair that does follow from coentropy

Here is an elementary replacement that retains the adaptive extraction's
small coentropy. Write L for the number of source bits, Q=2^M for the
number of admissible transcripts, and assume |F|≥2^(L-a). Among the
nonempty C_z=F∩G_z there is a z such that simultaneously

    |C_z| ≥ |F|/(4Q),       |C_z|/|G_z| ≥ 2^(-a)/4.       (7)

Indeed, transcripts failing the first inequality contain fewer than
|F|/4 inputs of F. Those failing the second contain fewer than
2^(-a)·Σ_z |G_z|/4 ≤ |F|/4. The exact-message sets are disjoint and their
total size is at most 2^L. Some input of F avoids both classes.
Consequently this same fibre has

    log₂|C_z| ≥ L-M-a-2,
    D_KL(Unif(C_z) || Unif(G_z)) ≤ a+2 bits.             (8)

For every row separator S between row bundles U,V in G_z, the latter
quantity bounds I_Cz(U;V | R_S). To check this, marginalize the relative
entropy to (U,V,R_S) and use the conditional product factorization of the
G_z law; its chain-rule expansion contains that conditional mutual
information plus nonnegative relative entropies. Thus any common
function Y of U and V on C_z satisfies

    H_Cz(Y | R_S) ≤ a+2.                               (9)

These statements hold simultaneously for every separator on the selected
fibre. In the adaptive application a=Kd. They are approximate Markov
bounds, not exact conditional independence, and the same a+2 may be
charged repeatedly: no summable or window-independent charge follows.

### Where the proposed pair count stops

For the symmetric-array code, every pair of distinct rows must share a
factor: after fixing all other rows their two cross entries retain a
common free symbol. A missing factor edge would make those rows
conditionally independent. Thus factors on at most W rows require at
least binom(d,2)/binom(W,2) factors in that particular presentation.

For a general code the same conclusion has not been proved. A missing
edge from row i to its helper bundle gives determination by the large
complement bundle (or (9) after payment), not a contradiction by itself.
For example, over a field of size at least d, d independent length-d
Reed–Solomon columns of dimension d-w-1 are determined by any d-w-1 rows
and have rate 1-(w+1)/d. They illustrate why determination by such large
complements alone allows rate approaching one; they are **not** codes
with recovery from w helper rows. An argument must use both requirements
and control repeated charges. No such inequality is supplied by this
audit. The proposed pure-Gibbs target therefore has no established
adaptive consumer; (7)–(9) state a repaired class that does have one,
conditional on a new capacity bound for that class.

[WholeRow]: ../StatementsRowSpread.lean
[BlockDefs]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/DefsCE.lean
[Blocks]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/Blocks.lean
[Count]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/CECount.lean
[Grain]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/MStarTM.lean
[Depth]: ../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/lean/BoundedStackDepth/Machines.lean
[DepStep]: ../../Merge-Depth-Input-Steering-and-the-Coding-Core-of-Matrix-Transposition-on-Tapes/lean/MergeDepth/ColdGenie.lean
[Hop]: ../../Bounded-Nesting-and-Depth-Reduction-for-Matrix-Transposition-on-Tapes/lean/BoundedNesting/OneWalk.lean
[Consumer]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/Statements/Coding.lean
[Coarse]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/CoarseTrace.lean
[OldRemark]: ../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/decomposition.tex
