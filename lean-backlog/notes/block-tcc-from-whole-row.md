# A common whole-row deficit implies the block Tape Coding Conjecture

Hans Brende and GPT-6 Astra, 15 November 2026.
**Status: the robust implication and its adaptive-machine consumer are
Lean-verified.** The geometric refinement, finite counting and uniform
composition are checked in the modules mapped in Section 7. No capacity
deficit is proved here.

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
| Finite invoice | [BlockCodeInvoice](../BlockCodeInvoice.lean): `robust_invoice` | Arbitrary natural co-entropy bill h, not only C₀db: L≤h+(4k+1)rG\|Γ\|+db\|E\|+b·a under whole-row exponent a. |
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
is checked by `robust_invoice`.

Reproduce the full dependency and axiom check with:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py
```

The modules use the repository's existing Lean/Mathlib v4.34.1 pins and a
1,000,000-heartbeat budget for arithmetic proofs. No frozen file is changed.

[WholeRow]: ../StatementsRowSpread.lean
[BlockDefs]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/DefsCE.lean
[Blocks]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/Blocks.lean
[Count]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/CECount.lean
[Grain]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/MStarTM.lean
[Depth]: ../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/lean/BoundedStackDepth/Machines.lean
[DepStep]: ../../Merge-Depth-Input-Steering-and-the-Coding-Core-of-Matrix-Transposition-on-Tapes/lean/MergeDepth/ColdGenie.lean
[Hop]: ../../Bounded-Nesting-and-Depth-Reduction-for-Matrix-Transposition-on-Tapes/lean/BoundedNesting/OneWalk.lean
[Consumer]: ../../Matrix-Transposition-and-the-Tape-Coding-Conjecture/lean/Transpose/Tape/Statements/Coding.lean
[OldRemark]: ../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/decomposition.tex
