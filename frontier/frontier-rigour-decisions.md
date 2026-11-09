# How the frontier map is drawn

Companion to the [frontier map](index.html), 9 November 2026. It records, piece by piece, how each class
on the map is stated and why each overlap, separation and inclusion is drawn as it is. Paper numbers
follow the root README.

## Semantics

- The outer frame is every deterministic multitape Turing machine in the frozen model of paper 1: a
  read-only two-way input tape, k work tapes and a one-way write-only output tape.
- The inner rectangle is the transposers: machines that, for every d, transpose every d × d matrix of
  b(d) = max(1, ⌈log₂ d⌉)-bit entries, at any running time.
- Inside the rectangle a property stands for the transposers that have it. A piece is red when no
  transposer in it runs in time O(L), where L = d² b(d).
- A red strip outside the rectangle is a property that no transposer has, unless a dotted ? joins it to
  the rectangle.
- A shape drawn inside another is a proved inclusion.
- The seven dark-outlined pieces (one work tape, oblivious data movement, few macroscopic crossings, one
  long-range work head, regular head motion, few large families and half-bound ball relations) follow a stricter rule. Each overlaps exactly the pieces it is proved to
  share a transposer with and stays apart from the rest. A dotted ? joins it to a piece when this is not
  known. These claims are pairwise: where an outlined piece passes through several pieces at once, no
  combination of them is claimed. Other overlaps carry no claim: shapes drawn apart may share
  transposers, and a drawn overlap may contain none.

## Witness machines

These explicit machines are all slow; they show that the drawn overlaps of the dark-outlined pieces are
non-empty. Every witness is a full transposer: on every input of every size d ≥ 1 it halts with the
transpose on its output tape, at whatever running time. Being correct on most inputs, or on the inputs
of some sizes, is not enough. Each base machine below transposes by construction, and each variant
changes only the motion of the heads, never the output, as its row explains.

| Name | Construction | What it shows |
|---|---|---|
| Round trip | One work tape. Compute d and b from L, copy the input with marker tracks for entries and rows, and park the input head off the input. Then make d round trips, writing output row j on the j-th rightward pass. Time about 2dL. | Oblivious, one work tape, pure data movement. For every radius r, an output written after the first r + 1 round trips reaches no input read within r dependency steps, so its ball of radius r is empty. |
| Counter | One work tape holding O(log L)-bit counters, run by a head that sweeps the counter cells. For each output bit in column-major order, walk the input head to its source and append the bit as it is read. | Oblivious, one work tape, pure data movement. The work head stays within O(log L) cells, so no revisit has an excursion of a fixed fraction of L and no step starts a macroscopic crossing. Every return family has O(log L) hops, and the family spans form two classes of disjoint spans. Each output reads its own source, so its balls contain it. |
| Parked counter | The counter machine, except that after reading each source bit it keeps the bit in its finite control, walks the input head off the input, and lets its work head sweep the counter cells for L steps before appending the bit, then walks the input head back, finding the input's end as the first non-blank cell. The appended bit is the source bit carried unchanged, so the output is the counter machine's. | As the counter machine. In addition, every dependency edge near a wait spans o(L) steps, so a dependency path of at most r edges from an output stays inside its wait for large d, where no input is read; all balls of radius r are empty. |
| Fresh copy | Two work tapes. Each pass writes the matrix minus its current first column to fresh cells of the other tape, outputting the removed entries, then rewinds. Counters are kept by alternating fresh copies. | Oblivious, pure data movement, and every cell of every tape, the input tape included, is entered at most three times. Late outputs have empty dependency balls. |
| Cancelling copies | The counter machine with two extra work tapes. In a first pass the input head reads the input once while both extra heads copy it, one cell per bit; both extra heads then rewind. The counter machine then runs, and the extra heads advance one cell after each append, so at the append step of output bit i both are at cell i. The machine appends the source bit XORed with the two copied bits of cell i. | The copied bits are equal, so the XOR returns the source bit: the machine transposes every input at every size, and it is oblivious. It combines data, so it is not pure data movement, and it has three work tapes. Each extra head makes one large return family per turn, four in all, and every other family has O(log L) hops. Each output reads its own source at the append step. At each append step the extra heads wait at the cell they returned to by a revisit that starts in the rewind and crosses the write-to-rewind revisits of cells nearer the start, both of order L for most cells. |
| Pauses | Pause for one step after appending an output bit 1, under one of four rules: (a) only after output bit 0; (b) only within the first ⌈d/4⌉ output rows; (c) after every output bit; (d) after every output bit of rows 1 to d − 1, unless output row 0 is all zeros, in which case never. | A pause step moves no head, writes back the scanned symbols and appends nothing, so the tapes and the output are those of the base machine, which still transposes every input; each rule reads only output bits already appended. Pauses enter no cell, so entries, revisits and crossings are unchanged. (a) gives two traces of probability ½: low adaptivity, not oblivious. (b) gives entropy about L/4 with every trace of probability 2^(−Ω(L)): low adaptivity, no trace of probability 2^(−o(L)). (c) gives entropy L: high adaptivity, no such trace. (d) gives entropy L − o(L), high adaptivity, and keeps the base trace on the inputs whose output row 0 is all zeros, a set of probability 2^(−db) = 2^(−o(L)): the kind of trace the crossings, one-head and regular-motion classes ask about. |
| Deep-nesting tapes | Add two data-free work tapes whose heads run paper 8's deep-nesting pair U(s₀, m, 1), with m growing with d and stroke length Λ = 2^s₀ chosen with mΛ = o(L), steered by counters on a third data-free tape whose head sweeps its O(log L) cells. The parameters are computed from L at the start. | The extra tapes run alongside the base machine and never influence its transitions or its output, so the machine still transposes every input; their motion depends only on d, so obliviousness is kept. The two walking heads have unbounded owner load and are outside Theorems F, B and M, so an oblivious machine with these tapes lies in the deep piece. Their excursions are O(Λ) = o(L), the counter head's are O(log L), and all their dependency edges span o(L) steps, so they add no macroscopic revisit, no long-range head and no input read near an output. |

## Classes stated without a time bound

A class that is defined only for machines with a given time constant contains no slower transposer, so
every class on the map is stated without one. Where a theorem takes a threshold from the time constant,
the class asks for its condition at every fixed threshold.

- **Only o(log d) monotone passes; if oblivious, only O(1) coarse passes** (outside the rectangle). A pass
  is a stretch in which every head moves monotonically. Every halting transposer needs at least
  log_(k+1) d − O(1) passes, at any running time (passes memo, Lean; paper 1, Theorems P and P′).
  Kirchherr's conservative machines with o(log d) reversals are a special case. In a coarse pass the input
  head and a bank of work heads are monotone up to o(L) cells and every other head stays within o(L)
  cells; boundedly many coarse passes over the whole run cannot transpose at any running time if the
  machine is oblivious (paper 16, Corollary 10.5 of Theorem 10.3; Corollary 10.4 across scales). Adaptive machines with
  O(1) coarse passes are excluded only in polynomial time, so they are not in the strip.
- **Output phase** (outside, with a dotted ?). On every run, the output is produced in a final stretch in
  which the input head and a fixed set of bank heads make O(1) phases, monotone up to o(L) jitter. Every
  other head visits o(L) cells, and a fixed fraction of the input rows is unread when the stretch
  begins. Paper 16, Theorems B and J with their suffix forms, excludes linear time. With the whole run as
  the stretch, no oblivious transposer has the property at any running time, and no adaptive one in
  polynomial time (paper 16, Corollary 10.5 of Theorem 10.3). Whether a transposer with an unrestricted prefix, or an
  adaptive one of superpolynomial running time, can have the property is not known.
- **Exactly one work tape.** Superlinear time is necessary (Dietzfelbinger, Maass and Schnitger 1991;
  Dietzfelbinger and Maass 1993; in this model also paper 4, Corollary 3.18, and paper 16,
  Corollary 4.2).
- **Oblivious data movement.** Entries are moved as indivisible items along an input-independent
  pattern. Superlinear time is necessary (Stoß 1973). In the series' terms, a linear-time oblivious
  transposer beats every routing by a factor of order log d (paper 1, Theorem "The code gap"), and a pure
  data mover is a routing. Data movement that depends on the entries is not covered (paper 1, condition
  (N1)).
- **One long-range work head, or none.** On some trace followed by a 2^(−o(L)) fraction of the inputs
  (the only trace, if oblivious), all work heads but one make only excursions of o(L) cells. Paper 16,
  Theorem H, excludes linear time at the explicit thresholds ε* and ε_sm. The machines whose work heads
  never return from a macroscopic excursion form a subclass, which paper 1's Theorem M* already
  excludes.
- **Regular head motion.** On some trace followed by a 2^(−o(L)) fraction of the inputs (the only trace,
  if oblivious), for every fixed c, every limit of the work-head paths over the first cL steps (frozen
  after halting), with time and space rescaled by L, is locally affine on an open set of full measure.
  Paper 2, Theorem 6.3, excludes linear time: in every such limit over the whole run of a linear-time
  transposer the work heads spend at least 1/(2G) of physical time in total outside open sets on which
  they are locally affine, where G = max(1, ⌈log₂(g+1)⌉) is the number of bits per work cell. The theorem
  is assembled from Lean declarations; paper 2 states that it is not a single exported Lean statement. It
  reaches a heavy trace because the inputs that follow it, all transposed correctly, number at least
  2^(L−o(L)), which is all its entropy hypothesis asks, and the popular trace of that family is the trace
  itself. Oblivious all-regular contracting recursions, and machines that run one on a heavy trace, form
  a subclass (Theorem 7.5 and Lemma 7.3); the five cascades of paper 16 are such recursions (cascade memo,
  Theorem 1.1). Theorem 7.5 also excludes adaptive recursions with no heavy trace, which are not in the
  class. Theorem 7.1's bounded palette words compile to size-indexed executors, not fixed machines, so
  they are a ruled-out strategy rather than a subclass (listed below the frame). Paper 4's written results measure travel instead
  of time and are cited on the card, but the class uses the time form.
- **Few macroscopic crossings.** On such a trace, some fixed fraction of the outputs, the same for every
  θ, is cut off by o(L) steps from the starts of crossing revisits of excursion more than θL, for every
  fixed θ > 0. Paper 16, Theorem X and Corollary 5.6, together with Theorem E(a) for heavy traces,
  excludes linear time. The order of quantifiers matters: Theorem X's threshold shrinks with the output
  fraction, so the fraction must be fixed before θ is chosen.
- **Half-bound piece.** The machine is oblivious and, for every fixed radius r, its ball relations of
  radius r lie in a proved half-bound class, apart from o(L) outputs. A linear-time oblivious machine has
  genies of cost εL whose cones lie in balls of a fixed radius (paper 14, Corollary O(a)). The revealed
  word is then an index code whose largest fibre is a storage code of rate about 1 − ε on these relations
  (paper 4, Remark 4.9(b)), which the half bound forbids.
- **Few large families.** The machine is oblivious, its family spans split into N classes of disjoint
  spans, and for every ε > 0 all but q families have at most εL hops (or the variant with two span
  classes plus one family). For linear time this is paper 9's admissible geometry, which is excluded.

## Decisions for the dark-outlined pieces

**One work tape**

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Round trip |
| Oblivious, deep | apart: disjoint | An oblivious one-tape machine has one work head, the free head of paper 8's Theorem M with no other heads (Lemma W), so it lies in the shallow piece |
| Low adaptivity, not oblivious | overlap | Round trip with pause variant (a) |
| High adaptivity | overlap | Round trip with pause variant (c) |
| Each cell entered O(1) times | apart, dotted ? | Not known |
| Half-bound piece | overlap | Round trip |
| Few large families | overlap | Counter |
| Few macroscopic crossings | overlap | Counter |
| One long-range work head | overlap | Every oblivious one-tape machine lies in it (an inclusion, stated on the cards but not drawn) |
| Oblivious data movement | overlap | Round trip, Counter |
| Bounded merging, linear data path | overlap | Round trip |
| Regular head motion | overlap | Round trip, Counter |

**Oblivious data movement**

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious | inside | Definition |
| Low adaptivity not oblivious, high adaptivity | apart: disjoint | It lies inside the oblivious circle |
| Oblivious, shallow | overlap | Round trip |
| Oblivious, deep | overlap | Round trip with deep-nesting tapes |
| Each cell entered O(1) times | overlap | Fresh copy |
| Half-bound piece | overlap | Round trip |
| Few large families | overlap | Counter |
| Few macroscopic crossings | overlap | Counter |
| One long-range work head | overlap | Counter |
| One work tape | overlap | Round trip, Counter |
| Bounded merging | inside | Pure data movement has bounded merge depth (paper 11, Remark "Examples") |
| Linear data path | inside | Copying is linear over every field (paper 8, Definition "Linear data path") |
| Regular head motion | overlap | Round trip, Counter |

**Few macroscopic crossings**

Membership is checked against the class as stated above, with one output fraction for every θ. Every
witness below makes no revisit of excursion more than o(L) on its heavy trace, so no step starts a
macroscopic crossing, and every set of outputs is cut off by the empty set for every θ.

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Counter |
| Oblivious, deep | overlap | Counter with deep-nesting tapes |
| Low adaptivity, not oblivious | overlap | Counter with pause variant (a) |
| High adaptivity | overlap | Counter with pause variant (d) |
| Each cell entered O(1) times | apart, dotted ? | Not known |
| Half-bound piece | overlap | Parked counter |
| Few large families | overlap | Counter |
| Bounded merging, linear data path | overlap | Counter |
| One work tape | overlap | Counter |
| Oblivious data movement | overlap | Counter |
| One long-range work head | overlap | Counter |
| Regular head motion | overlap | Counter |

**One long-range work head**

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Round trip, Counter |
| Oblivious, deep | overlap | Round trip or Counter, with deep-nesting tapes |
| Low adaptivity, not oblivious | overlap | Counter with pause variant (a) |
| High adaptivity | overlap | Counter with pause variant (d) |
| Each cell entered O(1) times | apart, dotted ? | Not known |
| Half-bound piece | overlap | Round trip |
| Few large families | overlap | Counter |
| Bounded merging, linear data path | overlap | Round trip, Counter |
| One work tape | overlap | Round trip, Counter |
| Oblivious data movement | overlap | Round trip, Counter |
| Few macroscopic crossings | overlap | Counter |
| Regular head motion | overlap | Round trip, Counter |

**Regular head motion**

Membership is checked against the class as stated above. Every witness's rescaled work-head paths over
the first cL steps converge to paths of finitely many straight pieces, for every fixed c, so each limit is
affine outside a finite set. Their setup, which computes d and b and lays the marker tracks, keeps each
work head within O(log L) cells, or moves it monotonically, up to zigzags of O(log L) cells, at a rate
that is constant over the phase or tends to 0, so the limits are affine there as well. The round trip makes its copy pass and then round trips of about 2L steps each. The counter's
and the parked counter's work heads stay within O(log L) cells, so their rescaled paths tend to 0. The
fresh copy's passes are monotone sweeps at unit speed, each of length a fixed fraction of L for the
first passes, with monotone rewinds between them. The cancelling copies' extra heads make one copy pass
and one rewind, then advance one cell per append, o(L) cells in the first cL steps. Deep-nesting tapes keep
their heads within O(mΛ) = o(L) cells. A pause step moves no head, so pause variant (a) changes the base
motion by at most one step, and variant (d) keeps the base trace on a set of inputs of probability
2^(−o(L)).

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Round trip, Counter |
| Oblivious, deep | overlap | Round trip with deep-nesting tapes |
| Low adaptivity, not oblivious | overlap | Round trip with pause variant (a) |
| High adaptivity | overlap | Round trip with pause variant (d) |
| Each cell entered O(1) times | overlap | Fresh copy |
| Half-bound piece | overlap | Round trip |
| Few large families | overlap | Counter |
| Few macroscopic crossings | overlap | Counter |
| One long-range work head | overlap | Round trip, Counter |
| One work tape | overlap | Round trip, Counter |
| Oblivious data movement | overlap | Round trip, Counter |
| Bounded merging, linear data path | overlap | Round trip |

The cancelling-copies machine, whose cell is certified under "The goal" below, also lies in this piece.

**Few large families**

The class lies in the shallow piece (see Inclusions), so it is apart from the deep piece and from both
adaptive regions, and every other pair has a witness: no relation is open.

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Counter, Round trip, Parked counter, Fresh copy, Cancelling copies |
| Oblivious, deep | apart: disjoint | The class lies in the shallow piece |
| Low adaptivity not oblivious, high adaptivity | apart: disjoint | The class is defined for oblivious machines |
| Each cell entered O(1) times | overlap | Fresh copy |
| Half-bound piece | overlap | Round trip, Parked counter, Fresh copy |
| Bounded merging, linear data path | overlap | Counter, Round trip, Parked counter, Fresh copy, Cancelling copies |
| One work tape | overlap | Counter, Round trip, Parked counter |
| Oblivious data movement | overlap | Counter, Round trip, Parked counter, Fresh copy |
| Few macroscopic crossings | overlap | Counter, Parked counter |
| One long-range work head | overlap | Counter, Round trip, Parked counter |
| Regular head motion | overlap | Counter, Parked counter |

**Half-bound ball relations**

The class is defined for oblivious machines, so it is apart from both adaptive regions; every other pair
has a witness, and no relation is open.

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Round trip, Parked counter, Fresh copy |
| Oblivious, deep | overlap | Round trip, Parked counter or Fresh copy, each with deep-nesting tapes (see below) |
| Low adaptivity not oblivious, high adaptivity | apart: disjoint | The class is defined for oblivious machines |
| Each cell entered O(1) times | overlap | Fresh copy |
| Few large families | overlap | Round trip, Parked counter, Fresh copy |
| Bounded merging, linear data path | overlap | Round trip, Parked counter, Fresh copy |
| One work tape | overlap | Round trip, Parked counter |
| Oblivious data movement | overlap | Round trip, Parked counter, Fresh copy |
| Few macroscopic crossings | overlap | Parked counter |
| One long-range work head | overlap | Round trip, Parked counter |
| Regular head motion | overlap | Round trip, Parked counter |

The deep witnesses need one check, because the dependency DAG has a revisit edge for every work tape,
including the data-free deep-nesting tapes. Their walk U(s₀, m, 1) is periodic with period
P = 4(m+1)Λ = o(L), so every revisit edge on them spans at most P steps, and the steering counter sweeps
its cells, so its edges are short too. Without the extra tapes, every edge after the copy phase spans at
most one round trip, one pass or one wait. Two cases follow.

- Round trip and parked counter: a round trip and a wait each last at least L steps, so a path of r edges
  from an output stays within r round trips, or inside the wait, and never reaches an input read.
- Fresh copy: its passes shrink, but every pass except the last o(d) lasts longer than P, so an edge
  still crosses at most one of them, and the outputs of the last o(d) passes are o(L) in number.

So in all three the balls of every fixed radius stay empty apart from o(L) outputs, and the half-bound
membership survives.

## Inclusions

Drawn, each proved:

- oblivious inside low adaptivity, since an oblivious machine has a single trace;
- the shallow and deep pieces, the half-bound piece, oblivious data movement and both overlays inside
  the oblivious circle, by definition (paper 8 defines a linear data path only for oblivious machines);
- few large families inside the shallow piece. Both conditions of the class ask for a partition of the
  family spans into N classes of disjoint spans (paper 9, Definition "Admissible return geometry"). Every
  hop of a family lies inside its span (paper 8, Definition "Families"), so at most N owners are open at
  any step. That bounds the owner load by N (paper 8, Definition "Owner-load"): Theorem F's class of
  bounded nesting load;
- the oblivious part of the bounded-entry disc inside the shallow piece, since entering every cell at
  most V times bounds the owner load by 2V − 1 (paper 8);
- the oblivious part of one work tape inside the shallow piece (see the table above);
- oblivious data movement inside both overlays.

Proved but not drawn, to keep the centre readable: the oblivious part of one work tape lies inside the
one-head island.

## Changes from the previous drawing

- "Data movement only" claimed every data mover. Only input-independent movement is excluded (paper 1,
  (N1)), so the piece is now oblivious data movement.
- The bounded-merging overlay sat inside the deep piece only. Nothing proves that, and the round-trip
  machine is a shallow member, so the overlay now meets both oblivious pieces.
- The linear data path overlay reached the adaptive regions, where paper 8's definition does not apply.
- The bands were drawn across every circle by convention. They are now drawn by proof, as above.
- The sweeps band is split. Its passes half contains no transposer and sits outside the rectangle; its
  never-fold-back half lies in the one-head island.
- XOR-frame recursions (paper 1, §12) and local packet coding (paper 2) are no longer drawn as pieces; see
  the next section.
- The two paper 16 islands, few macroscopic crossings and one long-range work head, paper 9's few large
  families and the half-bound piece are dark-outlined pieces with pairwise claims, like the two former
  bands. The half-bound piece is drawn as an ellipse along data movement, so that it can meet the
  bounded-entry disc.
- 9 November 2026. The motion obstructions were missing: paper 1's Theorem M* appeared only inside the
  one-head card, and paper 2's Theorems 6.3, 7.1 and 7.5 only as a clause of the packet-coding card, which
  placed them in its information-access model. They concern machines' actual head paths, and are now the
  dark-outlined piece "Regular head motion", stated for heavy traces like the paper 16 islands. Slow
  transposers with piecewise-straight rescaled motion are found in every other piece inside the
  rectangle, so the band meets each of them. Paper 4's written motion results, with Theorem C's exclusion
  of machines whose work heads are all home-based with legs of boundedly many constant-rate runs, are
  cited on its card and on the card of the shallower cuts. A referee pass the same day restricted the
  Theorem 7.5 subclass to oblivious recursions and recursions run on a heavy trace, moved Theorem 7.1 from
  the subclasses to the ruled-out strategies, cited Theorem C rather than C′ for home-based heads, and
    labelled Theorem 6.3 as assembled from Lean declarations.
- 9 November 2026. Theorem 7.1's bounded palette words joined the ruled-out strategies below the frame.
  Paper 3's barriers to reversing its bit-to-word reduction were considered and left off: they limit
  compilers that build a bit transposer from word-transposer calls, not constructions of a word
  transposer.
- 9 November 2026. The cascade text said that Problem 11.4 was open and that the rows-to-columns condition
  was not measured. All five cascades are now excluded (cascade memo), and the third and fourth also fail
  rows to columns (paper 16, Theorem 10.8). Paper 16's Corollary 7.3, a time bound for traces that keep the
  row-index scales in disjoint sets of steps, is stated in the text; it is drawn as no piece.

## Construction strategies ruled out

Three results on the page rule out construction strategies rather than machine properties, and are
listed below the frame instead of being drawn as pieces.

- **XOR-frame recursions** (paper 1, §12). The model is a recursion that interchanges address chunks with
  XOR gadgets in sheared frames, where each frame change costs a recursive interchange of narrower chunks.
  Every gadget needs at least as many frame changes as it has wires, so the recursion cannot reach linear
  time within the template. Paper 1 calls the link between the template and the preprint's construction
  informal, and says the results rule out a class of constructions, not linear-time transposition.
- **Local packet coding with a small helper budget** (paper 2; its motion theorems are not part of this
  model, and are the piece "Regular head motion"). The model is an information-access model:
  receivers that each hold one original row read a broadcast of fixed two-coordinate Boolean packets and a
  helper. Such broadcasts cannot save a fixed fraction of the bits. No theorem turns a machine's run into
    such a broadcast.
- **Bounded palette words** (paper 2, Theorem 7.1, Lean). Paper 2 declares three palettes of public
  operations on the matrix: integer, ternary, and mixed binary with masked strides. No word of bounded
  length over a palette transposes, even on a 2^(−o(L)) fraction of the inputs, however its operations vary
  with the size: each word compiles to a native execution with two work tapes, o(L) state bits and time
  O(L) whose work heads follow boundedly many affine pieces, which Theorem 6.6 excludes.

For the first two, nothing decides, yes or no, whether a given machine follows the strategy, so there is no set
of machines to draw. They stay on the page because they close two routes to a construction: the recursion
behind the only claimed transposer faster than O(L log d), and a natural local coding scheme. A
machine-level version of either, turning the machines that follow it into runs of the model, would make it
a set of machines and an island of the diagram. The palette words are formal, but a word may change
arbitrarily with the size, so they are programs indexed by the size and not a set of machines either; a
fixed machine whose rescaled head motion is regular lies in the piece "Regular head motion".

## The goal: a certificate for every Venn cell

The pairwise rule is a first step. The aim is a certificate for every Venn cell inside an outlined piece,
that is, for every combination of presence and absence of the other pieces: a witness transposer if the
cell is non-empty, a proof if it is empty. Nothing more is drawn for this; the record is kept here.

A witness whose membership in every piece is determined certifies exactly one cell. The memberships of
the witnesses above are as follows (S, D: oblivious shallow and deep; LA: low adaptivity, not oblivious;
HA: high adaptivity; ✓ member, · not a member).

| Witness | Adaptivity | Entry O(1) | Half-bound | Few families | Merging | Linear | One tape | Data movement | Crossings | One head | Motion |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Round trip | S | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | · | ✓ | ✓ |
| Counter | S | · | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Parked counter | S | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Fresh copy | S | ✓ | ✓ | ✓ | ✓ | ✓ | · | ✓ | · | · | ✓ |
| Cancelling copies | S | · | · | ✓ | ✓ | ✓ | · | · | · | · | ✓ |
| Round trip + deep-nesting tapes | D | · | ✓ | · | ✓ | ✓ | · | ✓ | · | ✓ | ✓ |
| Counter + deep-nesting tapes | D | · | · | · | ✓ | ✓ | · | ✓ | ✓ | ✓ | ✓ |
| Parked counter + deep-nesting tapes | D | · | ✓ | · | ✓ | ✓ | · | ✓ | ✓ | ✓ | ✓ |
| Fresh copy + deep-nesting tapes | D | · | ✓ | · | ✓ | ✓ | · | ✓ | · | · | ✓ |
| Round trip, pauses (a) | LA | · | · | · | · | · | ✓ | · | · | ✓ | ✓ |
| Counter or parked counter, pauses (a) | LA | · | · | · | · | · | ✓ | · | ✓ | ✓ | ✓ |
| Round trip, counter or parked counter, pauses (b) | LA | · | · | · | · | · | ✓ | · | · | · | · |
| Fresh copy, pauses (a) | LA | ✓ | · | · | · | · | · | · | · | · | ✓ |
| Fresh copy, pauses (b) | LA | ✓ | · | · | · | · | · | · | · | · | · |
| Round trip, pauses (d) | HA | · | · | · | · | · | ✓ | · | · | ✓ | ✓ |
| Counter or parked counter, pauses (d) | HA | · | · | · | · | · | ✓ | · | ✓ | ✓ | ✓ |
| Round trip, counter or parked counter, pauses (c) | HA | · | · | · | · | · | ✓ | · | · | · | · |
| Fresh copy, pauses (c) | HA | ✓ | · | · | · | · | · | · | · | · | · |
| Fresh copy, pauses (d) | HA | ✓ | · | · | · | · | · | · | · | · | ✓ |

Reasons for the entries that are not immediate from the constructions:

- The half-bound piece, few large families and both overlays are defined for oblivious machines only,
  so the adaptive witnesses lie outside them, and oblivious data movement is oblivious by definition.
- The round trip is not in the crossings class. For θ small compared with the output fraction, most
  outputs are written at cells that the head revisits only after going more than θL to the right. That
  revisit crosses the one between the previous leftward and the current rightward pass, so the output step
  itself starts a macroscopic crossing, and every cut must contain it.
- The fresh copy is not in the crossings class either. Each output reads a cell whose previous visit, in
  the rewind, starts a revisit that crosses the earlier write-to-rewind revisit of a cell nearer the
  region's start. Both revisits travel a fixed fraction of L, so cutting k outputs off costs at least k
  steps. Both of its data heads make excursions of order L, so it is not in the one-head class.
- The round trip and the fresh copy are in few large families by the variant condition: their large
  families are the turn families, which alternate along a chain of overlapping spans and so split into
  two classes of disjoint spans.
- The counter machine is not in the half-bound piece: each output reads its own source at the append
  step, so its relations contain loops and admit storage codes of rate 1.
- The deep-nesting tapes put a machine outside the shallow piece and so outside few large families. They
  break bounded entry and change no other entry.
- The crossings, one-head and regular-motion classes ask for a trace of probability 2^(−o(L)). Pause
  variants (b) and (c) leave none, so those witnesses lie outside all three, even with one work tape.
- Every base machine and every deep-nesting variant is in regular head motion, for the reasons under its
  table, and so are pause variants (a) and (d), which keep a trace of probability 2^(−o(L)) with the base
  machine's motion.
- Cancelling copies is in few large families by the first condition. Its four large families are the
  write-to-rewind and rewind-to-read families of the two extra heads; at any step at most six families
  are open, so the spans split into six classes of disjoint spans.
- Cancelling copies has merge depth 0, since no data passes through a cell entered more than three times
  (paper 11, Definition "Lineages and merge depth"), and its data path is linear over F₂: the output is
  the input bit plus the two copied bits.
- Cancelling copies is not in the half-bound piece, for the counter machine's reason. It is not in the
  one-head class, since both extra heads return after excursions of order L.
- Cancelling copies is not in the crossings class either. At the append step of output bit i, each extra
  head is at cell i. It returned there one step after the previous append, by a revisit that starts in
  the rewind and has excursion i; that revisit crosses the write-to-rewind revisit of cell 0, of excursion
  about L. Waiting on a cell makes no revisit, so the dependency path from the append step runs along state
  edges through the waiting steps and then along that revisit edge to its start. For outputs with i above
  θL these paths end at crossing starts and are vertex-disjoint, so cutting k such outputs off costs at
  least k steps.

The rows certify 19 distinct cells as non-empty. One of them is the cell inside few large families,
regular head motion and both overlays, and outside every other red piece and the bounded-entry disc. Cancelling copies certifies
it, and the drawing shows it as the part of few large families that lies in the regular-motion band,
outside the other red pieces. No row is in the
half-bound piece and outside every other red piece: every half-bound row is in oblivious data movement, so
that cell is open. Proved inclusions and disjointness settle every cell that would put a transposer in two
places the map keeps apart:

- one work tape in the deep piece;
- an oblivious one-tape transposer outside the one-head class;
- oblivious data movement outside the oblivious circle or outside either overlay;
- the half-bound piece, few large families or an overlay outside the oblivious circle;
- few large families or bounded entry in the deep piece.

Those cells are empty. Every other cell inside an outlined piece is open: no witness for it is known, and
no published result rules it out.

## Open questions

- Can a transposer with bounded cell entry have one work tape, few macroscopic crossings, or only one
  long-range work head? No published result settles any of the three (the dotted ? links from the
  bounded-entry disc). For one work tape, a crossing-sequence argument is a likely route to a negative
  answer.
- Does any transposer, at any running time, have the output-phase property? With the whole run as the
  stretch, coarse pass counting (paper 16, Corollary 10.5 of Theorem 10.3) rules out oblivious transposers at any running
  time and adaptive ones in polynomial time; with an unrestricted prefix, the pass bounds say nothing.

## How the geometry is checked

[`check_layout.py`](check_layout.py) reads the shapes back out of the SVG in `index.html` and checks them with
exact polygon operations. Run it from the repository root with

```sh
uv run --no-project --with shapely python frontier/check_layout.py
```

It checks that

- every required overlap of each dark-outlined piece contains a disc of diameter at least 12, and the
  piece misses every other piece;
- every certified cell that the drawing shows (here, the one certified by cancelling copies) contains such
  a disc;
- every required separation has a gap;
- every required inclusion holds;
- no shape lies inside another unless the inclusion is listed above;
- every dotted ? link joins the outlines of the two shapes whose relation is open, and crosses no other
  piece;
- the green question marks sit in the pieces their cards describe, and outside regular head motion,
  which no linear-time machine has.

It exits with status 1 if any check fails. Its lists of overlaps, separations and inclusions mirror the
tables above; change both together.
