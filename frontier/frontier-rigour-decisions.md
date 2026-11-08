# How the frontier map is drawn

Companion to the [frontier map](index.html), 8 November 2026. It records, piece by piece, how each class
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
- The four dark-outlined pieces (one work tape, oblivious data movement, few macroscopic crossings and
  one long-range work head) follow a stricter rule. Each overlaps exactly the pieces it is proved to
  share a transposer with and stays apart from the rest. A dotted ? joins it to a piece when this is not
  known. These claims are pairwise: where an outlined piece passes through several pieces at once, no
  combination of them is claimed. Other overlaps carry no claim: shapes drawn apart may share
  transposers, and a drawn overlap may contain none.

## Witness machines

These explicit machines are all slow; they show that the drawn overlaps of the dark-outlined pieces are
non-empty.

| Name | Construction | What it shows |
|---|---|---|
| Round trip | One work tape. Compute d and b from L, copy the input with marker tracks for entries and rows, and park the input head off the input. Then make d round trips, writing output row j on the j-th rightward pass. Time about 2dL. | Oblivious, one work tape, pure data movement. For every radius r, an output written after the first r + 1 round trips reaches no input read within r dependency steps, so its ball of radius r is empty. |
| Counter | One work tape holding O(log L)-bit counters, run by a head that sweeps the counter cells. For each output bit in column-major order, walk the input head to its source and append the bit as it is read. | Oblivious, one work tape, pure data movement. The work head stays within O(log L) cells, so no revisit has an excursion of a fixed fraction of L and no step starts a macroscopic crossing. Every return family has O(log L) hops, and the family spans form two classes of disjoint spans. Each output reads its own source, so its balls contain it. |
| Parked counter | The counter machine, except that after reading each source bit it keeps the bit in its finite control, walks the input head off the input, and lets its work head sweep the counter cells for L steps before appending the bit. | As the counter machine. In addition, every dependency edge near a wait spans o(L) steps, so a dependency path of at most r edges from an output stays inside its wait for large d, where no input is read; all balls of radius r are empty. |
| Fresh copy | Two work tapes. Each pass writes the matrix minus its current first column to fresh cells of the other tape, outputting the removed entries, then rewinds. Counters are kept by alternating fresh copies. | Oblivious, pure data movement, and every cell of every tape, the input tape included, is entered at most three times. Late outputs have empty dependency balls. |
| Pauses | Pause for one step after reading a 1 bit. Four variants: (a) on one fixed input bit; (b) on each of the first ⌈L/4⌉ bits; (c) on every bit; (d) on every bit, except on the inputs whose first ⌈√L⌉ bits are 0, which run without pauses. | Pauses enter no cell and move no head, so revisits, crossings and entries are those of the machine without pauses. (a) gives two traces of probability ½: low adaptivity, not oblivious. (b) gives entropy L/4 with every trace of probability 2^(−L/4): low adaptivity, no trace of probability 2^(−o(L)). (c) gives entropy L: high adaptivity, no such trace. (d) gives entropy L − o(L), high adaptivity, and keeps one trace of probability 2^(−⌈√L⌉) = 2^(−o(L)), the kind of trace the crossings and one-head classes ask about. |
| Deep-nesting tapes | Add two work tapes, carrying no data, that run paper 8's deep-nesting pair U(s₀, m, 1) with m growing with d and stroke length Λ = 2^s₀ chosen with mΛ = o(L). | Two heads of unbounded owner load, outside Theorems F, B and M: an oblivious machine with these tapes lies in the deep piece. Their excursions are O(Λ) = o(L) and their dependency edges span o(L) steps, so they add no macroscopic revisit, no long-range head and no input read near an output. |

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
  machine is oblivious (paper 16, Theorem 10.3; Corollary 10.4 across scales). Adaptive machines with
  O(1) coarse passes are excluded only in polynomial time, so they are not in the strip.
- **Output phase** (outside, with a dotted ?). On every run, the output is produced in a final stretch in
  which the input head and a fixed set of bank heads make O(1) phases, monotone up to o(L) jitter. Every
  other head visits o(L) cells, and a fixed fraction of the input rows is unread when the stretch
  begins. Paper 16, Theorems B and J with their suffix forms, excludes linear time. With the whole run as
  the stretch, no oblivious transposer has the property at any running time, and no adaptive one in
  polynomial time (paper 16, Theorem 10.3). Whether a transposer with an unrestricted prefix, or an
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
- **Few macroscopic crossings.** On such a trace, some fixed fraction of the outputs, the same for every
  θ, is cut off by o(L) steps from the starts of crossing revisits of excursion more than θL, for every
  fixed θ > 0. Paper 16, Theorem X and Corollary 5.6, together with Theorem E(a) for heavy traces,
  excludes linear time. The order of quantifiers matters: Theorem X's threshold shrinks with the output
  fraction, so the fraction must be fixed before θ is chosen.
- **Half-bound circle.** The machine is oblivious and, for every fixed radius r, its ball relations of
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
| Half-bound circle | overlap | Round trip |
| Few large families | overlap | Counter |
| Few macroscopic crossings | overlap | Counter |
| One long-range work head | overlap | Every oblivious one-tape machine lies in it (an inclusion, stated on the cards but not drawn) |
| Oblivious data movement | overlap | Round trip, Counter |
| Bounded merging, linear data path | overlap | Round trip |

**Oblivious data movement**

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious | inside | Definition |
| Low adaptivity not oblivious, high adaptivity | apart: disjoint | It lies inside the oblivious circle |
| Oblivious, shallow | overlap | Round trip |
| Oblivious, deep | overlap | Round trip with deep-nesting tapes |
| Each cell entered O(1) times | overlap | Fresh copy |
| Half-bound circle | overlap | Round trip |
| Few large families | overlap | Counter |
| Few macroscopic crossings | overlap | Counter |
| One long-range work head | overlap | Counter |
| One work tape | overlap | Round trip, Counter |
| Bounded merging | inside | Pure data movement has bounded merge depth (paper 11, Remark "Examples") |
| Linear data path | inside | Copying is linear over every field (paper 8, Definition "Linear data path") |

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
| Half-bound circle | overlap | Parked counter |
| Few large families | overlap | Counter |
| Bounded merging, linear data path | overlap | Counter |
| One work tape | overlap | Counter |
| Oblivious data movement | overlap | Counter |
| One long-range work head | overlap | Counter |

**One long-range work head**

| Piece | Drawn | Reason |
|---|---|---|
| Oblivious, shallow | overlap | Round trip, Counter |
| Oblivious, deep | overlap | Round trip or Counter, with deep-nesting tapes |
| Low adaptivity, not oblivious | overlap | Counter with pause variant (a) |
| High adaptivity | overlap | Counter with pause variant (d) |
| Each cell entered O(1) times | apart, dotted ? | Not known |
| Half-bound circle | overlap | Round trip |
| Few large families | overlap | Counter |
| Bounded merging, linear data path | overlap | Round trip, Counter |
| One work tape | overlap | Round trip, Counter |
| Oblivious data movement | overlap | Round trip, Counter |
| Few macroscopic crossings | overlap | Counter |

## Inclusions

Drawn, each proved:

- oblivious inside low adaptivity, since an oblivious machine has a single trace;
- the shallow and deep pieces, the half-bound circle, oblivious data movement and both overlays inside
  the oblivious circle, by definition (paper 8 defines a linear data path only for oblivious machines);
- few large families inside the shallow piece, since N classes of disjoint spans leave at most N families
  open at any step, so the owner load is at most N;
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
- The two paper 16 islands, few macroscopic crossings and one long-range work head, are dark-outlined
  pieces with pairwise claims, like the two former bands.

## Construction strategies ruled out

Two results on the page rule out informal construction strategies rather than machine properties, and are
listed below the frame instead of being drawn as pieces.

- **XOR-frame recursions** (paper 1, §12). The model is a recursion that interchanges address chunks with
  XOR gadgets in sheared frames, where each frame change costs a recursive interchange of narrower chunks.
  Every gadget needs at least as many frame changes as it has wires, so the recursion cannot reach linear
  time within the template. Paper 1 calls the link between the template and the preprint's construction
  informal, and says the results rule out a class of constructions, not linear-time transposition.
- **Local packet coding with a small helper budget** (paper 2). The model is an information-access model:
  receivers that each hold one original row read a broadcast of fixed two-coordinate Boolean packets and a
  helper. Such broadcasts cannot save a fixed fraction of the bits. No theorem turns a machine's run into
  such a broadcast.

In both cases nothing decides, yes or no, whether a given machine follows the strategy, so there is no set
of machines to draw. They stay on the page because they close two routes to a construction: the recursion
behind the only claimed transposer faster than O(L log d), and a natural local coding scheme. A
machine-level version of either, turning the machines that follow it into runs of the model, would make it
a set of machines and an island of the diagram.

## The goal: a certificate for every Venn cell

The pairwise rule is a first step. The aim is a certificate for every Venn cell inside an outlined piece,
that is, for every combination of presence and absence of the other pieces: a witness transposer if the
cell is non-empty, a proof if it is empty. Nothing more is drawn for this; the record is kept here.

A witness whose membership in every piece is determined certifies exactly one cell. The memberships of
the witnesses above are as follows (S, D: oblivious shallow and deep; LA: low adaptivity, not oblivious;
HA: high adaptivity; ✓ member, · not a member).

| Witness | Adaptivity | Entry O(1) | Half-bound | Few families | Merging | Linear | One tape | Data movement | Crossings | One head |
|---|---|---|---|---|---|---|---|---|---|---|
| Round trip | S | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | · | ✓ |
| Counter | S | · | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Parked counter | S | · | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Fresh copy | S | ✓ | ✓ | ✓ | ✓ | ✓ | · | ✓ | · | · |
| Round trip + deep-nesting tapes | D | · | ✓ | · | ✓ | ✓ | · | ✓ | · | ✓ |
| Counter + deep-nesting tapes | D | · | · | · | ✓ | ✓ | · | ✓ | ✓ | ✓ |
| Parked counter + deep-nesting tapes | D | · | ✓ | · | ✓ | ✓ | · | ✓ | ✓ | ✓ |
| Fresh copy + deep-nesting tapes | D | · | ✓ | · | ✓ | ✓ | · | ✓ | · | · |
| Round trip, pauses (a) | LA | · | · | · | · | · | ✓ | · | · | ✓ |
| Counter or parked counter, pauses (a) | LA | · | · | · | · | · | ✓ | · | ✓ | ✓ |
| Round trip, counter or parked counter, pauses (b) | LA | · | · | · | · | · | ✓ | · | · | · |
| Fresh copy, pauses (a) or (b) | LA | ✓ | · | · | · | · | · | · | · | · |
| Round trip, pauses (d) | HA | · | · | · | · | · | ✓ | · | · | ✓ |
| Counter or parked counter, pauses (d) | HA | · | · | · | · | · | ✓ | · | ✓ | ✓ |
| Round trip, counter or parked counter, pauses (c) | HA | · | · | · | · | · | ✓ | · | · | · |
| Fresh copy, pauses (c) or (d) | HA | ✓ | · | · | · | · | · | · | · | · |

Reasons for the entries that are not immediate from the constructions:

- The half-bound circle, few large families and both overlays are defined for oblivious machines only,
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
- The counter machine is not in the half-bound circle: each output reads its own source at the append
  step, so its relations contain loops and admit storage codes of rate 1.
- The deep-nesting tapes put a machine outside the shallow piece and so outside few large families. They
  break bounded entry and change no other entry.
- The crossings and one-head classes ask for a trace of probability 2^(−o(L)). Pause variants (b) and (c)
  leave none, so those witnesses lie outside both classes, even with one work tape.

The rows certify 16 distinct cells as non-empty. Proved inclusions and disjointness settle every cell
that would put a transposer in two places the map keeps apart:

- one work tape in the deep piece;
- an oblivious one-tape transposer outside the one-head class;
- oblivious data movement outside the oblivious circle or outside either overlay;
- the half-bound circle, few large families or an overlay outside the oblivious circle;
- few large families or bounded entry in the deep piece.

Those cells are empty. Every other cell inside an outlined piece is open: no witness for it is known, and
no published result rules it out.

## Open questions

- Can a transposer with bounded cell entry have one work tape, few macroscopic crossings, or only one
  long-range work head? No published result settles any of the three (the dotted ? links from the
  bounded-entry disc). For one work tape, a crossing-sequence argument is a likely route to a negative
  answer.
- Does any transposer, at any running time, have the output-phase property? With the whole run as the
  stretch, coarse pass counting (paper 16, Theorem 10.3) rules out oblivious transposers at any running
  time and adaptive ones in polynomial time; with an unrestricted prefix, the pass bounds say nothing.

## How the geometry is checked

[`check_layout.py`](check_layout.py) reads the shapes back out of the SVG in `index.html` and checks them with
exact polygon operations. Run it from the repository root with

```sh
uv run --no-project --with shapely python frontier/check_layout.py
```

It checks that

- every required overlap of each dark-outlined piece has visible area, and it misses every other piece;
- every required separation has a gap;
- every required inclusion holds;
- no shape lies inside another unless the inclusion is listed above;
- every dotted ? link joins the outlines of the two shapes whose relation is open;
- the green question marks sit in the pieces their cards describe.

It exits with status 1 if any check fails. Its lists of overlaps, separations and inclusions mirror the
tables above; change both together.
