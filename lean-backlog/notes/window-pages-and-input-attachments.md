# Window pages, input attachments, and the one-work-tape calibration

Hans Brende and GPT-6 Astra, 13 November 2026. Fronts D1/D4/D9.

This audits the one-work-tape proposal in Fable's C22. The corrected page
theorem and the interval-overwrite core are Lean-verified. The separator
criterion and expander control below have **written proofs only**. The
control is a unit-speed geometric schedule with supplied page lists; no
fixed one-work-tape compiler or transposition-correctness claim is made.

The conclusion is specific: planarity of the work-window graph alone does
not supply a separator of the helper relation. Input attachments must be
included. This does not refute the row-spread theorem or a half-rate bound
for the correctly specified native class.

## 1. Keep the graph layers distinct

Write $h=db$ and $L=d^2b$. There are four relevant graphs:

- The **work-window graph** has time windows as vertices and state/work
  predecessor-window edges. One work head gives two noncrossing pages
  plus the spine, hence a planar simple graph.
- The **row helper graph** $H$ is bipartite, on raw rows $A_i$ and physical
  output rows $B_j$. An edge means that a cone in output row $j$ reads a
  bit of raw row $i$. A declared whole-row helper relation can add edges.
- The **actual coordinate incidence graph** has separate input and demand
  ports for each bit. It uses actual cones, with the transpose demand
  indexing. Pairing ports are not identified or joined by incidence edges.
- The **whole-row completion** gives each output bit every bit of each
  declared helper row. A row edge becomes a $K_{h,h}$ between coordinate
  port groups. Completing a relation can destroy a useful separator bound.

[Paper 5, Theorem 4.2 and Corollary 4.4][P5sep] require separators or
uniform hyperfiniteness at the **coordinate-port** layer. The paired-distance
theorem applies to the actual degree-capped native cones, not arbitrary
whole-row completions. None of these statements transfers work-window
planarity through the input attachments.

Even a matching row graph illustrates the distinction. Its whole-row
completion consists of $d$ copies of $K_{h,h}$. For fixed $K<h$, each copy
requires at least $h$ port deletions to leave components of size at most
$K$. Thus this completed graph is not uniformly hyperfinite as $h$ grows.
A half-rate argument can still work by separating paired coordinates in
different components; bounded component size is not necessary for that.

Input attachments are not globally monotone. At window width four, the
unit-speed raw walk

```
0 1 2 3 | 4 5 6 7 | 6 5 4 3 | 2 1 0 0
```

has input-row sets $\{0\},\{1\},\{0,1\},\{0\}$. The local two-row bound
does not control all visits to one row across time. Output-row append
intervals, in contrast, are ordered.

## 2. A sufficient row-separator bound

Let $C$ be a nonempty whole-row code on $d\times d$ matrices over $q\ge2$
symbols. In its bipartite row helper graph delete raw-row vertices $S$ and
output-row vertices $T$. Put $z=|S|+|T|$, and suppose the remaining
components have at most $K$ row vertices. Let component $c$ contain $a_c$
raw-row vertices and $b_c$ output-row vertices. Then

$$
\log_q\#C\le\frac{d^2+u}{2},\qquad
u=dz-|S||T|+\sum_c a_cb_c,
$$

and

$$
\sum_c a_cb_c\le\frac{K(2d-z)}4,\qquad
\log_q\#C\le\frac{d^2+dz+Kd/2}{2}.
$$

*Proof.* Freeze coordinates $(i,j)$ whose $A_i$ or $B_j$ was deleted,
and those whose two row vertices belong to the same surviving component.
The two sets are disjoint and have exactly the stated total size $u$.
Every remaining paired coordinate has its two ports in different row
components, while every recovery incidence stays inside a row component.
Consequently its ports are also in different components of the completed
coordinate incidence graph. Paper 5's separated-components lemma bounds
each conditional code by $q^{(d^2-u)/2}$. There are at most $q^u$ fibres.
Finally $a_cb_c\le(a_c+b_c)^2/4\le K(a_c+b_c)/4$, and
$\sum_c(a_c+b_c)=2d-z$. ∎

Thus $z=o(d)$ and $K=o(d)$ give half rate, uniformly in $q$. Uniform
hyperfiniteness of the **row** graph also suffices, by taking the dimension
limit at each fixed deletion fraction and then sending that fraction to
zero. No paired-distance hypothesis is needed for this row-level argument.
The result reuses Paper 5's finite conditioning and component bound; it
does not provide the required row separator.

If further genie information is used to obtain the row separator, that
cost remains payable. For arbitrary old storage codes, use the
[raw-boundary transfer](row-spread-of-cones.md#4-arbitrary-code-fibres-the-raw-boundary-strengthening),
not an assumption that a machine's step values preserve every such code.

## 3. Input attachments can create a robust expander

Use the ordered bipartite expanders of [Paper 5, Lemma 7.1][P5exp]. For
fixed constants $J,\Delta,\eta>0$, with $\eta\le1$, the graph $H_m$ has
$m$ source vertices and $m$ target vertices, degree at most $\Delta$,
vertex expansion

$$|N(U)\setminus U|\ge\eta|U|\quad (|U|\le m),$$

and its edges partition into $J$ partial increasing matchings. Set
$d=2m$, $h=db$, $L=dh$. Supply these ordered matching lists to the following
geometric schedule with one raw head, one work head and ordered appends:

1. Append the first $m$ raw rows $A$ in order, with the work head parked at
   zero. Load the last $m$ rows $B$
   into a contiguous work bank. Return both heads to zero.
2. For each matching page, visit its source/target row pairs $(a,t)$ in
   increasing order. Position both heads monotonically at $ah$ and $th$,
   waiting only at row starts. Scan their $h$ bits in lockstep. Optionally
   use the local update $B_t[v]\leftarrow B_t[v]\mathbin{\mathrm{xor}}A_a[v]$.
   Rewind both heads after the page, preserving the bank.
3. Append the work bank in order, with the raw head parked at zero.

The expander's local target $t<m$ is physical output row $m+t$; its core
embeds at the global row-helper vertices $A_a$ and $B_{m+t}$ of Section 1.

There are exactly $L$ appends. Initial output/load/reset costs at most
$2L$ ticks. The two forward distances on a page sum to at most $L$, and
its joint rewind costs at most $L/2$. Final output costs $L/2$. Hence

$$T\le(5/2+3J/2)L.$$

This specifies every positioning phase and retains preserving visits.
The optional computation is a shear, not transpose. Generating the lists
and implementing this scheduler with a fixed **one-work-tape** native
controller is an additional obligation not discharged here.

For each edge $A_aB_t$ and each interior lane $v=1,\ldots,h-1$, follow
consecutive visits to work cell $th+v$ backwards from its final append to
the page step reading $A_a[v]$. This is an actual dependency path of at
most $2J+3$ edges. Interior cells are visited at most once per forward
scan and per rewind, including the initial post-load rewind. Lane zero is
excluded because waits there can add
arbitrarily many visits. Each step lies on at most $\Delta$ of these paths:
it scans one work cell, and that target row has at most $\Delta$ neighbors.

For **any** genie $\Gamma$, losing a row edge from the full cone helper
graph requires hitting all its $h-1$ lane paths after their roots. Thus
the number $f$ of lost expander edges satisfies

$$f(h-1)\le\Delta|\Gamma|.$$

Suppose row-vertex deletion reduces the remaining helper graph to components
of size at most $K$. Its expander core has $d$ vertices. If fewer than
$d/4$ core vertices were deleted and $K\le d/4$, collect surviving core
components until their union $U$ has size between $d/4$ and $d/2$.
Every original neighbor outside $U$ is a deleted vertex or an endpoint of
a lost edge. For $z$ deleted row vertices,

$$\eta d/4\le z+f.$$

If $h\ge2$ and $|\Gamma|\le\eta L/(16\Delta)$, then
$f\le\eta d/8$, and necessarily $z\ge\eta d/8$. The same lower bound
already holds when $z\ge d/4$. Therefore, at each fixed $K$ and all large
$d$, a fixed positive fraction of row vertices must be removed. The row
helper graphs are not uniformly hyperfinite, despite having only one work
walk and hence planar work-window graphs. Adding helper incidences cannot
weaken this obstruction.

This disproves a separator transfer based only on those **geometric**
premises. It does not claim an expanded family in the fixed one-work-tape
native class without the missing compiler, or a near-full-rate correct
source, or a code above half rate.

## 4. What remains of the calibration

Adding the raw-head visit structure makes the omitted source connections
explicit. These are geometric bookkeeping edges, not computational
dependency edges from a mutable input. The raw walk contributes its own
two noncrossing pages; the union with the work layer need not be planar.
The preceding control shows the problem at the row-incidence layer
without appealing to arbitrary abstract four-page graphs.

The actual one-work-tape machine exclusion remains established elsewhere:
[Paper 16, Corollary 4.2][P16heads] excludes the relevant oblivious correct
traces; [Paper 18, Theorem 4.3][P18returns] gives the stronger adaptive
success bound. At one work tape the off-carrier set is empty, so their
positive required return invoice is violated. These correctness-dependent
theorems do not assert a half-rate bound for every code on every one-work
relation. The classical Boolean result is Dietzfelbinger and Maass's
[1993 Theorem 2.1](https://igi-web.tugraz.at/PDF/46.pdf), for a two-way
read-only input and write-only output, with optimal time $\Theta(n^{5/4})$.
The separator proposal in this note has not rederived these exclusions.

Two tasks remain directly meaningful: obtain a paid separator of the
**augmented row helper graph** using additional native/correct-source
structure, or prove a coding deficit that tolerates its expansion. Neither
may assume globally monotone input attachments, nor ignore the difference
between a geometric schedule and a fixed native program.

## 5. Reproduction and formal status

From the repository root:

```sh
python3 lean-backlog/tools/window_page_controls.py
```

This uses only Python 3. Optional `--output PATH` saves the receipt. It
checks 118,078 exact walk/window cases, the missing-start-cell examples,
both signs witnessing one coarse edge, loss of endpoint uniqueness, and
nonmonotone raw attachments. It does **not** test the expander family or
compile a native machine; those claims have the written scope above.

For Lean, run the three commands in the
[row-spread note](row-spread-of-cones.md#5-formal-status-and-reproduction).
`WindowAmortization.lean` proves literal interval-overwrite accounting;
its native label adapter remains pending. `WindowPages.lean` proves the
page theorem for the exact native dependency quotient, reusing the
existing walk-stack theorem. `StatementsRowSpread.lean` proves the finite
rectangle expansion bound as well as the earlier code/cut adapters.
The separator criterion and expander control here are not Lean-verified.

[P5sep]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/directed-coding.tex
[P5exp]: ../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/native-examples.tex
[P16heads]: ../../Oblivious-Linear-Time-Tape-Transposers-Need-Macroscopic-Crossings/paper/sections/heads.tex
[P18returns]: ../../Macroscopic-Information-Transfer-in-Adaptive-Tape-Transposition/paper/sections/returns.tex
