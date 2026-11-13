# Whole-row shape after an additional cheap cut

Hans Brende, Claude Fable 5.2 and GPT-6 Astra, 13 November 2026.

**Fronts D4/D9 and D1.** Fable proposed the window argument in C20; Astra's
audit corrected its conventions, sharpened the finite bound, and added the
raw-boundary transfer below. The window/row-spread theorem is now completely
**Lean-verified**, including the native geometry and all counting adapters.
[WindowSpread.lean](../WindowSpread.lean) proves the exact target in
[StatementsRowSpread.lean](../StatementsRowSpread.lean) as a corollary of a
stronger prefix theorem. The machine/crux consequences below retain reviewed
written proofs; the whole-row capacity bounds remain conjectural.

This is an extraction, not a capacity bound. After a small additional genie,
all bit cones in almost every output row use boundedly many input rows. The
bound is uniform in dimension and entry width, with depth and the other
parameters fixed first. It does not give the stronger global monotone
row-word cover of Paper 5; Section 6 explains the countercontrol.

## 1. Definitions and conventions

Use the actual native dependency graph and `coneSystem` of
[Paper 14](../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/lean/BoundedStackDepth/Machines.lean).
A trace has $k$ unit-speed work heads, a unit-speed two-way input head, and
at most one append per step. The input/output length is $L=d^2b$, with
$b\ge1$, and a physical row has $h=db$ bits. The horizon obeys
$T\le C(L+1)$, $C\ge1$, and exactly $L$ bits are appended.

State edges go to the preceding step; work edges go to the last earlier visit
to the same scanned cell. Pauses are already accounted for by the state edge;
a first visit has no earlier work predecessor. Positions and reads are those
before the transition. A $\Gamma$-free path excludes revealed vertices
**strictly after its root**. Depth $D$ here means at most $D$ edges, hence at
most $D+1$ vertices, matching the `SCone` convention.

Partition the steps into $N=\lceil T/h\rceil$ windows of $h$ steps, the last
possibly shorter. For real $C$ the safe bound is

$$N\le T/h+1\le Cd+C/h+1. \tag{1}$$

Neither correctness nor obliviousness is needed for the geometric result on
one trace. The integer price $\beta\ge1$ per revealed step is a parameter; for
machine-value applications take it at least the machine's value width.

## 2. Window accounting

**Lemma 1 (amortized predecessor windows).** For one work tape, let $m_i$ be
the number of earlier windows containing the last pre-window visit to some
cell scanned in window $i$. Then $\sum_i m_i\le3N$.

*Proof.* At each window boundary label every tape cell by the most recent
window that scanned it, or by “never”. There are finitely many maximal
constant-label intervals, even on the infinite tape; initially there is one.
Let their number be $\Phi_i$. The next window scans an interval. If it
intersects $q_i$ label intervals, replacing its labels by $i$ leaves at most
three in their place: a left remainder, the new interval, and a right
remainder. Thus $\Phi_{i+1}\le\Phi_i-q_i+3\le\Phi_i-m_i+3$.
A repeated label can occupy multiple blocks, but $q_i\ge m_i$ still holds.
Sum and use $\Phi_0=1\le\Phi_N$. ∎

The finite interval-overwrite inequality and this endpoint-potential
telescoping are now Lean-verified in
[WindowAmortization.lean](../WindowAmortization.lean). Overwrite labels need
not be fresh, and any subset of the encountered old labels can be charged.
[WindowLabels.lean](../WindowLabels.lean) proves the native visited
interval and exact last-window-label overwrite. [WindowCounting.lean](../WindowCounting.lean)
enumerates a fixed finite integer span, proves the literal list update,
and transfers the predecessor-label count. Its theorem
`sum_predecessorWindows_le_three_mul` proves Lemma 1 directly from
`IsWalk`, including zero-width and empty clipped-window cases.

This is interval bookkeeping related to the block computation graphs in
[Hopcroft, Paul and Valiant, *On Time Versus Space*, JACM 24(2), 332–337
(1977), §2, p. 333](https://www.csd.uwo.ca/~mmorenom/CS433-CS9624/Resources/p332-hopcroft.pdf).
Their construction first makes a simulation block-respecting; Lemma 1 works
on the given walk. We found no statement of the following same-trace
extension in Papers 5, 11 or 14 or their shared Lean dependencies. This is
not an exhaustive novelty claim about the literature.

**Proposition 2 (finite row spread; Lean-verified).** Let $d\ge4$, $b\ge1$, $\beta\ge1$,
$C\ge1$, $\varepsilon>0$, and let $\Gamma$ leave full depth at most $D$. Put

$$M=\left\lceil\frac{4k(k+1)\beta C}{\varepsilon}\right\rceil,
\quad M'=\left\lceil\frac{2C}{\varepsilon}\right\rceil,
\quad w=2(M'+1)(M+2)^D. \tag{2}$$

There exist $\Gamma'\supseteq\Gamma$, a set $E$ of output rows and helper-row
sets $\rho(r)$ such that

$$\beta\,\#(\Gamma'\setminus\Gamma)\le\varepsilon L,
\qquad \#E\le\varepsilon d,\qquad \#\rho(r)\le w,$$

and for $r\notin E$ every bit cone in output row $r$ lies in the input rows
$\rho(r)$. The original depth bound is preserved.

The stronger theorem `WindowSpread.native_row_spread_prefix` only requires
**at least** $L$ appends, allows any natural step price $\beta$ (including
zero), and proves

$$\Gamma'\setminus\Gamma\subseteq[0,T),\qquad
\beta\,\#(\Gamma'\setminus\Gamma)\le\frac{63}{64}\varepsilon L,
\qquad \#E\le\frac{21}{32}\varepsilon d. \tag{2a}$$

The width is unchanged. `nativeRowSpreadQuantitative` derives the original
statement directly, and `nativeRowSpreadExtension` gives its qualitative form.

*Outline of the formal proof.* Call a window bad if the **union** of its
work predecessor windows over all tapes has more than $M$ elements. Its
size is at most the sum of the per-tape counts, so
$(M+1)\#\mathrm{bad}\le3kN$. This union criterion can reveal fewer windows
than the initial sum criterion. When $M>0$ it also gives the older bound
$\#\mathrm{bad}\le3kN/M$.
Reveal the preceding state step of each bad window and every external work
predecessor of every step in it. Window zero is never bad. At most
$kh+1\le(k+1)h$ steps are charged per bad window. With (1),

$$\beta\,\#(\Gamma'\setminus\Gamma)
\le\frac{3\varepsilon}{4C}Nh
\le\frac{3\varepsilon}{4}(L+1+h/C)
\le\frac{63}{64}\varepsilon L \quad(d\ge4). \tag{3}$$

The price bound is automatic when $\beta=0$. The last inequality uses
$1/L\le1/d^2$ and $h/(CL)\le1/d$. The initial cut
may be arbitrarily expensive; only new steps are charged. If $k=0$, there
are no bad windows and no added cuts; below $M=0$ and only state edges remain.

A free path cannot leave a bad window backwards: every external target has
been revealed, even when the path's root is revealed. A good window has at
most $M$ work predecessor windows plus the preceding window. Including a
stay choice, at most $(M+2)^D$ windows are reachable in at most $D$ edge
transitions. The input head scans at most $h$ consecutive positions in one
window, hence meets at most **two** physical input rows; out-of-input
positions contribute no bits.

For each requested output row take the interval from its first to its last append,
not just its possibly sparse append set. These intervals are disjoint and
ordered. A row interval meeting more than $M'+1$ windows contains at least
$M'$ complete windows between its endpoint windows. There are therefore at
most

$$\#E\le N/M'\le\frac{21}{32}\varepsilon d\le\varepsilon d$$

such rows. Every other row uses at most $M'+1$ starting windows. Union their
reachable windows and the two input rows per window to obtain (2).
Enlarging a cut cannot increase free-path depth. The common estimate
$16Nh\le21CL$ gives both constants in (2a), as proved in
[WindowBudgets.lean](../WindowBudgets.lean). The proof modules use the
actual `prevS`, `DepStep`, `readPos` and `appendTime` definitions; no native
compatibility or counting premise is left undischarged. ∎

## 3. The whole-row capacity statement actually needed

A whole-row code is a set of matrices over a finite alphabet $\Sigma$ such
that column $r$ is determined, on that code, by all entries of one set
$\rho(r)$ of at most $w$ rows. Decoding may be nonlinear and may vary
between columns. A capacity upper bound assumes no efficiency of decoding.

The canonical alphabet is $\Sigma_d=\{0,1\}^{b(d)}$, of size $2^{b(d)}$,
**not** exactly $d$ in general. The dimension threshold must work along these
growing alphabets. Separate fixed-alphabet theorems with uncontrolled
alphabet-dependent thresholds do not suffice. Nor does the scalar-linear
D1 proposition in `StatementsWholeRow.lean` cover these nonlinear fibres.

An adequate target is: for every fixed $w$ and every $\eta>0$, all large $d$
and **all finite alphabets**, uniformly, have

$$\#C\le(\#\Sigma)^{(1-\delta(w)+\eta)d^2}. \tag{4}$$

Restricting (4) to $\Sigma_d$ is a weaker sufficient target for canonical
width. For bit transposition alone a binary bound suffices; Paper 3 does not
provide an unrestricted word-to-bit reduction.

Exceptions need no new conjecture. Freeze $e$ exceptional columns. The at
most $(\#\Sigma)^{de}$ resulting fibres have constant decoders on those
columns, with empty helper sets. All good columns keep their helper rows.
Thus an all-column cardinal bound $A$ implies $(\#\Sigma)^{de}A$ with
exceptions. This finite lemma is Lean-verified as
`exceptional_column_card_bound`.

**Corollary 3 (direct machine consequence).** Suppose (4) holds at the width
in (2), with $D$ supplied by Paper 14 Corollary 9.3(a) at price
$\varepsilon L$. If $\delta(w)>(169/64)\varepsilon$, there is no correct oblivious
linear-time transposer with those fixed resources at all sufficiently large
dimensions. The earlier conditions $\delta(w)>3\varepsilon$ and
$\delta(w)>4\varepsilon$ remain sufficient.

*Proof.* The original genie and Proposition 2 cost at most $(127/64)\varepsilon L$
bits together. Paper 14's `exists_indexCode` holds for **any** revealed set,
so a largest actual value fibre has at least $2^{(1-(127/64)\varepsilon)L}$ inputs.
Output row $r$ demands input column $r$. The new fibre is a whole-row code
outside at most $(21/32)\varepsilon d$ columns. Freezing these and applying (4)
bounds its size by $2^{(1-\delta(w)+\eta+(21/32)\varepsilon)L}$. Choose
$0<\eta<\delta(w)-(169/64)\varepsilon$. ∎

A half-rate bound for every fixed window, uniform along the canonical
alphabets, would therefore exclude the machines; $\varepsilon=1/9$ works.
The known gap $1/(w+1)$ is too small. A hypothetical machine instead supplies
codes with rate arbitrarily near one at some fixed window for each requested
rate, along growing entry alphabets. This does not assert a fixed-alphabet
counterexample to D1 or a cheap implementation of arbitrary whole-row codes.

## 4. Arbitrary code fibres: the raw-boundary strengthening

Actual machine values suffice in Corollary 3, but need not preserve the
side information of an arbitrary code on the original cones. A different
charge resolves this at fixed original depth. For arbitrary cuts set

$$U=\bigcup_{u\in\Gamma'\setminus\Gamma}I_\Gamma(u),
\qquad B_D=\sum_{j=0}^D(k+1)^j,$$

where $I_\Gamma(u)$ is the raw-input cone at step $u$. Then

$$I_\Gamma(t)\subseteq I_{\Gamma'}(t)\cup U,\qquad
\#U\le B_D\,\#(\Gamma'\setminus\Gamma) \tag{5}$$

when original full depth is at most $D$. These assertions are Lean-verified
(`depCone_change_cut`, `card_new_cut_raw_support_le`), reusing the native
path and ball counts. The inclusion does not require nested cuts.

*Proof.* An old free path either stays free or first hits a new cut vertex
**strictly after its root**. This vertex lies in $\Gamma'\setminus\Gamma$;
the remaining suffix witnesses membership in its old cone. Each old cone
has at most $B_D$ positions. Take their union. ∎

**Corollary 4 (conditional native-crux transfer).** If, for some fixed
$\delta>0$, every fixed-window whole-row code has asymptotic rate at most
$1-\delta$, uniformly along the canonical alphabets, then Paper 14's native
`Crux` holds at rate $\delta$ for every fixed $k,\beta,C,D$. The all-finite-
alphabet version gives the corresponding bound for every $b\ge1$.
In particular, the uniform whole-row half-rate target implies native
half rate. This is a written implication, not a proof of either conjecture.

*Proof.* Start with any binary storage code on an original depth-$D$ native
cone system.
Apply Proposition 2 with step price $B_D$ and extra budget $\eta L$.
By (5) and (2a), freezing at most $(63/64)\eta L$ raw bits transfers each
resulting code fibre to the new cone relation. Freeze the exceptional
columns too, at cost at most $(21/32)\eta L$. Apply the whole-row bound
with slack $\eta$. The original code has rate at most
$1-\delta+(169/64)\eta$. For an index
code of $m$ bits its largest fibre has at least $2^{L-m}$ elements, so
$m\ge(\delta-(169/64)\eta)L$. Let $\eta$ tend to zero in the crux quantifiers.
Depth, cut price, window and slack are fixed before dimension grows.
Neither correctness nor cheapness of the initial $\Gamma$ is used. ∎

The direct machine route is quantitatively cheaper: it pays actual step
values rather than the factor $B_D$. Do not read (5) as a bound uniform
when $D$ grows with dimension.

## 5. Formal status and reproduction

`StatementsRowSpread.lean` reuses `MotionDepthCodes.IsStorageCode` and
`BoundedStackDepth.coneSystem`. It defines the geometric target and nonlinear
capacity conjectures and proves elementary adapters including exceptional
columns and (5). `WindowSpread.lean` proves the geometric target completely.
No whole-row capacity conjecture is proved. Corollaries 3 and 4 are written
consequences, not yet complete Lean theorems. All formalized endpoints use
only `propext`, `Classical.choice` and `Quot.sound`; there are no new axioms
or proof placeholders.

Check from Paper 15's existing package, which supplies both dependencies:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py
```

[The audit controls](row-spread-controls.md) give the exact finite tests and
reproduction command. Those tests check conventions and guards; the written
proofs cover unbounded dimensions. No native-machine normal form is inferred
from finite experiments.

## 6. A stronger row-word inference fails

The initial note also claimed a globally bounded cover by Paper 5's monotone
partial row words. Proposition 2 does **not** imply it. The number of monotone
pieces can grow; bounded helper-row count does not control their arrangement.

The [block-reversal control](row-spread-controls.md#block-reversal-and-global-row-words)
has $d=s^2$ and reads row $f(sa+t)=sa+s-1-t$ for output row $sa+t$ in
$O(L)$ unit-speed trace time. Direct root incidences survive every genie.
A fixed family of $K$ row words of length at most $\ell$ and band radius $a$
has at most $H=K(2a+1)^{\ell+1}$ monotone branches. Each agrees with $f$ on
at most $s$ rows. Allowing a coordinate exception set $Z$, a cover still needs

$$\#Z\ge\frac{1-H/s}{2}\,L.$$

Thus fixed $K,a,\ell$ and $o(L)$ exceptions cannot cover these unit-speed
geometries. This refutes the stronger geometry-only inference, not row
spread or an extraction claim restricted to correct transposers. The control
does not transpose arbitrary inputs.

## 7. Expansion and the corrected page structure

Fable proposed these two statements in C22. The rectangle version of
Proposition 7.1 and the exact native dependency-page version of Proposition
7.2 are now Lean-verified. The input-attachment and separator qualifications
below are essential to their use.

**Proposition 7.1 (incidence-free rectangles).** Let $C$ be a whole-row code
on $d\times d$ matrices over an alphabet of $q$ symbols. If
$R,J\subseteq[d]$ and $\rho(j)\cap R=\varnothing$ for every $j\in J$, then

$$\#C\le q^{d^2-|R||J|}.$$

If $q\ge2$ and $\#C\ge q^{(1-\delta)d^2}$, this implies
$|R||J|\le\delta d^2$. These statements are
`wholeRow_rectangle_card_bound` and `wholeRow_rectangle_deficit` in
[StatementsRowSpread.lean](../StatementsRowSpread.lean).

*Outline.* The coordinates outside $R\times J$ determine every coordinate
inside it, since their helper rows avoid $R$. This is precisely the
independent-coordinate bound already proved in
[Paper 5's `StorageCode.lean`](../../Directed-Recovery-Structures-in-Tape-Computations/lean/DirectedRecovery/StorageCode.lean).
The formalization reuses that result; it does not rebuild entropy machinery.

The following two consequences hold for every $A\subseteq[d]$:

$$
(d-|A|)\,\#\{j:\rho(j)\subseteq A\}\le\delta d^2,
\qquad
(d-|A|)\,\#E(A)\le\delta d^2,
$$

where $E(A)=\{i:\forall j,\ i\in\rho(j)\Rightarrow j\in A\}$.
For the first take $R=A^c$ and $J=\{j:\rho(j)\subseteq A\}$.
For the second take $R=E(A)$ and $J=A^c$. The second conclusion strengthens
the initial version: **the rows in $E(A)$ need not themselves belong to
$A$**. At a half $|A|=d/2$, both counts are at most $2\delta d$.
The large whole-row fibres extracted from a hypothetical transposer must
satisfy these conditions with $\delta$ of order $\varepsilon$.
This is a necessary expansion condition, not a new capacity bound.

**Remark (the limit of one particular patch accounting).** Let
$A=\rho(J)=\bigcup_{j\in J}\rho(j)$. Recovery guarantees a deficit credit
$e=|J|(d-|A|)$ on the patch consisting of rows $A$ and columns $J$;
its size is $p=|A|d+e$. This is a guaranteed **lower credit**, not an upper
bound on the patch's actual deficit. If $|A|\ge\gamma w|J|$, with
$\gamma>0$, then $e/p\le1/(1+\gamma w)$ whenever $p>0$.

For any selected patches with credits $e_i\le c p_i$, nonnegative weights
$\lambda_i$ and maximum weighted coordinate overlap $r>0$, the credited
quantity satisfies $\sum_i\lambda_i e_i/r\le c d^2$, because
$\sum_i\lambda_i p_i\le r d^2$. Thus this **sum-of-credits divided by maximum
overlap** method cannot yield a common deficit from patches with ratio
$O(1/w)$. This does not limit every possible cover, conditional-entropy or
Shearer argument, and it does not prove that the order bound is optimal
among them.

**Proposition 7.2 (noncrossing pages after time contraction).** Contract each
fine time to its time-window number, discard loops, and merge repeated
edges. The resulting dependency graph is covered by the window spine and
$2k$ noncrossing pages. Here a page forbids strict interleaving
$u<u'<v<v'$ of two edges $(u,v),(u',v')$; shared endpoints are allowed.
The native statement is `timeWindow_dependency_pages` in
[WindowPages.lean](../WindowPages.lean). More generally, a nondecreasing
chronological contraction preserves noncrossing, and any such contraction
increasing by at most one at each fine step sends state edges to the spine.

*Outline.* For a predecessor-label witness cell, choose its first visit
$q$ in the later window. Its last visit $p$ before that window is its actual
previous visit. If $q=p+1$, the coarse edge lies on the spine. Otherwise the
walk between $p$ and $q$ stays strictly above their common cell or strictly
below it. Same-side excursions cannot cross. This fine-time decomposition
is already `BoundedNesting.walkDag_isStack`, recalled in
[Paper 14, §2](../../Bounded-Stack-DAGs-Reduce-to-Constant-Depth/paper/sections/preliminaries.tex).
Strictly crossing coarse endpoints would force strictly crossing fine
endpoints. The Lean proof reuses the fine theorem and proves the quotient
step. [WindowLabels.lean](../WindowLabels.lean) now proves that a last
pre-window visit is an actual `DepStep` predecessor at the first visit
inside the window, including pauses. It also proves interval visitation
and exact last-window-label overwrites. Packing these labels into the
finite-list amortization and transporting the predecessor-label count
are proved in `WindowCounting.lean`; `WindowSpread.lean` completes the extraction.

The initial classification by strict left/right of the head at the window
start omitted equality. For example, windows $0^h,1^h,0^h,1^h$ have
crossing edges $(0,2),(1,3)$, both witnessed at their destination window's
starting cell. Assigning all ties to the same page fails; their true
excursion signs are opposite. The strict-left and strict-right subfamilies
were valid, but did not cover all edges.

Contraction also loses the endpoint-uniqueness conditions of `StackDag`.
One coarse page can have unbounded degree at a vertex. Therefore the
quotient cannot be fed directly into a fixed-stack theorem without another
adapter. Lemma 1 still bounds its average in-degree by $3k+1$ when the
state spine is included.

For $k=1$ the simple work-window graph is planar: draw the two pages on
opposite sides of the spine. That is a statement about the **work** graph.
Output-row append intervals are ordered, but the attachment of a time
window to its at most two consecutive input rows need not be monotone.
The actual row relation is contained in the composition of these
attachments with bounded-depth dependency reachability; the attachments
cannot be dropped. Arbitrary graphs with the same page count are not
thereby proved to be native cone systems.

[The one-work-tape calibration](window-pages-and-input-attachments.md)
explains why work planarity alone does not supply the separator hypothesis
on the helper relation, and states a correct row-level sufficient criterion.
The common whole-row deficit remains open.

## 8. Grid labellings and their scope

Fable's formulation, audited and strengthened by Astra, 13 November 2026.
The results in this section have **written proofs only**. They do not give
a general coding deficit or a tape implementation.

**Definition.** Let $G$ have $L=d^2b$ vertices, with $d,b\ge1$ and arcs
$p\to q$ meaning that $q$ is a helper of $p$. A *grid labelling* consists
of maps $f,g:V\to[d]$ (row and column) with exactly $b$ vertices in every
joint fibre. Its row helper graph has an edge $g(p)\to f(q)$ for every
arc. Its forward and reverse degrees are bounded by $w,w'$ respectively.
A forward-window labelling imposes only the bound $w$.

Enumerating each joint fibre identifies a code over an alphabet $A$ with
a matrix code over $A^b$. A forward-window labelling gives whole-row
recovery of window $w$. No reverse degree bound is needed for this
implication. Conversely, whole-row recovery supplies a grid-labelled
relation, but its vertex degree may be as large as $wdb$. Bounded **bit**
degree is extra native structure.

Proposition 2 supplies forward row spread outside at most $\varepsilon d$
exceptional columns. Freeze them first, paying at most $\varepsilon L$
bits in addition to the cut. A native full-depth cone bound controls vertex
outdegree by $B_D$, not vertex indegree or reverse row degree. The following
paid reduction supplies the latter bounds while retaining the grid.

**Proposition 8.0 (conditioning without deleting grid vertices).** Let $C$
be a nonempty storage code over $q\ge2$ symbols on a forward-window grid.
For any set $Q$, some fibre obtained by fixing $Q$ has size at least
$|C|/q^{|Q|}$. On this fibre use no helpers for $p\in Q$, and replace
$N(p)$ by $N(p)\setminus Q$ otherwise. Keep all vertices and both labels.
This is a storage code on the same balanced grid, and no degree increases.

For integer thresholds $W,V\ge0$, freezing every row used by more than
$W$ columns costs at most $wL/(W+1)$ coordinates and leaves reverse row
degree at most $W$. If vertex outdegree was at most $B$, additionally
freezing vertices of indegree greater than $V$ costs at most $BL/(V+1)$
and leaves vertex indegree at most $V$.

*Proof.* Partition by the values on $Q$ and choose a largest fibre.
Its frozen arguments are constants in the old recovery functions. The
row helper graph has at most $wd$ edges, so at most $wd/(W+1)$ rows
have reverse degree greater than $W$; each contains $db$ coordinates.
The vertex relation has at most $BL$ arcs, giving the second count.
Take the union of the frozen sets. Every removed helper is constant;
keeping its vertex preserves exactly $b$ coordinates in each grid cell. ∎

**Proposition 8.1 (necessary conditions).** Write $C_r=g^{-1}(r)$ and
$H_r=\bigcup_{p\in C_r}N(p)$, a set of distinct helpers. Then:

- $|H_r\cap C_{r'}|\le wb$ for every $r,r'$;
- vertices sharing a helper with a vertex in $C_r$ lie in at most $ww'$
  columns.

*Proof.* The helpers lie in at most $w$ rows, each meeting $C_{r'}$ in
$b$ vertices. Each of these helper rows is used by at most $w'$ columns. ∎

Thus $H_r$ meets at least $|H_r|/(wb)$ columns when $w>0$. With minimum
vertex outdegree $a>0$ and maximum indegree $\Delta_{\rm in}$, this is at
least $ad/(w\Delta_{\rm in})$. The initial claim $ad/w$ omitted shared
helpers. For example, on $\mathbb Z_d^2$ the loopless rules
$(i,j)\to(j,i+t)$, $1\le t\le a<d$, have in- and outdegree $a$ and grid
window $(1,1)$, but each column's helper union meets exactly $d$ columns.

**Proposition 8.2 (exact coset windows).**

(a) Any helper permutation taking a complete column onto another complete
column forces forward window $d$ in a balanced grid. In particular this
holds for ordinary right-Cayley arrows $x\to xs$ with right-coset columns
$Kx$ and a nonempty generator set, for **any** balanced row labelling.

(b) Let a finite group have order $d^2b$, and let $K,K'$ have index $d$
with $KK'=G$ and $|K\cap K'|=b$. Use columns $Kx$, rows $K'y$, and helpers
$x\to\theta(x)s$, where $\theta$ is an automorphism and $s$ ranges over
a nonempty set $S$. Put $t=[\theta(K):\theta(K)\cap K']$. The actual
forward and reverse windows both lie between $t$ and $|S|t$. A single
generator gives exactly $(t,t)$.

*Proof.* (a) Every complete column meets every row. (b) The image of $Kx$
is $\theta(K)\theta(x)s$, meeting exactly $t$ right cosets of $K'$.
The preimage of $K'y$ is
$\theta^{-1}(K')\theta^{-1}(ys^{-1})$, meeting exactly $t$ right cosets
of $K$, since $|K|=|K'|$. Take the union over generators. ∎

The case $\theta(K)=K'$ gives both windows at most $|S|$. It is sufficient,
not necessary: bounded index $t$ is the exact criterion in this model
when $|S|$ is bounded. For $d=2^m$, $b=m$, take
$G=\mathbb F_2^m\times\mathbb F_2^m\times C_m$ with the two coordinate
subgroups including the common factor $C_m$. Swapping only $m-1$ of the
$m$ pairs of binary axes gives $t=2$ for every $m\ge2$, although
$\theta(K)\ne K'$. These are incidence examples, not high-rate codes.

**What this tests.** Labelling a displayed recovery graph is sufficient;
failure does not exclude other recovery rules for the same code. An
asymptotic half-rate counterexample needs one fixed window and rates at
least $1/2+c$, for some fixed $c>0$, along an unbounded sequence of
dimensions. Refuting a common positive deficit
requires rates arbitrarily close to one, with a window fixed separately
for each desired rate. The native alphabet is $\{0,1\}^{b(d)}$.
A single finite labelled block establishes neither asymptotic conclusion.
Even a successful abstract family still needs a paid tape implementation.

[Grid labellings and amplified codes](grid-labellings-and-amplified-codes.md)
tests Paper 15's constructions against these obligations, including
layout and small-component obstructions. Arbitrary grid labellings of its
growing seed blocks remain unresolved. The input-attachment control does
not prove that every whole-row relation is a native relation, and the
separator criterion remains a sufficient target without a known native
extraction mechanism; only the work-planarity inference is refuted (X13).

## 9. Rates at growing windows: simplex codes (Fable, 13 November 2026)

Status: **written proof only; not Lean-formalized**. For each fixed integer
$m\ge3$ this constructs codes at windows growing with $d$. The case $m=2$
recovers the pairing rate. It gives no asymptotic rate above one half at a
fixed window.

**Proposition 9.1 (projective simplex codes).** Fix an integer $m\ge2$. For
each prime power $q$, take as rows the points and as columns the hyperplanes
of $\operatorname{PG}(m-1,q)$, with $\rho(H)$ the points on hyperplane $H$.
Then

$$d=\frac{q^m-1}{q-1},\qquad w=\frac{q^{m-1}-1}{q-1}.$$

For every finite alphabet $A$ of size $a\ge2$ there are whole-row codes
$C\subseteq A^{d\times d}$ for this relation whose normalized rates
$\log_a|C|/d^2$ tend to $1-1/m$ as $q\to\infty$ through prime powers. The
convergence is uniform in $A$: for every $\eta>0$, a threshold
$q_0(m,\eta)$ works for all such alphabets. The codes can be chosen so that
each coordinate is recovered from at most $m-1$ other coordinates in its
allowed helper rows. Alternatively, incident cells may be left free and
recovered by self-reading, giving the slightly larger finite rate below.
The code alphabet and the projective field are unrelated.

*Proof.* Put $V=\mathbb F_q^m$. A projective basis is an unordered set of
$m$ independent one-dimensional subspaces $P_1,\ldots,P_m$. Let $H_j$ be the
span of the other $m-1$ points. Its simplex consists of the $m$ cells
$(P_j,H_j)$. These are nonincident, and $P_i\subset H_j$ for $i\ne j$, so
each cell's allowed rows contain all the other cells of its simplex.

Form the $m$-uniform hypergraph on the nonincident cells, with these
simplices as edges. There are

$$N=d(d-w)=dq^{m-1}$$

vertices. Write $B_0(q)=1$ and

$$B_r(q)=\frac{|\operatorname{GL}_r(q)|}{(q-1)^r r!},$$

the number of unordered projective bases of an $r$-dimensional space. A
simplex containing $(P,H)$ is determined by a projective basis of $H$;
thus every vertex has degree $\Delta=B_{m-1}(q)$. Two distinct vertices
$(P,H),(P',H')$ have codegree zero unless $P'\subset H$ and $P\subset H'$.
When these incidences hold,
$V=P\oplus P'\oplus(H\cap H')$, and a common simplex is determined by a
projective basis of $H\cap H'$. Its codegree is exactly
$\lambda=B_{m-2}(q)$. Consequently

$$\frac{\lambda}{\Delta}
=\frac{(m-1)(q-1)}{q^{m-2}(q^{m-1}-1)}
\sim(m-1)q^{-2(m-2)}.$$

For fixed $m\ge3$, $\Delta\to\infty$ and $\lambda=o(\Delta)$. The
[Pippenger–Spencer theorem, *Asymptotic behavior of the chromatic index for
hypergraphs*, JCTA 51(1), 24–42 (1989)](https://doi.org/10.1016/0097-3165(89)90074-5)
gives an edge colouring with $(1+o(1))\Delta$ colours. Since the hypergraph
is regular, its largest colour class is a matching covering $(1-o(1))N$
vertices. Let this matching have $\nu$ edges and leave $U=N-m\nu=o(N)$
vertices uncovered. For $m=2$, instead use the exact perfect matching of
ordered pairs $(P,Q)$ with $(Q,P)$: then $\nu=N/2$ and $U=0$. The
small-codegree theorem is not needed in that case, where
$\Delta=\lambda=1$.

Identify $A$ with the cyclic group of order $a$. On each matched simplex
impose a single sum-zero constraint; it has $a^{m-1}$ solutions and lets
each cell read the other $m-1$ cells. Fix uncovered nonincident cells to
zero. Initially leave all $dw$ incident cells free; they can self-read
because their own row belongs to $\rho(H)$. The constraints occupy disjoint
cells, so

$$|C|=a^{dw+(m-1)\nu},\qquad
\frac{\log_a|C|}{d^2}
=1-\frac1m+\frac{w}{md}-\frac{(m-1)U}{md^2}.$$

Here $w/d\to0$. If self-reading is forbidden, fix the incident cells to
zero as well. The rate becomes
$(1-1/m)(1-w/d-U/d^2)$, with the same limit; constant cells require no
helpers. The matching depends only on $m,q$, which proves the stated
uniformity in the alphabet. ∎

**Remark (exact vector code; written proof only).** For any finite $q$,
using the entry alphabet $A^\Delta$ removes the packing loss altogether.
Give each nonincident cell $\Delta$ lanes, one for each incident simplex.
On every simplex impose a sum-zero constraint on its dedicated lane at
each of its $m$ cells. Each underlying nonincident $A$-symbol belongs to exactly one
constraint, so these $N\Delta/m$ constraints use disjoint variables. Leave
incident cells free. The resulting code has

$$|C_{\mathrm{vec}}|=a^{\Delta d^2-N\Delta/m},\qquad
\frac{\log_{a^\Delta}|C_{\mathrm{vec}}|}{d^2}
=1-\frac1m+\frac{w}{md}.$$

Each nonincident lane uses $m-1$ other lanes in allowed rows. A whole entry
may use up to $(m-1)\Delta$ other entries, while the whole-row window stays
$w$; free incident cells still self-read. Unlike Proposition 9.1, this
exact finite construction uses selected alphabet powers and does not
assert that they fit canonical entry widths in general.

For the Fano plane ($m=3,q=2$), $d=7$, $w=3$ and $\Delta=3$. With binary
lanes this does fit the canonical width $b(7)=3$: there are $147$ bits and
$28$ independent triple constraints, giving $2^{119}$ codewords and rate
$119/147=17/21$. Disjoint scalar simplices have at most
$21+2\lfloor28/3\rfloor=39$ free entry-symbols here; the vector construction
has normalized dimension $119/3>39$. The scalar gadget count is not a
capacity bound for arbitrary codes.

This uses the established fractional clique-cover strategy of
[Christofides and Markström, *The Guessing Number of Undirected Graphs*,
EJC 18(1), P192 (2011), §4](https://doi.org/10.37236/679), also discussed
after the “Guessing numbers” corollary of
[Paper 7](../../Nested-Elimination-and-Half-Rate-Bounds-for-Storage-Codes/paper/sections/consequences.tex).
The application here is to the projective relation; the vector-coding
mechanism is not new.

- At $m=2$, $d=q+1$ and $w=1$. With free incident cells, the code has the
  usual pairing cardinality $a^{d(d+1)/2}$ and rate $(d+1)/(2d)$.
  At $m=3$, the simplices are triangles of projective points with their
  opposite sides: the limiting rate is $2/3$ at $w\sim\sqrt d$.
- For each fixed $m$, $\log w/\log d\to\alpha_m=(m-2)/(m-1)$ and the
  limiting rate is $1/(2-\alpha_m)$. These are the discrete exponents
  $0,1/2,2/3,3/4,\ldots$; the proof gives neither every real exponent nor a
  uniform assertion with $m$ growing with $q$. No matching upper bound is
  proved. The [random triangle construction](simplex-code-calibration.md)
  attains limiting rate $2/3$ with $w=(1+o(1))d^{1/3}\log d$, beating the
  formula $1/(2-\alpha)$ at $\alpha=1/3$. In particular a uniform half-rate
  bound cannot extend to these growing-window families.
- Proposition 2 supplies a **fixed** window before dimension grows.
  This implies $\log w/\log d\to0$; the converse fails, for example when
  $w=\log d$. The machine/crux consequences require a **common positive
  deficit across all fixed windows**. Their dimension thresholds may
  depend on the window; no threshold uniform along a growing $w(d)$ is
  required. The simplex construction leaves that common-deficit question
  open.

## 10. After the random-incidence code: global and conditional excess

Fable's proposal of 13 November 2026, with Astra's scope audit and Clebsch
countercontrol. The conditioned-far version is false. Section 11 subsequently
refutes the global version with a constant independent of the window;
window-dependent additive and fixed-window limiting bounds remain open.

**10.1 The proposed staircase.** The proved random triangle code has rate
$2/3-o(1)$ at $w=(1+o(1))d^{1/3}\log d$. For a fixed $m$, the expected
number of $m$-cliques through a cell in random incidence of density $p$
is, up to a fixed symmetry factor and missing-diagonal factors,

$$d^{2(m-1)}p^{m(m-1)}.$$

This suggests density $p=d^{-2/m}$, window exponent $1-2/m$, and clique
rate $1-1/m$. For $m\ge4$ this remains a first-moment calculation, not
an existence or packing theorem. The deterministic pairing relation gives
the $m=2$ endpoint; a random graph of mean degree one does not automatically
supply it. A bound $1/2+C\log w/\log d+o(1)$ applicable to the proved
triangle family would require $C\ge1/2$.

More general rooted-pattern counts depend on all their incidences and on
dense subpatterns. A finite pattern with a gain is not by itself a
positive-density construction at a specified window exponent.

**10.2 Near cells.** Call $(i,c)$ near when row $i$ and column $c$ have
distance at most three in the bipartite incidence graph of $\rho$; all
other pairs are far, including disconnected pairs. If forward and reverse
degrees are bounded by $w,w'\ge1$, then

$$N_3\le\min\{d^2,\;dw[1+(w'-1)(w-1)]\}.$$

This is an upper bound, not an equality. Forward degree alone does not
imply $N_3=O(d)$: $\rho(c)=\{0,c\}$ has window two and every cell near.
The paid reverse-degree reduction in Section 8 is needed before using
such a count on arbitrary native row-spread relations.

**Former global conjecture (refuted in Section 11).** There is an absolute constant
$C_0\ge0$ such that every whole-row code over $q\ge2$ symbols satisfies

$$\log_q|C|\le d^2/2+C_0N_3.$$

At bounded forward and reverse degrees this would give an additive $O(d)$
error. With only the forward bound, paid reverse-degree trimming would
still give limiting half rate, but not the same additive error. The proof
of that implication is in the [far-cell calibration](far-cell-calibration.md).

**10.3 The stronger gate is refuted.** It was proposed that fixing the near
cells leaves at most half of the far coordinates free. The existing
Clebsch code refutes this: use $d=16$, $\rho(c)=N_{\rm Clebsch}(c)$ and
put the ten-dimensional binary code on the diagonal. Exactly those
sixteen diagonal cells are far, all at distance five; all 240 near cells
are fixed to zero. Every active helper is mutual. This whole-row
counterexample is Lean-verified in [FarClebsch.lean](../FarClebsch.lean).
It does not show an advantage from adding one-way helpers to the full
mutual-helper graph.

This single gadget does not refute the global conjecture: its full-array
dimension is ten, far below $d^2/2=128$. Section 11 supplies a full-array
family that does refute the proposed window-independent constant. A finite far-only excess does not provide the
amplification or density needed to contradict that bound. Likewise, the
small-component theorem charges port distances up to $2s-1$ for components
of size $s$, not just distance three. Its proof is consistent with Clebsch.

The next argument must bound global information, accounting for the
entropy lost on the near coordinates as well as any gain on the far ones.
The separately restricted cubic incidence/girth-ten-or-twelve question
remains open; Clebsch has degree five and incidence girth four. It is parked
because no tie from that restriction to native cone systems is supplied. No larger-host search was required to settle the
unrestricted conditioned-far claim.

## 11. Diagonal codes and the window-dependent excess

Fable's proposal of 13 November 2026, reviewed and strengthened by Astra.
The [complete calibration](diagonal-code-calibration.md) supplies the
folded-cube proof, finite certificates and scope. The placement statement
is Lean-verified; the general hypercube bounds are reviewed written proofs.

**Proposition 11.1 (placement carries a row relation).** Let $f:[d]\to[d]$
be any function. A finite storage code with helpers $i\mapsto\rho(f(i))$ embeds
in the cells $(i,f(i))$ as a whole-row code for $\rho$, fixing other cells
and preserving cardinality. No injectivity or linearity assumption is needed.

*Outline of the formal proof.* Different coordinates occupy different
rows. Recovery reads the placed coordinates in the supplied rows and
applies the original storage-code rule. See `placedCode_isWholeRow` and
`card_placedCode` in [FarClebsch.lean](../FarClebsch.lean); the old diagonal
lemma is their identity-placement corollary. ∎

For a group $G$ and $\rho(c)=cT$, the functions $f_g(i)=ig$ partition the
array into displacement diagonals, each carrying the Cayley relation
$i\to igT$. Products of diagonal codes give whole-row codes. This is a
construction, not an assertion that all codes decompose. Ordinary
transposed-cell pairing needs self-row access (or a separately checked
twisted pairing); it is not automatic for arbitrary $T$.

**Proposition 11.2 (the hypercube family, strengthened).** For $1\le w\le k$,
$d=2^k$, and $T$ consisting of $w$ independent vectors in $\mathbb F_2^k$,
put $\rho(c)=c+T$. A binary code attains

$$\log_2|C|=d^2/2+dS(w),\qquad
S(w)=\sum_{j\text{ odd}}\binom wj2^{-(j+1)/2}.$$

Every code over $q\ge2$ symbols has
$\log_q|C|\le d^2/2+2^{w-2}d$.

*Proof.* A displacement which is a sum of $j$ odd distinct elements of $T$
has selected helpers giving disjoint folded $j$-cube subgraphs. Their
binary fitting rank is $(4^m-2^m)/2$ for $j=2m+1$, proved by the explicit
square-zero group-ring recurrence in the calibration. Ignore extra edges
and use those component codes. On remaining diagonals use a perfect
matching. For the upper bound, helper sets lie in cosets of
$\operatorname{span}\{t+t_0:t\in T\}$, of dimension $w-1$; Paper 17's
Proposition `rows`(a,c) applies. ∎

The original loop/$K_4$/Clebsch bound
$d^2/2+d[w/2+\binom w3/4+\binom w5/8]$ is the subconstruction using
$j=1,3,5$ only. Extra helpers may join its selected components, which
causes no problem because the decoder can ignore them.

For every fixed radius $r\ge1$,
$N_r=d\sum_{j\le r,\ j\text{ odd}}\binom wj$.
Since $S(w)$ grows exponentially while this sum is polynomial in $w$,
**no window-independent constant multiplying $N_r$ bounds all excess**,
for any fixed radius. The surviving additive question permits a coefficient
$F(w,w')$, necessarily at least $S(w)$ when $w'=w$. At fixed $w$ the
constructed rate still tends to one half; the native question remains open.

**Finite coupling calibration.** On $\mathbb F_2^4$, $T$ a basis has exact
whole-array capacity $q^{176}$ for every finite alphabet, attained by the
diagonal construction. The Clebsch helper set has binary diagonal dimension
210 and whole-array upper bound 211. All three types of covariant
binary two-sector coupling were enumerated exactly and none improves the
diagonal baseline; unrestricted coupling and vector/nonlinear gains remain
open. The characteristic-two group algebra does not admit the proposed
16-character Fourier reduction. See the linked calibration for the exact
scope and reproduction commands.

**General-group mutual-helper theorem (reviewed written proof).** For every
fixed window, only $O_w(d/\log d)$ displacement diagonals in any finite
group have non-bipartite mutual-helper graphs. A code recovered within each
diagonal using only its mutual helpers therefore has rate at most
$1/2+O_w(1/\log d)$, even with correlations between diagonals; a shared
advice value adds its stated information cost. The proof counts symmetric
translates using the central involutions of the subgroup generated by a
normalized helper set, then takes a finite union over helper subsets.
See [the complete proof](diagonal-code-calibration.md#5-most-translated-mutual-helper-graphs-are-bipartite).
This closes the proposed positive-density undirected/non-bipartite route.
One-way helpers and cross-diagonal recovery remain possible; no native
normal form has been proved.

## 12. The mutual-helper graph of an arbitrary row relation: two tokens (Fable, 13 November 2026)

Status: Proposition 12.1 has a **reviewed written proof**, not a Lean
formalization. Astra's review corrects the closed-walk consequences below;
[the audit and full-graph controls](two-token-and-oriented-controls.md)
contain the counterexamples, proofs and exact reproduction commands.

Let B be the incidence graph of ρ: row port i and column port r are adjacent
when i ∈ ρ(r). Cells (c,r) and (c′,r′) are mutual helpers when c′ ∈ ρ(r)
and c ∈ ρ(r′). Let M be this graph on all d² cells, including a loop at
(c,r) exactly when c ∈ ρ(r).

**Proposition 12.1 (two tokens).** A step of M moves tokens on row port c
and column port r to neighbours in B; the new cell lists the token on
the row side first. Consequently:

- (a) M is the quotient by coordinate exchange of the graph of ordered
  opposite-side pairs of B, with simultaneous moves. That graph is bipartite.
- (b) The shortest **odd closed walk** in M through (c,r) has length
  dist_B(c,r), with infinity for disconnected ports. An M-component is
  bipartite exactly when none of its cells has its two ports in the same
  B-component.

*Proof.* An odd closed M-walk lifts to two B-walks exchanging the starting
ports, giving the lower bound on length. A shortest B-path and its reverse
produce a closed M-walk of that length. Backtracking supplies every larger
**odd** length. The component criterion follows. ∎

**Consequences and limits.**

- This is not a statement about simple cycles through a cell or the number
  of distinct sectors. On a six-vertex incidence path, the endpoint cell
  is a leaf of M but has an odd closed walk of length five, using a loop
  in the middle. One Clebsch sector already contains odd cycles of length
  five. The previous inference that a bounded number of coupled sectors
  must be bipartite far away is withdrawn; Proposition 12.1 does not
  explain the negative two-sector test.
- With σ(c) = {r : c ∈ ρ(r)}, the exact neighbourhood is
  N_M(c,r) = ρ(r) × σ(c). Common-neighbour counts are products of the
  two corresponding intersection sizes. Two cells sharing a row need
  not share any helper; their count is |ρ(r) ∩ ρ(r′)|·|σ(c)|.
- A mutual-only linear code is a **subspace of** a fitting kernel
  ker(τ − K), with K(X) = Σ A_j X B_jᵀ. If P is the incidence matrix,
  the factors can be chosen with supp(A_j) ⊆ supp(Pᵀ) and
  supp(B_j) ⊆ supp(P). Every fitting recovery matrix has such an
  elementary-matrix decomposition, with no bound on the number of terms.
  For maximum dimension one may optimize over the full kernels.
- If both incidence degrees are bounded, deleting the cells at distance
  at most R leaves a bounded-degree graph of odd girth greater than R,
  after removing at most d Σ_{j≤R} Δ^j cells. Paper 4's locally bipartite
  theorem therefore bounds scalar complex-linear rates by ½+o(1), with
  uniformly bounded actual recovery coefficients. Fixed block width is
  also covered there; growing width and arbitrary coefficients are not.
  Forward degree alone requires an additional paid reverse-degree trim.
- Paper 13 supplies high-rate examples with the same broad degree and
  odd-girth conditions. It does not supply a two-token presentation on a
  full balanced grid. The unrestricted finite-field/nonlinear two-token
  capacity question remains open. A proposed colour-swap import must
  check injectivity and grid balance; if all its recovery arcs cross one
  bipartition, its capacity is at most half.

**Full-graph and directed controls (Astra).** In the group case, normalized
helpers generate a subgroup H. Exactly d|H| cells lie in nonbipartite
components of M; for H=G, all cells lie in one such component. This prevents
extending the within-diagonal theorem simply by counting bad components.
More quantitatively, for a w-regular incidence matrix with normalized
second singular value s₂, deleting cells to make the *full induced* M
bipartite costs at least d²(1−s₂)/(2−s₂). It also has a positive linear
fixed-coordinate reveal cost on sufficiently high-rate codes. This is a
written method obstruction, not a capacity bound. The known Paley tournament
on seven vertices has binary dimension four with no mutual pairs, now
Lean-verified along with the all-alphabet upper bound q⁴. Thus an oriented
half-rate lemma is false. Neither control settles full-grid capacity.
