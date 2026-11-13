# Whole-row shape after an additional cheap cut

Hans Brende, Claude Fable 5.2 and GPT-6 Astra, 13 November 2026.

**Fronts D4/D9 and D1.** Fable proposed the window argument in C20; Astra's
audit corrected its conventions, sharpened the finite bound, and added the
raw-boundary transfer below. The window/row-spread theorem and the machine/crux
consequences have reviewed **written proofs**, not complete Lean proofs.
[StatementsRowSpread.lean](../StatementsRowSpread.lean) states the geometric
target as a proposition without asserting it; its elementary code and cut
adapters are Lean-verified. The whole-row capacity bounds remain conjectural.

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
interval and exact last-window-label overwrite. Enumerating its fixed
integer span as a list and transporting the predecessor-label count
into the finite-list formulation remain unformalized.

This is interval bookkeeping related to the block computation graphs in
[Hopcroft, Paul and Valiant, *On Time Versus Space*, JACM 24(2), 332–337
(1977), §2, p. 333](https://www.csd.uwo.ca/~mmorenom/CS433-CS9624/Resources/p332-hopcroft.pdf).
Their construction first makes a simulation block-respecting; Lemma 1 works
on the given walk. We found no statement of the following same-trace
extension in Papers 5, 11 or 14 or their shared Lean dependencies. This is
not an exhaustive novelty claim about the literature.

**Proposition 2 (finite row spread).** Let $d\ge4$, $b\ge1$, $\beta\ge1$,
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

*Proof.* For $k\ge1$, call a window bad if its predecessor-window counts
summed over tapes exceed $M$. There are at most $3kN/M$ bad windows.
Reveal the preceding state step of each bad window and every external work
predecessor of every step in it. Window zero is never bad. At most
$kh+1\le(k+1)h$ steps are charged per bad window. With (1),

$$\beta\,\#(\Gamma'\setminus\Gamma)
\le\frac{3\varepsilon}{4C}Nh
\le\frac{3\varepsilon}{4}(L+1+h/C)
\le\frac{63}{64}\varepsilon L \quad(d\ge4). \tag{3}$$

The last inequality uses $1/L\le1/d^2$ and $h/(CL)\le1/d$. The initial cut
may be arbitrarily expensive; only new steps are charged. If $k=0$, there
are no bad windows and no added cuts; below $M=0$ and only state edges remain.

A free path cannot leave a bad window backwards: every external target has
been revealed, even when the path's root is revealed. A good window has at
most $M$ work predecessor windows plus the preceding window. Including a
stay choice, at most $(M+2)^D$ windows are reachable in at most $D$ edge
transitions. The input head scans at most $h$ consecutive positions in one
window, hence meets at most **two** physical input rows; out-of-input
positions contribute no bits.

For each output row take the interval from its first to its last append,
not just its possibly sparse append set. These intervals are disjoint and
ordered. A row interval meeting more than $M'+1$ windows contains at least
$M'$ complete windows between its endpoint windows. There are therefore at
most

$$N/M'\le\frac{\varepsilon}{2}(d+1/h+1/C)\le\varepsilon d$$

such rows. Every other row uses at most $M'+1$ starting windows. Union their
reachable windows and the two input rows per window to obtain (2).
Enlarging a cut cannot increase free-path depth. ∎

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
$\varepsilon L$. If $\delta(w)>3\varepsilon$, there is no correct oblivious
linear-time transposer with those fixed resources at all sufficiently large
dimensions. The original sufficient condition $\delta(w)>4\varepsilon$
leaves additional asymptotic slack.

*Proof.* The original genie and Proposition 2 cost at most $2\varepsilon L$
bits together. Paper 14's `exists_indexCode` holds for **any** revealed set,
so a largest actual value fibre has at least $2^{(1-2\varepsilon)L}$ inputs.
Output row $r$ demands input column $r$. The new fibre is a whole-row code
outside at most $\varepsilon d$ columns. Freezing these and applying (4)
bounds its size by $2^{(1-\delta(w)+\eta+\varepsilon)L}$. Choose
$0<\eta<\delta(w)-3\varepsilon$. ∎

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
By (5), freezing at most $\eta L$ raw bits transfers each resulting code
fibre to the new cone relation. Freeze the at most $\eta d$ exceptional
columns too, at cost at most $\eta L$. Apply the whole-row bound with slack
$\eta$. The original code has rate at most $1-\delta+3\eta$. For an index
code of $m$ bits its largest fibre has at least $2^{L-m}$ elements, so
$m\ge(\delta-3\eta)L$. Let $\eta$ tend to zero in the crux quantifiers.
Depth, cut price, window and slack are fixed before dimension grows.
Neither correctness nor cheapness of the initial $\Gamma$ is used. ∎

The direct machine route is quantitatively cheaper: it pays actual step
values rather than the factor $B_D$. Do not read (5) as a bound uniform
when $D$ grows with dimension.

## 5. Formal status and reproduction

`StatementsRowSpread.lean` reuses `MotionDepthCodes.IsStorageCode` and
`BoundedStackDepth.coneSystem`. It defines the geometric formalization target
and nonlinear capacity conjectures and proves elementary adapters including
exceptional columns and (5). It does **not** assert the geometric theorem
as a Lean theorem or prove any whole-row capacity conjecture. No new axioms
or proof placeholders are used.

Check from Paper 15's existing package, which supplies both dependencies:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env lean ../../lean-backlog/StatementsRowSpread.lean
lake env lean ../../lean-backlog/WindowAmortization.lean
lake env lean ../../lean-backlog/WindowPages.lean
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
remain pending; the complete extraction is not yet Lean-verified.

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
