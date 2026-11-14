# Whole-row shape after an additional cheap cut

Hans Brende, Claude Fable 5.2 and GPT-6 Astra, 13 November 2026.

**Fronts D4/D9 and D1.** Fable proposed the window argument in C20; Astra's
audit corrected its conventions, sharpened the finite bound, and added the
raw-boundary transfer below. The window/row-spread theorem is now completely
**Lean-verified**, including the native geometry and all counting adapters.
[WindowSpread.lean](../WindowSpread.lean) proves the exact target in
[StatementsRowSpread.lean](../StatementsRowSpread.lean) as a corollary of a
stronger prefix theorem. [ConeCodeTransfer.lean](../ConeCodeTransfer.lean) and
[RowSpreadCrux.lean](../RowSpreadCrux.lean) now complete the conditional
coding transfer and machine exclusion. The whole-row capacity bounds remain
conjectural.

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

**Lean-verified:** `wholeRow_window_bound_excludes` in
[RowSpreadCrux.lean](../RowSpreadCrux.lean). It needs (4) only along the
canonical alphabets, at this single explicit window.

*Outline of the formal proof.* The original genie and Proposition 2 cost at most $(127/64)\varepsilon L$
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
half rate. This proves an implication, not either capacity conjecture.

**Lean-verified:** `uniformWholeRowRateCanonicalBits_crux` and
`uniformWholeRowRate_cruxOn` in [RowSpreadCrux.lean](../RowSpreadCrux.lean).
The former gives the literal `BoundedStackDepth.Crux`; the latter gives
`CruxOn` uniformly over all positive bit widths. The shared proof also
allows any prescribed family of positive widths, and does not need
$\delta>0$ until the exclusion corollary.

*Counting argument and outline of the formal proof.* Start with any binary storage code on an original depth-$D$ native
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

The exported finite theorem is stated directly for an index code with
$m$ message bits. For $d\ge4$, $b\ge1$ and any trace satisfying the stated
time and depth bounds with at least $L$ appends, it proves

$$L\le m+\frac{105}{64}\varepsilon L+ba,$$

assuming a whole-row cardinal bound $|C|\le(2^b)^a$ at the explicit
window priced by $B_D$. It sums over common message/raw-bit fibres,
rather than selecting a largest one. The generic fibre adapter needs no
positivity assumption on $d,b$ or $a$. The preceding all-storage-code
calculation is the written explanation of the same counting argument;
the exported native endpoints are index-code bounds and `Crux` statements.

The direct machine route is quantitatively cheaper: it pays actual step
values rather than the factor $B_D$. Do not read (5) as a bound uniform
when $D$ grows with dimension.

## 5. Formal status and reproduction

`StatementsRowSpread.lean` reuses `MotionDepthCodes.IsStorageCode` and
`BoundedStackDepth.coneSystem`. It defines the geometric target and nonlinear
capacity conjectures and proves elementary adapters including exceptional
columns and (5). `WindowSpread.lean` proves the geometric target completely.
`ConeCodeTransfer.lean` reuses Paper 15's entry addressing and the existing
exceptional-column lemma to count arbitrary encoder/raw-bit fibres.
`RowSpreadCrux.lean` proves Corollaries 3 and 4 and combines the latter
with Paper 14's `crux_excludes`. No whole-row capacity conjecture or
unconditional machine exclusion is proved. All formalized endpoints use
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

## 13. Odd sector walks are square roots: bounded coupling in a group (Fable, 13 November 2026)

Status: the results below now have **reviewed written proofs**. Astra's
strengthening replaces the structure-theorem sketch for bounded coupling
by an elementary reduction to the previous mutual-diagonal theorem. The
[full proof and finite controls](bounded-sector-coupling.md) also contain
an independent near-abelian theorem. Only the elementary group identities
are Lean-verified; the capacity results are not.

**Setting.** Let |G|=d, ρ(c)=cT, 1≤|T|≤w. A cell (r,c) has sector
r⁻¹c. Fix a recovery support valid throughout the code, using only
mutually available helpers. Each connected component of its undirected
support is assumed to meet at most m sectors. Components may split sectors
and overlap in their sector labels; a partition of whole sectors is a
special case. Nonlinear recovery and arbitrary correlations are allowed.

**Proposition 13.1 (odd sector walks).** A mutual step sends g to
t⁻¹g⁻¹u⁻¹, t,u∈T. The sector g has an odd closed walk of length 2j+1
exactly when gxg=y for some x∈T(T⁻¹T)^j and y∈[T(T⁻¹T)^j]⁻¹,
equivalently (gx)²=yx. If R₂ is the largest square-root multiplicity in G,
at most w^{2(2j+1)}R₂ sectors qualify.

*Proof.* After 2j steps the left and right factors of g range independently
over (T⁻¹T)^j and (TT⁻¹)^j. Closing the last step gives the stated
sandwich equation. The map g↦gx is bijective. The algebraic identities,
including the actual cell/sector move, are in
[SectorWalks.lean](../SectorWalks.lean). ∎

**Corollary 13.2 (sharper finite bound).** Put
X=T(T⁻¹T)^{m−1}, s=|X| and E={g:gXg∩X⁻¹≠∅}. Then

  log_q|C| ≤ (d²+d|E|)/2,
  |E| ≤ min(d, s(s+1)R₂/2),   s≤w^{2m−1}.

In particular the excess is at most (d/2)min(d,w^{4m−2}R₂), improving
the original w^{6m}R₂d estimate. A nonbipartite graph on at most m
vertices has an odd closed walk through each vertex of length at most
2m−1; pad to that single length. The square-root equations can be indexed
by unordered pairs from X. Projection onto recovery components gives the
capacity bound, without product independence.

Odd-order groups have R₂=1, giving O_{w,m}(d) excess. The elementary identity

  Σ_z |{a:a²=z}|² = d·k_real(G) ≤ d·k(G)

replaces Frobenius–Schur: write equal-square pairs as b=ah and count
conjugators a⁻¹ha=h⁻¹, one contribution d per real conjugacy class.
If k(G)≤d^{1−η}, the bound gives a vanishing excess for
m≤(η/8−γ)log_w d, with fixed w>1 and 0<γ<η/8. The strict margin matters.

**Theorem 13.3 (all groups, strengthened).** At fixed w,m, uniformly over
all finite groups, growing finite alphabets and nonlinear codes as above,

  log_q|C| ≤ d²/2 + O_{w,m}(d²/log d).

More generally, if B_m cells lie in recovery components meeting more than
m sectors, the upper bound is (d²+B_m)/2+O_{w,m}(d²/log d). A fixed rate
gain ε therefore requires (2ε−o(1))d² cells in such components for every
fixed m. This is a recovery-support requirement, not a time lower bound.

*Proof outline; complete written proof in the linked note.* Complete each
small nonbipartite recovery component to the available mutual relation on
its ≤m sector labels. Retain parallel sector edges and their row
multipliers. A spanning tree supplies fundamental closed walks of length
≤2m−1 whose multiplier/parity pairs generate all closed-walk pairs.
Nonbipartiteness supplies an odd generator. Multiplying each even generator
by that odd one yields an inverse-closed odd generating set with lengths
≤4m−3. Its multipliers lie in gY for the fixed word set
Y=T(T⁻¹T)^{2m−2}. An odd identity word makes the mutual Cayley graph of
gY nonbipartite. The prior general-group theorem bounds these g by
O_{w,m}(d/log d), independently of the component or partition. Projection
finishes the argument. ∎

A shared transcript with M possible values adds log_qM; recovery support
may depend on that paid transcript; the mixed bound uses a common upper
bound on B_m across fibres. An uncharged codeword-dependent
partition is not covered. The all-group theorem no longer uses Neumann.
Separately, the original near-abelian route works and excludes positive
limiting excess for **every whole-row code** whenever commuting probability
stays bounded below: a bounded-by-abelian-by-bounded structure yields
uniform polynomial incidence growth, ball peeling yields row separators,
and the existing row-separator bound applies. The needed group theorem
was verified in Eberhard's 2015 reproof, not the inaccessible Neumann
original. Details and precise references are in the linked note.

**Remark 13.4 (trace family).** On n=2^a−1 vertices with helper shifts
{1,2,4,…,2^{a−1}}, the fitting polynomial 1+Tr(x) has exactly 2^{a−1}
simple nonzero roots, proving binary kernel dimension 2^{a−1} for every a.
The relation is oriented for a≥3; a=1 has a loop and a=2 is bidirected.
The window grows and the excess is half a symbol, so this does not give
a fixed-window positive-density construction.

**Proposition 13.5 (exact good-sector capacity, directed).** In G=F_p^k,
put V=span(T−T), r=dim V≤w−1. Outside −t₀+V every diagonal has capacity
exactly q^{d/p} over every finite alphabet: a functional maps its helpers
to a directed p-cycle, and constants on the cycles of any one helper
attain the resulting upper bound. Thus arbitrary correlated own-sector
codes satisfy

  log_q|C| ≤ d²/p + (1−1/p)p^r d.

The O(d) exceptional term requires p,w fixed; for varying p it must be
kept explicit.

**Finite-test correction.** On the proposed canonical 7:3 and 13:3 hosts,
six sectors have odd return length one and all others have length three.
Covariant mutual-only codes using at most two sectors per block already
carry 259 symbols in 441 cells and 832 symbols in 1521 cells, over every finite alphabet, by combining
free loops, triangle codes and a certified sector matching. These exceed
the pairing-plus-loops counts 252/819 but demonstrate no unbounded-coupling mechanism.
Both host families also have an abelian normal subgroup of index three,
so their asymptotic full-code capacities are covered by the near-abelian
theorem. The uninformative solver comparison was replaced by these exact
controls; none is an optimized capacity claim.

**Surviving target.** Mutual recovery must use unboundedly many sector
labels on a positive fraction of cells in any fixed positive-rate gain,
outside the uniform near-abelian regime. A logarithmic coupling requirement
needs the separate class-count hypothesis above. Expansion is a candidate
family, not a necessary property proved here. There is still no common
whole-row deficit or native transposer exclusion from these results.

## 14. Two-sided symmetric decoders are at one half; the family for the large-component case (Fable, 13 November 2026)

**Reviewed and strengthened by Astra, 14 November.** Full written proofs,
field qualifications and exact certificates are in
[symmetry and locality barriers](symmetry-and-locality.md). These results
are not Lean-formalized. Front D1; no new native exclusion.

**14.1 (swapped blocks).** Over every field, if a linear decoder exchanges
$E_i\otimes E_j$ and $E_j\otimes E_i$, then

$$\dim\operatorname{Fix}K\le d^2/2+\tfrac12\sum_i(\dim E_i)^2.$$

A given code is contained in the fixed space, not necessarily equal to it.
The original paired-block proof stands.

**14.2 (cubic strengthening).** Suppose $H\le G$, $|G|=d$, $|H|=h$,
$\operatorname{char}F\nmid h$, and the coefficients obey

$$k(c,r;i,x)=k(h_2c,h_1r;h_1i,h_2x).$$

If $n_\sigma$ are the irreducible degrees over a splitting extension, then

$$\dim\operatorname{Fix}K
 \le d^2/2+\frac{d^2}{2h^2}\sum_\sigma n_\sigma^3
 \le d^2/2+\frac{d^2}{2\sqrt h}.$$

The cubic expression replaces the original fourth moment in good
characteristic. The uniform $d^2/(2\sqrt h)$ error holds over **every
field**, including characteristics dividing $h$: the commutant has
dimension $d^2/h$, and an invariant composition flag gives the general
bound $(d^2+d\sqrt{\dim\mathcal A})/2$ when
$\tau K\in\mathcal A\otimes\mathcal A$.
On an equal-type block in the semisimple case,
$K=\operatorname{flip}_{V_\sigma}\otimes D_\sigma$; its exact fixed
dimension is $n_\sigma\dim\ker(I-D_\sigma)+
\binom{n_\sigma}{2}\dim\ker(I-D_\sigma^2)$. This strengthens the diagonal
block estimate and requires no characteristic-two eigenspace split.
For $H=G$ the rules are the constant templates
$X[c,r]=\sum_{t\in T,y\in G}\phi(t,y)X[rt,cy]$, with unrestricted helper
columns. Growing twisted symmetry suffices over every field, without
quasirandomness. The cubic expression is sharp in the split semisimple
case among unrestricted twisted intertwiners, not asserted attainable
with a specified sparse helper set.

**14.3 (local rules, repaired).** The earlier assertion of equality with a
constant template outside $O(d)$ output cells was false: the radius-one
rule $K(X)_{c,r}=X_{r,r}$ is a counterexample. Under the precise anonymous,
coloured, edge-labelled **four-port** locality definition in §3 of the
linked note, the stronger useful replacement is

$$K=K_0+L+E,\qquad \operatorname{rank}L\le d,\qquad
 \operatorname{rank}E\le d\sum_{j=0}^{4R+3}w^j,$$

where $K_0$ is constant-template. No girth or coefficient-size hypothesis
is needed for this normal form. The all-field symmetry bound gives rate
$1/2+1/(2\sqrt d)+O_{w,R}(1/d)$ on every growing finite-group family,
not only SL₂.

**14.4 (amenable sources, all alphabets).** A fixed marked finitely
generated amenable source group gives uniformly hyperfinite quotient
Cayley graphs. The row-separator bound therefore gives $1/2+o(1)$ for
**every** whole-row code, nonlinear codes included and uniformly over
finite alphabets. The source must preserve the chosen generators.
The proof uses Elek–Szabó Proposition 4.1 and marked compactness;
Schramm's theorem alone does not supply the amenability implication.
Fixed generator budget and bounded derived length satisfy the hypothesis.
A positive limiting gain requires failure of hyperfiniteness, not
necessarily expansion.

**14.5 (exact universal zero-corner limit).** For any allowed support
relation $R$, over every field, the maximum rank of an idempotent $P$
with $PKP=0$ for **every** freely supported $K$ equals the independence
number of $R$ (loops excluded). Indeed, for the nonzero-row set $U$ and
nonzero-column set $V$ of $P$, $U\cap V$ is independent and
$P=P I_{U\cap V}P$. Coordinate independent-set projections attain the bound.
For the regular mutual graph this gives
$\operatorname{rank}P\le d^2s_2/(1+s_2)$.
It concerns a universal free-coefficient certificate, not cancellations
in one decoder. The earlier bipartizing-deletion bound is a different
optimization.

**The family and the surviving target.** Let
$G_p=\mathrm{SL}_2(\mathbb F_p)$, $p\ge5$ prime, and
$T=\{I,A,B\}$ for the upper and lower unipotents with off-diagonal entry 2.
The incidence family expands and has girth $\Omega(\log p)$.
Its ordinary degrees and all requested exact $E_1,E_2$ counts are in §5
of the linked note. The group has centre $\{\pm I\}$; it is not simple.

The cubic character formula needs good characteristic; the uniform
commutant bound does not. Actual constant or growing-subgroup-twisted
rules are therefore at half plus $o(1)$ over every field. For Borel
symmetry on SL₂, the older $C_p$ or $C_{p-1}$ argument already sufficed. A profile of
$\mathcal B(c^{-1}r)\mathcal B$ is not that symmetry, but is excluded
separately: it differs from a constant template on only $d^2/(p+1)$ cells.

A split/nonsplit discriminant profile has two positive-density pieces
and survives these particular exclusions. Its bounded complex
**mutual-only** version is already excluded by Paper 4, Theorem A and
the gauge extension. A remaining bounded target is the finite-field
version, with one shared decoder and dimension counted on the full array.
No finite example above half, or above the applicable architecture
baselines, has been found in this audit. No optimizer was run.

## 15. Reformulations nearest the wall: presentability and the dual form (Fable, 13 November 2026)

Status: **reformulations with one-line proofs**, no new bound. They state the
wall (front D1) with no restriction to groups, mutual helpers or symmetry.

**15.1 (presentable recovery digraphs).** A recovery digraph H on d² vertices
is the recovery relation of a whole-row decoder at window w exactly when its
vertices can be labelled bijectively by pairs (tail, head) ∈ [d]² so that the
bipartite graph {(head(x), tail(y)) : x → y in H} has degree at most w at
every head. In words: the vertices fall into d columns and d rows, one vertex
in each row-column intersection, and all arcs leaving a column end in at most
w rows. Arcs are otherwise free: the helper's column is unconstrained. So the
universal host is the line digraph of the complete digraph with loops,
fattened by ρ; for ρ the identity it is that line digraph itself.

For a presentable H carrying a code of rate 1 − η, the finite order bound is

$$|A|\ge\sum_r\frac{d-|\rho(r)|}{|\rho(r)|+1}
 \ge\frac{d(d-w)}{w+1},\qquad
 w\ge\frac{1-\eta}{\eta+1/d}. \tag{15.1}$$

Indeed, choose a random row order and take cells $(c,r)$ for which
$c\notin\rho(r)$ precedes every row of $\rho(r)$. Every helper arc inside
this set strictly increases the row order, so the set is acyclic. Its
expected size is the displayed sum. Projection to its complement is
injective on any storage code, yielding (15.1). The earlier finite claim
$|A|\ge d^2/(w+1)$ omitted loops: at $w=1$, $\rho=\mathrm{id}$, the
symmetric code has dimension $d(d+1)/2$. Only asymptotically does the
necessary condition become **$w\ge1/\eta-1$**.

For fixed window and a fixed positive asymptotic excess above half, the
row-graph family cannot be hyperfinite. The small-component obstruction
and the counts of Proposition 8.1 also apply, with their stated scopes.
For $d^2b$ coordinates, replace the bijection by balanced cells of size
$b$; (15.1) is unchanged after normalization by the total size.

**15.2 (the dual form, linear codes).** A linear whole-row code of dimension
(1 − η)d² exists for ρ exactly when there is a subspace U ⊆ M_d(F) of
dimension ηd² that contains, for every column r and every vector α, a matrix
supported on column r and the rows ρ(r) whose column r agrees with α outside
ρ(r). (U is the dual code; the matrix is the check of the cells of column r
with weights α.) Pairing uses $U=\operatorname{span}\{E_{ij}-E_{ji}:i<j\}$,
with zero diagonal also in characteristic two. The reverse relation has the
same maximal linear dimension: if $K$ fits $\rho$, then $\tau K^T\tau$
fits $\rho^{-1}$ and $\operatorname{rank}(I-\tau K^T\tau)=
\operatorname{rank}(I-K)$. Here $\tau$ exchanges
the two cell indices. This is not an assertion about nonlinear capacity.

*The wall for linear codes, in one line:* a lower bound dim U ≥ δd² with δ
independent of w. The rectangle bound gives max_J |J|(d − |ρ(J)|), about
d²/(4w) on expanding relations.

**15.3 (the question this isolates).** For each fixed odd $m$, the fifteenth
paper's full field-linear majority kernels have rate at least
$1-e^{-\lambda m}$ on a growing tower, at degree bounded in $m$.
Its binary syndrome fibres have guaranteed rate at least
$1-(\log_2 q)e^{-\lambda m}$, where $q$ is the fixed seed field size.
The necessary asymptotic window is therefore at least $e^{\lambda m}-1$
for a field code at the first rate, or $e^{\lambda m}/\log_2q-1$ for
a binary code at the second. Neither order bound precludes a window
depending only on $m$.

The target must also specify the grid dimensions and lanes. One sufficient
positive result would present each full field kernel, padded by fixed zero
coordinates to the next square, on a scalar grid at a window $w(m)$
independent of tower level. The [grid note, §6](grid-labellings-and-amplified-codes.md#6-the-growing-tower-support-and-intrinsic-gates)
gives the binary-fibre and canonical-lane adapter. This would prove
$\sup_w R(w)=1$ and refute a **common positive deficit**. It would not
exclude every window-dependent deficit or decide native tape realization.
A negative answer for this tower alone would not settle all whole-row
codes; its value would depend on how far the obstruction generalizes.

Bounded or slowly growing product blocks are excluded (grid note, §§2,5).
For the growing tower, its displayed support cannot use a column label
that ignores any tensor factor at canonical width. Every decoder of the
full field kernel also fails the natural tensor-cylinder columns (§6).
Arbitrary fully mixed partitions, and alternative binary-fibre decoders,
remain open.

## 16. Presentable relations: normal form and partition-independent gates

Fable's proposal, audited and strengthened by Astra, 14 November 2026.
Status: **reviewed written proofs, not Lean-verified**. Front D1, gap G0.
Sections 16.1, 16.2 and 16.4 allow one-way helpers and nonlinear recovery;
16.3 concerns a symmetric support (or the mutual subrelation of a directed
support). Every assertion is about the specified support, not all possible
decoders of a code using it.

**16.1 (normal form).** A digraph $H$ on $d^2$ vertices is whole-row
presentable at window $w$ exactly when there are column and row maps
$\phi,\psi:V(H)\to[d]$, jointly a bijection onto $[d]^2$, and a bipartite
row helper graph $B$ of forward degree at most $w$, such that

$$u\to v\text{ in }H\quad\Longrightarrow\quad
       (\psi(v),\phi(u))\in B.$$

This is the definition written on the vertices of $H$. If $H$ is symmetric,
applying the condition in both directions places it as a spanning subgraph
of the two-token graph of $B$ (§12). For $d^2b$ vertices, replace the bijection
by exactly $b$ vertices in each row-column cell. Projection of walks to
cells still gives walks in the two-token graph, and cell-count bounds
acquire a factor $b$. This does not bound the degree of the actual support
unless a separate degree hypothesis is imposed.

**16.2 (shortening and its limitation).** Fix the entries outside a set
$S$. The resulting fibre, restricted to $S$, is a storage code on $H[S]$:
all removed helper arguments are constants. Empty fibres cause no exception.
Over an alphabet of size $q$, a one-column fibre has at most $q^{wb}$
words, a fibre on columns $J$ has at most $q^{b|\rho(J)||J|}$ words, and a
fibre on arbitrary $S$ has at most $q^{|S|-a(H[S])}$ words, where $a$ is
the maximum size of an induced acyclic set. The first two follow by
projection to the helper rows inside the retained columns; the last is
acyclic elimination. The field-linear column case is (6) of the
[grid note](grid-labellings-and-amplified-codes.md).

The precise generic-position condition is that projection of a
$K$-dimensional linear code onto $S^c$ has rank
$\min(K,d^2b-|S|)$. Rank-nullity then gives shortened dimension
$\max(0,|S|-(d^2b-K))$. On a union of columns this value passes the
shortening gate whenever the rectangle bound holds. This explains why
that gate alone need not detect a mixed partition; it is not a claim
that every mixed partition of the tower has generic shortening.

**16.3 (odd closed walks in every layout).** Suppose the row helper graph
has forward and reverse degrees at most $w,w'$. Let $H$ be a symmetric
support in a balanced grid with $b$ lanes, and write $\mathrm{Bad}_j(H)$
for vertices lying on an odd closed walk of length at most $2j+1$. Then

$$|\mathrm{Bad}_j(H)|\le bd\,w(ww')^j. \tag{16.1}$$

*Proof.* By the two-token identity a bad cell has its row port within
incidence distance $2j+1$ of its column port. Every shorter odd path can
be padded by backtracking to this exact length. There are at most
$w(ww')^j$ such walks from each column, and at most $b$ vertices in each
cell. ∎

A radius-$j$ induced ball is non-bipartite exactly when its root has an
odd closed walk of length at most $2j+1$. A same-parity edge in a breadth-first
layering gives one direction; every vertex of such a closed walk is at
distance at most $j$ from its root, giving the other. Thus (16.1) bounds
non-bipartite balls as well. For fixed $w,w'$ with $ww'>1$, any
$j\le(1-\varepsilon)\log_{ww'}d$ gives a vanishing bad fraction for
each fixed $0<\varepsilon<1$.
When $w=w'=1$, the bound $bd$ holds at every radius.

A forward cap alone does not imply this conclusion for unbounded-degree
supports. For instance, $\rho(0)=\{0\}$ and $\rho(r)=\{0,r\}$ for $r>0$
have $w=2$, but the full mutual graph has a loop within distance one
of every cell. Even after removing loops, every cell is at distance at
most one from the row-zero clique, so all radius-two balls are non-bipartite
for $d\ge3$.

**Forward-only strengthening with bounded actual degree.** Suppose instead
that only the forward window $w$ is bounded, and the actual symmetric
support has maximum degree $\Delta$. For every integer $R\ge0$,

$$\frac{|\mathrm{Bad}_j(H)|}{d^2b}
 \le \frac{w(wR)^j}{d}
       +\frac{w}{R+1}\sum_{i=0}^j\Delta^i. \tag{16.2}$$

*Proof.* Delete the vertices $Z$ in rows whose reverse row-degree exceeds
$R$. There are at most $wd/(R+1)$ such rows, so
$|Z|\le wd^2b/(R+1)$. A bad root with a witnessing walk avoiding $Z$
is counted by (16.1) on the remaining incidence graph, which has reverse
degree at most $R$. If a witnessing walk meets $Z$, its root is within
$H$-distance $j$ of $Z$, using the shorter direction around the closed
walk. At most $|Z|\sum_{i=0}^j\Delta^i$ roots have that property. ∎

For fixed $w,\Delta,j$, taking $R\asymp d^{1/(j+1)}$ gives bad fraction
$O_{w,\Delta,j}(d^{-1/(j+1)})$, uniformly in $b$. There is also an explicit
growing-radius guarantee. Set $K=\max(2,w,\Delta)$ and $R=K^{2j+2}$.
Equation (16.2) gives

$$\frac{|\mathrm{Bad}_j(H)|}{d^2b}
 \le \frac{K^{2j^2+3j+1}}d+K^{-j}. \tag{16.3}$$

In particular $j=\lfloor\sqrt{\log_K d}/3\rfloor$ tends to infinity
with bad fraction tending to zero. This uses the actual degree bound;
it is a square-root-logarithmic radius, not the logarithmic radius
obtained from a bounded reverse window.

**Application to amplification: exact scope.** If a fixed positive share
$\alpha$ of seed vertices have odd closed walks of a fixed bounded length
in the actual mutual support of $A$, and $\gamma_s\ne0$ for some odd
$s$, then at least $\alpha^sN^m$ amplified vertices have such walks.
Choose $s$ active coordinates, pad their walks to a common odd length
by backtracking, and use the exact support formula (4) of the grid note.
Both directions of every used edge survive. At fixed $m$ and bounded
seed degree, (16.2) rules out a bounded-forward-window presentation of
that displayed support in every layout. It does not rule out alternative
recovery rules for the same code.

This gives **no exclusion of Paper 15's actual tower**: its containing
seed graphs already have odd girth tending to infinity. Moreover the
chosen $A$ need not have symmetric support, use every containing edge,
or be connected or of logarithmic diameter. None of these properties may
be inferred from an ambient arithmetic graph. Conditionally, if the
actual mutual seed support is connected, non-bipartite and of diameter
$D_0$, every seed vertex has an odd closed walk of length at most
$2D_0+1$, by breadth-first layering. For an unpadded presentation
$N^m=d^2b$, (16.1) forces $d\le w(ww')^{D_0}$.
At $D_0=O(\log N)$ this is only a requirement
exponential in the fixed amplification order $m$, not a window diverging
with tower level. That diameter premise is not supplied by Paper 15.

**16.4 (spread and concentration).** In every presentation, the distinct
helpers used by one column meet any other column in at most $wb$ vertices.
If reverse row-degree is bounded by $w'$, all tails entering one row lie
in at most $w'$ columns. If the actual support has minimum outdegree
$a\ge1$ and maximum indegree $\Delta$, one column sends at least $adb$
arcs. Each helper receives at most $\Delta$ of them, so they reach at least

$$\left\lceil\frac{ad}{\Delta w}\right\rceil$$

different columns. This is a dense column quotient when $a,\Delta,w$
are fixed. At least **one** helper row receives $adb/w$ arcs, and each
receives at most $\Delta db$. There is no linear lower bound for each
helper row: for $d\ge3$ (indices modulo $d$), the loopless permutation

$$F(c,r)=\begin{cases}(r,c+1),&c\ne0,\\(r+1,1),&c=0\end{cases}$$

has in/outdegree one and both windows two. Column $r$ sends $d-1$ arcs
to row $r$ and only one to row $r+1$. The two cases map bijectively to
vertices outside and inside column one, respectively. Independent lanes
give the same counterexample with $b$ sparse arcs.

These bounds require the stated actual minimum/maximum degrees. A global
rank bound alone does not give minimum outdegree one at every vertex of
the majority support. The first intersection bound, even when combined
with balanced column sizes, is not enough to test the tower: [grid note,
§7](grid-labellings-and-amplified-codes.md#7-why-the-intersection-test-cannot-decide-mixed-layouts)
shows that every bounded-degree loopless support passes it for some
columns at canonical width. Finding compatible rows is a separate obligation.

**Remark (the dual support-count attempt).** Ordering columns in the dual
form of §15.2 and counting checks not already supported in earlier columns
and their helper rows reproduces the order certificate
$\sum_\ell(d-w-|\rho(r_1,\ldots,r_\ell)|)_+$. This records the outcome
of that particular counting argument, not a limitation on every method
using the dual space.

## 17. Swap lifts and the limit of fixed-radius statistics

Fable's proposal, with Astra's proof and scope audit, 14 November 2026.
Status: **written proof; not Lean-verified**. Front D1, gap G0.
One-way helpers are allowed. This section concerns presentation of a
specified support; it supplies no high-rate code.

**Swap lifts.** Let B be any simple Δ-regular bipartite graph on d row
ports and d column ports. Constant forward and reverse degrees on equal
side sizes must agree, since dw = dw′. There are b ≥ 1 vertices in each
cell, L = d²b. For each edge (i, r), independently choose a uniform
bijection from the db vertices of column r to the db vertices of row i.
Its arcs point from a vertex to its helper. The resulting graph has
in- and outdegree Δ and a presentation of window Δ. At b = 1 this is
the rule (c, r) → (i, π_{r,i}(c)). No girth or expansion assumption on B
is made; even disjoint small complete bipartite components are allowed.

**Proposition 17.1 (local limit, including lanes).** Fix Δ and t. Put

  Q = 2Δ Σ_{h=0}^t (2Δ)^h.

For db > Q, any specified root has probability at most
Q(Q+1)/(db−Q) of failing to have the radius-t ball of the directed tree
with Δ incoming and Δ outgoing arcs at every vertex. Distance here is
undirected graph distance, with arc orientations retained. Consequently,
with probability tending to one, all but o(L) roots have this ball as
d → ∞, uniformly in b ≥ 1 and B.

*Proof.* Explore all incoming and outgoing stubs at vertices at distance
at most t, including the boundary; at most Q stubs are queried. Store
each revealed matching pair and its graph edge. A query of an already
known pair adds nothing. For a genuinely fresh forward or inverse query,
the remaining bijection is conditionally uniform on at least db−Q
unused coordinates. At most Q+1 choices hit an already discovered vertex.
This deferred-exposure statement remains true for adaptive queries:
the history fixes only the matching pairs already revealed.

Every first loop, opposite-arc pair or cycle is created by a fresh edge
hitting a discovered vertex. A union bound gives the claimed probability.
Querying boundary stubs detects extra edges inside the induced ball.
The expected number of bad roots is O_{Δ,t}(d), so their fraction tends
to zero in probability by Markov's inequality. ∎

Both comparison families below can be loopless. For each edge matching
there are b forbidden self-pairs, each with probability 1/(db). Its
probability of avoiding all of them is at least 1−1/d. Independence gives
a full loop-free probability at least (1−1/d)^{dΔ} ≥ 4^{−Δ} for d ≥ 2.
Conditioning on this event preserves the local-limit conclusion.

**Corollary (same limit, different presentability).** For fixed Δ ≥ 3,
there are loopless families of window Δ and loopless families requiring
window greater than d^{1−2/Δ−ε}, for any fixed 0 < ε < 1−2/Δ, with the
same limiting unmarked fixed-radius neighbourhood distributions. This
holds also at canonical entry width.

*Proof.* Compare the conditioned lifts with the exact model of
[grid §7](grid-labellings-and-amplified-codes.md#7-why-the-intersection-test-cannot-decide-mixed-layouts):
Δ independent uniform derangements on L vertices, with duplicate arcs
ignored. That model is not a uniform simple regular digraph. Before
conditioning, the permutation exploration has collision probability at
most Q(Q+1)/(L−Q). The probability that all Δ permutations are
derangements is at least 3^{−Δ}, so conditioning preserves convergence
to the same directed tree. Ignoring duplicate arcs changes only bad
neighbourhoods. Equation (9) of the grid note gives the claimed failure
of presentation with probability tending to one. Intersect these events
for any finite collection of radii, then choose a sequence by a diagonal
argument. ∎

**Scope.** The limiting, unmarked, fixed-radius distribution does not
determine presentability. Exact finite histograms, growing-radius tests,
global girth, and distances involving an additional partner marking are
not decided by this corollary. In particular it proves neither that the
Paper 13/15 high-rate supports have the same limit nor that local
information cannot contribute to a capacity proof. No high-rate code is
constructed on either comparison family. Global arguments invariant
under relabelling remain possible: the counting proof itself quantifies
over every partition. The earlier claims excluding all local tests or
all partition-free proofs were too strong.

**17.2 (the host, linear form).** Fix ρ and vectorize X by columns:
x_r(c) = X[c,r], y_i(j) = X[i,j]. The swap τ maps stacked columns to
stacked rows. A scalar-linear code C has whole-row recovery precisely
when some family of d × d matrices Φ_{r,i} satisfies

  x_r = Σ_{i∈ρ(r)} Φ_{r,i} y_i  for every X ∈ C and every r.

Thus C is **contained in** ker(I−Φτ), where
Φ = Σ_{(i,r)∈B} E_{r,i} ⊗ Φ_{r,i}. Recovery that is initially nonlinear
on a linear code still factors linearly through the helper projection;
extend that map from its image to obtain Φ. Conversely the full kernel
is a code, so the maximum scalar-linear dimension is exactly
max_Φ dim ker(I−Φτ). No coefficient bound is imposed.

For b scalar lanes the same statement uses db × db blocks and τ swaps
the two matrix indices while preserving the lane. Scalar linearity over
an extension field does not cover every binary-linear code on b-bit
entries. Bounded actual support degree makes these blocks sparse;
one permutation block per edge is a further restriction. The
[host audit](whole-row-host-audit.md) records the precise decomposition,
its limitation, and the finite benchmarks for this unrestricted host.

## 18. Signed row synergy and recovery budgets

Fable's proposal, audited and extended by Astra, 14 November 2026.
Status: **written proofs, not Lean-verified**; the candidate common-deficit
and strong-synergy bounds in 18.5 remain conjectural. Front D1. The entropy arguments allow nonlinear recovery and
any distribution supported on a nonempty code. Uniformity is needed only
for the cardinality and linear rank interpretations and their finite
benchmarks, not for the entropy inequalities themselves.

Use d rows, b scalar coordinates per entry, and a scalar alphabet of size
q ≥ 2. Entropies are in base q, N = d²b, Y_c is row c, and H = H(X).
For a fixed row order, write <c and >c for the preceding and following
rows. Put A = Σ_c H(Y_c), R = Σ_c H(Y_c | rest), and

  Syn_c = I(Y_c; rest) − I(Y_c; Y_{<c}) − I(Y_c; Y_{>c}),
  S = Σ_c Syn_c.

**18.1 (identity and terminology).** For every order,

  2H = A + R + S.

*Proof.* Add the entropy chain rules in the two orders. For each row,
H(Y_c | Y_{<c}) + H(Y_c | Y_{>c})
= H(Y_c) + H(Y_c | rest) + Syn_c. ∎

Thus S is order-independent. It is a signed net quantity, not a
nonnegative attribution of information to cells. In standard terminology,
S = DTC − TC is the **negative O-information** of the rows, where
TC = A−H and DTC = H−R. This is the quantity of
[Rosas, Mediano, Gastpar and Jensen, *Physical Review E* 100, 032305
(2019), Definition 1](https://arxiv.org/pdf/1902.11239), with the sign
reversed; [published version](https://doi.org/10.1103/PhysRevE.100.032305).
The identity and entropy invariant are not new.

All asymptotic bounds on S below are upper bounds, equivalently bounds
on max(S,0). Large negative values are possible even at window one:
if all rows repeat one uniform length-db vector, H=db, A=N, R=0 and
S=2db−N for d ≥ 2.

**18.2 (the two slack terms).** Let L be b times the number of cells
(c,r) with c ∈ ρ(r). Whole-row recovery gives R ≤ L ≤ wdb: after all
other rows are specified, only these loop coordinates can remain free.
Since A ≤ N, the exact relation is

  2H = N + L + S − (N−A) − (L−R).                         (18a)

Both subtracted terms are nonnegative. Consequently H ≤ (N+L+S)/2,
but equality requires both full row marginals and saturation of the
residual loop allowance. The earlier unconditional description of the
excess beyond the loop bound as S/2 omitted these slacks.

For a row order, partition each row's scalar coordinates into those
recoverable wholly from earlier rows, those recoverable wholly from
later rows, and an exceptional set E_c. Break ties arbitrarily. The
first two tuples are functions both of Y_c and of the respective side;
therefore the corresponding mutual informations dominate their entropies.
Subadditivity then gives

  Syn_c + H(Y_c | rest) ≤ |E_c|.                         (18b)

Taking loops and helper sets straddling the row as exceptions recovers
the symmetrized order estimate. It is a budget inequality, not a claim
that only split cells have synergy. For example, put a uniform sum-zero
word of length d ≥ 2 on the diagonal and fix every other cell to zero, with
ρ(r) = {r}. Then H=d−1, A=d, R=0, S=d−2, although no helper set is split.
The contribution comes from correlated loop entries.

**18.3 (nonlinear single-row recovery, with exceptions).** Suppose all
but J scalar coordinates are recoverable from a single other row;
the choice of row may depend on the coordinate but is fixed across codewords.
Let Z be the tuple of those J exceptional coordinates. Then

  S+R = 2H−A ≤ H(Z) ≤ J,       H ≤ (N+H(Z))/2.           (18c)

*Proof.* Condition on Z. For each row order, put each nonexceptional
coordinate in the first or second tuple of (18b) according to its helper
row. Exceptional coordinates are now constants. Summing gives
2H(X|Z) ≤ Σ_c H(Y_c|Z). Unconditioning gives
2H−A ≤ 2H(Z)−Σ_c I(Y_c;Z). The revealed part Z_c of row c is a
function of both Y_c and Z, so Σ_c I(Y_c;Z) ≥ Σ_c H(Z_c) ≥ H(Z).
This proves (18c), without linearity or single-entry helpers. ∎

In particular, if all nonloop coordinates have single-other-row
recovery, S+R is at most the joint entropy of the loop coordinates,
hence at most L. More generally, if J_joint additional nonloop
coordinates need joint recovery, S+R ≤ L+J_joint. A rate at least
1/2+η therefore forces J_joint ≥ 2ηN−L. This is a necessary extensive
joint-recovery requirement when w is fixed and η > 0; a finite O(d)
excess does not imply positive density.

For the uniform law on a scalar linear code, let U_c be the span of its row-c coordinate
functionals in its dual, U_< = Σ_{i<c} U_i, and U_> = Σ_{i>c} U_i.
Then

  Syn_c = dim(U_c ∩ (U_<+U_>)) − dim(U_c ∩ U_<) − dim(U_c ∩ U_>).

Equivalently it is the nonnegative distributivity defect

  dim(U_c ∩ (U_<+U_>)) − dim((U_c ∩ U_<)+(U_c ∩ U_>))

minus dim(U_c ∩ U_< ∩ U_>). If all row spaces are coordinate
subspaces in a common basis, this defect vanishes, so S ≤ 0 and the
half-plus-loop bound follows. Positive total S forces a positive total
defect, but the signed expression also subtracts redundant information.
For vector-linear codes use all scalar coordinate functionals; no
extension-field linearity is assumed.

**18.4 (exact benchmarks, including far contributions).** Independent
sum-zero gadgets of m ≥ 2 cells in distinct rows contribute m−2 to S;
independence is what permits addition across gadgets. Each gadget has
entropy m−1, row-entropy sum m and zero residual entropy. Free loop
coordinates and pairs contribute zero. Thus the Fano scalar construction (the scalar-linear optimum over GF(2) and GF(3))
has H=39, A=49, R=21, S=8, and the basis host at d=8 has A=64, R=24, S=4.
These saturate (18a)'s coarse entropy estimate, not a universal function
F(w,w′).

The earlier claim that all known synergy is in near cliques is false.
Exact binary computations on the existing codes give:

| Host | d | H | A | R | S |
|---|---:|---:|---:|---:|---:|
| Two basis helpers | 4 | 12 | 16 | 8 | 0 |
| Three basis helpers | 8 | 46 | 64 | 24 | 4 |
| Four basis helpers | 16 | 176 | 256 | 64 | 32 |
| Clebsch helpers | 16 | 210 | 256 | 80 | 84 |

In the last code the independent diagonal factors contribute 80 from
K4 gadgets and **4 from the Clebsch diagonal**. Its 16 active cells
have incidence distance five and their mutual graph is triangle-free.
Thus those four units are not explained by disjoint near-clique gadgets
in the given coordinates. This is a property of explicit independent
factors, not a general decomposition of S into cell contributions.

More generally the [folded-cube code](diagonal-code-calibration.md#2-a-binary-code-on-every-odd-folded-cube)
on d=4^m active diagonal cells, at window 2m+1, has
H=(d+2^m)/2, A=d, R=0 and S=2^m for m ≥ 1. Every active coordinate
is uniform by translation invariance and is determined by its fitting
equation. At m ≥ 2 these cells have distance 2m+1 and a triangle-free
recovery graph. Fixing the other d²−d cells creates exactly that much
row-marginal slack, so this is not a high-rate full-array example.

For the full hypercube product at d=2^k with w ≤ k basis helpers, put

  a(w) = Σ_{odd j≤w} binom(w,j) 2^{−(j+1)/2}.

The existing construction has H=d²/2+d a(w), A=d² and R=wd, hence

  S = d[2a(w)−w]
    = d Σ_{odd j≥3} binom(w,j) 2^{−(j−1)/2}.              (18d)

Terms with j>3 come from far non-clique factors of the full code.
The coefficient grows exponentially in w but is constant at fixed w.
None of these controls refutes an upper bound S≤F(w,w′)d at fixed caps.

[Reproduction instructions and exact receipt](../tools/diagonal-calibration/row-synergy-README.md)
check generator projections, parity-check shortening, the per-order
identity and diagonal additivity. These are computer checks, not Lean
proofs. Taking b independent copies multiplies H,A,R,S by b; dividing
by b gives the same table in entry units. The entropy identities also
apply to coupled lanes and nonlinear codes.

**18.5 (what the candidate statements mean).** Fix one allowed alphabet/
lane policy, such as canonical binary entries, and use uniform code laws
for the candidate bounds. Let r(w) be the limsup of the suprema of H/N
and s(w) the limsup of the suprema of S/N over the same
whole-row codes at forward window at most w. Subadditivity gives S≤H;
(18a) gives S≥2H−N−L. Therefore

  2r(w)−1 ≤ s(w) ≤ r(w).                                 (18e)

A common positive capacity deficit exists if and only if s(w) stays
uniformly below one, **with a possible factor-two change in constants**.
For example s(w)≤1−2δ gives r(w)≤1−δ, while r(w)≤1−δ only gives
s(w)≤1−δ by this argument. This is an asymptotic equivalence; finite
bounds retain L≤wdb.

The strong proposal is S ≤ F(w,w′)db, uniformly in alphabets and lanes,
when both forward and reverse
row degrees are bounded by fixed w,w′. It suffices for half rate with
linear excess. A converse is not supplied by the identity: (N−A) and
(L−R) must also be controlled. With only a forward cap, paid trimming
of high reverse rows would yield asymptotic half rate from this strong
proposal, but not automatically a linear-excess bound. Indeed, freeze
raw rows of reverse degree greater than t. There are at most wd/(t+1)
of them, costing at most wN/(t+1) coordinates. On each fibre delete
their helper incidences and apply the proposed bound with caps w,t.
If s rows were frozen, their zero conditional entropy gives A≤N−sdb.
Thus the conditional entropy bound plus the sdb reveal cost gives rate
at most 1/2+w/[2(t+1)]+o(1) for fixed t. First let d grow, then let
t grow. The raw S of the unconditioned code need not
obey the same trimming estimate.

Capacity alone does not control raw S. For d=4k, take k independent
row triples (a,b,a+b), with a,b uniform vectors of length d, and k zero
rows. Let every column read the 2k data rows. The host's exact capacity
is q^{2kd}=q^{d²/2}; these rows determine the array and the code attains
that many words. Yet A=3d²/4, R=0 and S=d²/4. Its window d/2 grows,
so it is not a counterexample to the fixed-window strong proposal.

Nor is a positive fraction of each row's information being joint enough:
the diagonal sum-zero example has S=d−2 and rate tending to zero, even
though almost every fair split of the other rows reveals its typical
row only jointly. A strong-form counterexample must fix the degree
caps and make S/(db) unbounded. To refute a common deficit one needs
s(w) arbitrarily close to one as w varies.

Finally, an order split is not an independent fair split. For a uniform
random order, row c has predecessor set B with probability
1/[d binom(d−1,|B|)]. Equivalently, choose p uniformly in [0,1] and
place each other row before c independently with probability p. Hence
S is the sum over c of the integral of the expected Syn_c over these
Bernoulli(p) splits. This follows by conditioning on row c's independent
uniform priority, or by integrating p^{|B|}(1−p)^{d−1−|B|}.
At three parity rows the order total is 1, whereas summing the fair-split
expectations gives 3/2. A random-split argument must use the correct
weights or prove an additional comparison.

**18.6 (what the existing barriers give).** The
[row-separator proof](window-pages-and-input-attachments.md#entropic-strengthening-the-actual-row-marginals)
does strengthen directly to S+R ≤ H(Z). If u is that note's number
of revealed entry positions, H(Z) ≤ bu in scalar units. Consequently hyperfinite row relations have
max(S,0)=o(N), and bounded components with no deleted vertices have max(S,0)=O(db).
This follows from conditional single-other-group recovery, not merely
from the old cardinality bound. An arbitrary deterministic common
advice value Q is charged by 2H(Q)−Σ_c I(Y_c;Q) ≤ 2H(Q); the improved
one-copy charge uses that Z consists of fixed coordinates.

The [algebra and twisted-symmetry bounds](symmetry-and-locality.md)
do not yet give a raw-S theorem in the original row coordinates.
A proved dimension estimate 2H ≤ N+D gives only
S ≤ D+(N−A)−R. For example the scalar common-algebra theorem supplies
D=d√a when that algebra has dimension a; the good-characteristic
subgroup theorem supplies its stated cubic-moment D. The extra term
N−A cannot be silently dropped. Row basis changes used in those proofs
need not preserve S: changing three one-coordinate rows (a,b,0) into
(a,b,a+b) takes S from 0 to 1. No new raw-S bound, or counterexample
to such a bound within the symmetry class, is proved here.

## 19. Conditional row recovery and the full Shannon question

Fable and GPT-6 Astra, 14 November 2026. The finite inequalities and
certificates below have written proofs; no new Lean formalization is claimed.
The uniform Shannon-deficit question in 19.4 remains open.

**19.1 (conditional single-row bound, strengthened).** Use base-q entropy
and b scalar lanes per entry. Fix a set B of rows, put n=d−|B|, and let
J₀, J₁, J₊ be the columns with zero, one, or at least two helpers outside
B. For r∈J₁ write s(r) for its unique unrevealed helper row. Let Z_B
contain the unrevealed-row coordinates of the J₊ columns and the b lanes
at (s(r),r) for each r∈J₁. Then

  2H(X | Y_B) ≤ Σ_{c∉B} H(Y_c | Y_B) + H(Z_B | Y_B)
             ≤ Σ_{c∉B} H(Y_c | Y_B) + b[n|J₊|+|J₁|].       (19a)

Consequently

  H(X) ≤ bd|B| + (b/2)[n(|J₁|+2|J₊|)+|J₁|].             (19b)

*Proof.* On each Y_B-fibre, the J₀ columns are fixed. Outside Z_B every
remaining coordinate is recovered from one other unrevealed row. Apply
18.3, and average its joint-coordinate-entropy bound over Y_B. For (19b),
bound the unrevealed row entropies by bn(|J₁|+|J₊|) in total and pay
H(Y_B)≤bd|B|. This is valid for nonlinear recovery and coupled lanes. ∎

**Precisely which relaxation is order-dominated.** The deficit from d²b
certified by (19b) is bG_B, where

  G_B = n|J₀| + (n−1)|J₁|/2.

Put B first in a row order, then order the other n rows uniformly.
Each J₀ column contributes n cells to the row-order DAG; each J₁ column
contributes (n−1)/2 in expectation, the expected number of rows after
s(r). All other contributions are nonnegative. Some full row order
therefore certifies at least G_B cells. This proves domination of (19b),
not of (19a) with actual marginal and exception entropies retained.

There is no random-like-relation hypothesis in the Bernoulli calculation.
If every column has exactly w≥1 helpers and B selects rows independently
with probability p, then exactly

  E[G_B]/d² = (1−w/d)(1−p)[p^w+(w/2)(1−p)p^{w−1}].       (19c)

For a column of degree s≥1 its unnormalized contribution is
(d−s)(1−p)[p^s+(s/2)(1−p)p^{s−1}]. To check this, in the J₀ case all s
helpers are revealed and d−s other rows may survive; in the J₁ case the
one surviving helper cancels the −1 in n−1. A degree-zero column
contributes d(1−p). Linearity of expectation handles overlapping helper
sets. For d→∞ first and then w growing, the best deficit in (19c) is of
order 1/w; the two terms have maxima of that order. ∎

This does **not** rule out every repeated-conditioning or Shannon argument.
After conditioning the array is rectangular, n by d, and a helper set
missing B retains its original size. A general proof-system barrier needs
its own definition and proof; the one-shot count bound supplies neither.

**19.2 (cells, linear codes).** For an order of the scalar coordinates,
let B_f and B_b be the coordinates not determined by their predecessors
and successors, respectively. On a linear code these are the forward and
backward greedy bases of the coordinate matroid. Both have size dim C, so

  2 dim C − N = |B_f∩B_b| − |V∖(B_f∪B_b)|,  N=d²b.

This is inclusion-exclusion. Above half rate, every order has more
coordinates determined by neither side than by both. For the full symmetric
matrix code the off-diagonal pairs give complementary choices, but its db
free diagonal coordinates belong to **both** bases. The identity concerns
scalar coordinates, not indivisible vector entries. It is not a necessity
statement about the form of every possible nonlinear proof.

**19.3 (what reordering cannot do).** For b=1 and any cell order, let
E₋ and E₊ consist of cells whose entire declared helper rows precede or
follow them, respectively. Both induced helper digraphs are acyclic.
Writing α for the host's largest induced acyclic-set size gives

  |E₋∪E₊| ≤ 2α,  |V∖(E₋∪E₊)| ≥ d²−2α.                 (19d)

Empty helper sets can belong to both; loops belong to neither. The
statement concerns declared helpers, not all recovery functions available
on a particular code.

A constant quadratic lower bound in (19d) needs an actual upper bound on
α. Paper 17's [Proposition `expanding`(a)](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex)
supplies one under **both** a perfect matching π(r)∈ρ(r) and
|⋃_{r∈J}ρ(r)|≥(1+ε)|J| for every |J|≤d/2. Together with Proposition
`rows`(b), it gives α≤d(d−1)/2−E_d, where

  E_d = Σ_{j=0}^{⌊d/2⌋} [j−⌊j/(1+ε)⌋].

Thus at least d+2E_d cells have helpers on neither side in every order.
These are cited existing written results, not a consequence of the open
Problem 9.4(c) or of unspecified expansion.

For clarity, ordinary bounded-degree vertex expansion is insufficient for
that conclusion about α. Take a balanced k+k bipartite expander core and
attach one private leaf to each vertex. The resulting balanced row graph
has d=2k and bounded degree. Order core raw rows first and raw leaves
last. Leaf columns contribute Σ_{i=1}^k(2k−i) DAG cells and core columns
contribute Σ_{i=1}^k(k−i), totaling d(d−1)/2. The leaf-core matching
allows row-relabelled symmetric matrices, so this host has exactly
q^{d(d+1)/2} codewords at capacity and α=d(d−1)/2.
Vertex expansion survives: for a set U of at most half the new vertices,
let A be its core vertices and B the labels of its included leaves. If
|A△B|≥|U|/2, the leaf edges supply that many external neighbours.
Otherwise min(|A|,2k−|A|)>|U|/4; core vertex expansion η and maximum
degree Δ give at least η|U|/(4Δ) external core neighbours. Hence the
new expansion is at least min(1/2,η/(4Δ)). This control does not assert
that an order eliminates every split cell; it distinguishes two expansion
hypotheses.

**19.4 (the full Shannon question, and its finite calibration).** The later
[Fano certificate](fano-shannon-certificate.md) proves a strict full-host
gap, Sh=119/3 versus order=41, with no linearity or source-independence
assumption. The asymptotic question below remains open. For
V=[d]×[d], let R_i and C_r be the coordinate sets of row i and column r,
and R_{ρ(r)} their prescribed helper union. Define Sh(ρ) as the maximum
of h(V) over normalized, monotone, submodular functions on **all** subsets
of V such that

  h({v})≤1,  h(C_r∪R_{ρ(r)})=h(R_{ρ(r)}) for every r.     (19e)

This is a finite LP. The column equality is equivalent to the individual
cell recovery equalities by monotonicity and submodularity. For scalar
q-symbol entries, base-q entropy of a uniform codeword is feasible; a
feasible polymatroid need not be entropic.
The series already uses this distinction: Paper 4's
[polymatroid definitions](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/preliminaries.tex)
and Paper 7's elimination certificates explicitly quantify over all valid
polymatroids. Algebraic and spectral bounds with extra decoder hypotheses
are not simply consequences of (19e).

Lanes do not add a separate Shannon-LP obstruction: with b scalar lanes
and unit capacity on each, Sh_b(ρ)=b Sh(ρ). For the upper bound aggregate
the b lanes of each entry and divide h by b. For the lower bound take
h_b(S)=Σ_{ℓ=1}^b h(S_ℓ), where S_ℓ is the entry set selected in lane ℓ.
Both operations preserve the polymatroid and recovery axioms. This says
nothing about realizability of a non-entropic scalar witness.

The asymptotic question is whether

  sup_w limsup_{d→∞} sup_{|ρ(r)|≤w} Sh(ρ)/d² < 1.          (19f)

A Yes gives a common capacity deficit. A No rules out that uniform bound
from only (19e), not a bound using inequalities valid for actual codes.
One finite gap, or a fixed-window family whose Shannon rate exceeds half,
does not by itself decide (19f). Near-order witnesses must be full feasible
polymatroids, with windows fixed before dimension grows. Neither all-cell
Shannon optimality nor a barrier to it has been established in general.

**The requested d=8 instance is already solved.** On F₂³ with
ρ(r)=r+{1,2,4}, the saved order (0,3,5,6,1,2,4,7) has the 18-cell DAG

  A = {1,2,4,7}×{1,2,4,7} ∪ {(6,1),(7,0)}.

Its complement B has 46 cells. In the displayed row order, every cell v_j
of A has helpers H_j inside B∪{v_1,…,v_{j−1}}. Shannon submodularity
therefore gives h(v_j | B,v_{<j})≤h(v_j | H_j)=0. Chain rules and
singleton bounds give h(V)=h(B)≤46. This is an explicit integral dual
certificate: sum the singleton budgets on B, its chain subadditivity
inequalities, and these 18 conditional-entropy decreases; subtract the
zero recovery equalities. Every inequality coefficient is one.

The known product of 24 free loop cells, 16 pairs and two K₄ sum-zero
codes attains q^{46} over every finite alphabet. Thus **Sh(ρ)=46**, with
no LP needed. The same saved certificates give exact Shannon optima 12
and 176 at basis hosts d=4 and d=16. The
[reproduction tool](../tools/diagonal-calibration/README.md#shannon-certificates)
checks the symbolic dual and the existing constructions; it performs no
search. These are existing capacities with an explicit Shannon audit.

**Do not replace the full cell cone by unspecified row/column variables.**
The family F={U(A,B): U(A,B)=R_A∪C_B} is not closed under intersection:
a row meets a column in one cell. Closing under both intersection and
union generates every cell subset. The natural weaker relaxation on F
that keeps only monotonicity, h(U)≤|U| and submodularity pairs whose
intersection is in F is different even at window one. For ρ(r)={r},
put

  h(U(A,B))=f(|A∪B|),  f(k)=dk−⌊k²/4⌋.                 (19g)

It is well-defined: proper line unions have unique A,B, and every
representation of V has A∪B=[d]. The increasing concave sequence f
makes its index-set function submodular; the index set of a retained
intersection is contained in the intersection of the two index sets.
Also |U(A,B)|≥d|A∪B|−⌊|A∪B|²/4⌋: among line unions using k indices,
the smallest has disjoint A,B as balanced as possible. Thus all the
specified partial axioms and h(R_i∪C_i)=h(R_i) hold. At d=3 this gives
7, although the full Shannon/order optimum is 6. The alleged earlier
row/column-only equality with the order bound therefore needs its precise
constraints and a certificate; it is false for this natural relaxation.

**Stronger: the coarse data have a linear entropic realization for every d.**
Over a finite field of size q≥d, choose distinct evaluation points a_i.
For each odd r<d independently choose a uniform polynomial P_r of degree
less than r. Give formal row i and formal column i the same tuple Y_i:
⌈d/2⌉ independent private field symbols, followed by P_r(a_i) for every
such r. The tuple has exactly d symbols. For a set of k indices,
Vandermonde rank gives

  H(Y_A) = ⌈d/2⌉k + Σ_{odd r<d} min(k,r)
         = dk−⌊k²/4⌋.

For the last equality, both sides start at zero and have successive
increments d−⌊k/2⌋. Independence of the private coordinates and polynomial
blocks makes their entropies add. Thus the same coarse values satisfy
all entropy and linear-rank inequalities on these formal variables.
Canonical q=2^{⌈log₂d⌉} works for d≥2. At d=3 the construction is simply
Y_i=(G,P_i,Q_i), one common symbol and two private ones.
For d≥3 the total exceeds the full grid bound d(d+1)/2, so these data
cannot extend to unit-capacity cells with the prescribed intersections.
This is a constant-density obstruction to the specified coarse relaxation,
not a non-Shannon gap or a high-rate code for the full host. Universal
entropy or linear-rank inequalities on the formal variables cannot exclude
these data. A projected grid constraint could: the additional restriction
must encode the missing cell compatibility.

**Literature boundary.** Generic guessing graphs do have genuine Shannon
gaps: [Baber et al., Theorem 6.2, arXiv:1410.8349v2](https://arxiv.org/pdf/1410.8349v2)
give Sh(R⁻)=114/17 and the smaller Zhang–Yeung bound 1212/181.
[Sun and Jafar, Theorems 1–2, arXiv:1303.7000v1](https://arxiv.org/pdf/1303.7000v1)
give a multiple-unicast index-coding example with Shannon symmetric-rate
bound 2/5, Zhang–Yeung bound 11/28 and vector-linear symmetric capacity
5/13. The latter is an
index-code rate, not the storage rate in (19f); linear-rank inequalities
alone constrain only linear codes.

Placing an n-vertex guessing graph on the diagonal realizes its problem
as a **shortened** n×n whole-row host, with all off-diagonal coordinates
fixed. This also embeds its polymatroid by assigning zero entropy off the
diagonal. It does not transfer a Shannon/capacity gap to the unrestricted
host: both full optima may increase, and only n out of n² cells were
active. No verified unrestricted whole-row-host Shannon gap follows from
these references or this placement. The next test must keep the full
cell constraints and the asymptotic density, rather than enlarge a solved
finite calibration or discard the grid intersections.

**19.5 (ordered partial-helper information).** Written proof, independently
reviewed; not Lean-verified. This refines the chain-rule accounting of
18.3 and 19.1; it supplies no new uniform capacity deficit.

Let h be any normalized monotone submodular function on all subsets of
V=[d]×[d], with exact column recovery, and fix a row order. For a nonempty
helper set ρ(c), let last(c) be its last row and put

  E_c = {(p,c) : p < last(c), p ∉ ρ(c)},
  E_q = ⋃_{last(c)=q} E_c,
  P_q = ⋃_{last(c)=q} (ρ(c) ∖ {q}).

Omit empty-helper columns from these definitions: their entropy is zero
by recovery. Write R_q for row q, R_P for the union of rows in P,
E=⋃_q E_q, Inc={(p,c):p∈ρ(c)}, A=Σ_q h(R_q), H=h(V), and
TC_E=Σ_q h(E_q)−h(E). All conditional quantities below are polymatroid
increments; the sets E_q and R_{P_q} may overlap. Then

  2H + TC_E ≤ A + h(Inc | E)
                   + Σ_q [I(E_q;R_{P_q}) − I(R_q;R_{P_q})].       (19h)

In particular, under unit singleton caps and N=d²,

  2H ≤ N + |Inc| + Σ_q I(E_q;R_{P_q}).                            (19i)

*Proof.* The row chain rule gives A−H=Σ_q I(R_q;R_{<q}). Both
E_q and R_{P_q} lie in earlier rows, and exact recovery gives
h(E_q | R_q∪R_{P_q})=0. Hence the summand is

  I(R_q;R_{P_q}) + h(E_q|R_{P_q})
    + I(R_q;R_{<q} | R_{P_q}∪E_q).

Also E∪Inc generates V by induction along the row order: a nonincident
cell is either in E or has all its helpers in earlier rows. Thus
H=h(E)+h(Inc|E). Substitution proves (19h); its exact nonnegative slack
is Σ_q I(R_q;R_{<q}|R_{P_q}∪E_q). Dropping nonnegative terms and using
the singleton caps proves (19i). ∎

If |ρ(c)|≤w for every column, then for every row order H≥(1/2+ε)N
requires the information sum in (19i) to be at least 2εN−wd.
No estimate bounding that sum uniformly
in w is proved here. The generating set E∪Inc is the usual last-helper
order seed; the new display retains the partial-helper information instead
of replacing it by a coordinate count. It is not covered by the claim
that the count relaxation of 19.1 is order-dominated. At window one all
P_q are empty and the existing half-plus-incident bound is recovered.
For lanes the same proof uses all scalar coordinates and their actual
entropies; no independence or linearity assumption is needed.

With reverse degree at most R, each cell lies in at most R+1 of the
sets E_q∪R_{P_q}. The sharper, already available way to bound the
information sum is 20.4: writing
TC_cell(V)=Σ_v h({v})−H, that theorem gives

  Σ_q I(E_q;R_{P_q}) ≤ Σ_{v∉Inc} h({v}) ≤ (R+1)TC_cell(V).

The first inequality uses the disjoint nonincident sets E_q. No additional
incident-cell term is needed. This is **cell** total correlation, not row
total correlation. The cover count alone does not justify charging mutual
information to total correlation on each union: E_q∩R_{P_q} can contain
nonincident cells. Combining the displayed bound with (19i) gives only
H≤((R+2)N+|Inc|)/(R+3), weaker than the existing (20c).

**19.6 (a conditional-Shearer identity).** Written proof, independently
reviewed; not a new entropy principle and not Lean-verified here. For
arbitrary bundles Y_1,…,Y_w with w≥1, let Y be their union and Y_{−j}
the union omitting j. Define DTC(Y)=Σ_j h(Y_{−j})−(w−1)h(Y).
For any bundle C, without a recovery premise,

  Σ_j h(C|Y_{−j}) + DTC(Y) − h(C)
    = DTC(Y|C) + (w−1)h(C|Y) ≥ 0.                              (19j)

Here conditional DTC uses the contracted polymatroid h_C. The identity
is expansion of the definitions. Its nonnegativity is conditional
Shearer: each h(Y_j|Y_{−j},C) is at most its chain-rule increment
h(Y_j|Y_{<j},C). Paper 2's
[`submodular_cover`](../../Local-Coding-Barriers-and-the-Limits-of-Tape-Geometry-for-Matrix-Transposition/lean/TransposeFollowup/SubmodularCover.lean)
already formalizes the underlying covering inequality; (19j) is not a new
covering theorem. Overlapping bundles are allowed. If w=0, the proposed
inequality holds only when h(C)=0, as recovery from empty helpers ensures.
At w=1 it is an identity. The fraction (m−2)/m from an independent
m-cell parity gadget concerns its number of cells, not the helper
window w; no universal triangle-lane fraction in w is asserted.

**19.7 (last-helper correction and a directed-cycle control).** Written
proofs, independently reviewed; not Lean-verified. Assume exactly three
distinct helpers per column, with ordered helper rows p₁(c)<p₂(c)<p₃(c).
Use positions φ in {1,…,d}, and put S_i=Σ_c φ(p_i(c)). Retain E_q and
P_q from 19.5. Let M_c be the cells of column c strictly between p₂(c)
and p₃(c), and let J={(p₃(c),c):c∈[d]} be the last-helper cells. Set

  U = Σ_c h(M_c | R_{p₁(c)}∪R_{p₂(c)}),
  D_q = {(q,c):p₃(c)<q},   F_q=R_q∖D_q,
  Z_q = R_{P_q}∪D_q,      W=Σ_q h(E_q|Z_q).

For any full polymatroid with unit singleton caps and exact recovery,

  H ≤ S₂ + U + h(J) ≤ S₂ + U + d,                           (19k)
  H + W ≤ Σ_q h(F_q|Z_q) ≤ S₃.                             (19l)

*Proof.* Expand H in a row-major cell order. The cells at or before
their column's second helper cost at most S₂. The middle-cell increments
are at most U, since both earlier helper rows precede them. The subsequence
of last-helper increments costs at most h(J), and cells after the last
helper have zero increment. This proves (19k).

Every D_q is determined by earlier rows. Both P_q and E_q lie in earlier
rows, and E_q is determined by F_q∪Z_q. The row chain rule therefore gives
the exact identity

  H = Σ_q h(F_q|Z_q) − W
        − Σ_q I(F_q;R_{<q}|Z_q∪E_q).

Dropping the last nonnegative sum and using Σ_q|F_q|=S₃ proves (19l).
The original correction to the order bound is H≤S₃−W; the intermediate
conditional-row invoice can be much sharper. ∎

Thus an additional premise W≥κU, κ≥0, would give

  H ≤ [κS₂+S₃+κh(J)]/(1+κ).                                (19m)

These displays refine the chain-rule arguments in 19.1 and 19.5; they do
not themselves supply κ. In particular, deleting mutual helper arcs is
insufficient for κ>0 valid for every code and row order, even at forward
and reverse degree three.

**Exact control.** Use row/column labels 0,…,6 in their natural order,
with positions label+1 and helper sets

  ρ = [{0,1,6}, {0,1,4}, {0,1,5}, {2,3,6},
       {2,3,6}, {2,4,5}, {3,4,5}].

Copy one free alphabet symbol to a=(4,0), b=(5,1), c=(6,2), and fix
every other cell. Over every alphabet of size q≥2 this is a q-word code:
a reads c, c reads b, and b reads a. All three cells are nonincident;
none of their pairs is mutual even in the full allowed host. Constant
cells require no reads. Every forward and reverse degree is exactly three.

The only nonzero middle term is column 0, so U=1. The only E_q with
positive entropy is E₆, containing a. Its P₆={0,1,2,3} rows are constant,
but D₆ contains c, so W=0. In total

  (H,S₂,S₃,U,W)=(1,24,44,1,0),   h(J)=0.

Thus loss through D_q need not come from mutual partners. The stronger
conditional-row invoice in (19l) is exactly 1 on this example. The code
has rate 1/49 and uses constant dummy columns and unused declared helpers;
it does not refute a near-order, high-rate, large-girth, averaged-order or
paid-error coupling premise. No asymptotic capacity conclusion follows.

The [standard-library checker](../tools/host-probe/ordered_correction_control.py)
verifies recovery, degrees, the absence of active mutual pairs and every
displayed finite entropy/count value. It evaluates this explicit law
exactly; it performs no host search or numerical entropy optimization.

## 20. Cell budgets, token closures and the Shannon/order test

Fable's proposals, audited and extended by Astra, 14 November 2026.
Status: **written proofs and exact finite certificates, not Lean-verified**.
Fronts D1/D0. No new asymptotic capacity bound or construction with a
positive fixed-window asymptotic gain is obtained. Write V=[d]×[d],
H_r=R_{ρ(r)}, and Sh(ρ) as in (19e).

**20.1 (normalized budgets and the column-symmetry obstruction).** For a
normalized monotone submodular g on cell sets,

  h(S)=min_{T⊆S} [g(T)+|S∖T|]

is a normalized polymatroid with singleton cap one. For minimizers T⊆S
and U⊆Q, use T∪U and T∩U for S∪Q and S∩Q. Submodularity of g and the
identity for the two residual cardinalities prove submodularity of h.
Intersecting a larger-set minimizer with S proves monotonicity;
T=∅ gives h(S)≤|S|. Normalization of g is required.

A row polymatroid a gives g(T)=a(rows touched by T), equivalently
h(S)=min_A[a(A)+|S∖R_A|]. These budgets **can** recover columns:
a(A)=min(d|A|,r) gives h(S)=min(|S|,r), satisfying recovery whenever
r≤d min_j|ρ(j)|. The actual limitation is stronger symmetry. If h is
invariant under a transitive group of simultaneous column permutations,
then a single column equality h(C_r∪H_r)=h(H_r) implies

  h(V)=h(H_r)≤d|ρ(r)|.                                  (20a)

Indeed, the permutations fix H_r and transport the equality to every
column. Submodularity says a union of zero-marginal sets still has zero
marginal. Row budgets have this symmetry, hence rank at most dw at
fixed window w. Arbitrary host polymatroids cannot be symmetrized this
way: these column permutations need not preserve the host constraints.

**20.2 (line envelopes can lose both submodularity and recovery).** Let
u be a polymatroid on formal row and column labels and set

  h(S)=min_{A,J}[u(A,J)+|S∖(R_A∪C_J)|].

Even if every formal column lies in the closure of its formal helper
rows, neither desired conclusion follows. Both failures occur at d=2,
ρ(r)={r}, with labels 0,1 and formal line entropies at most two.

- For u(A,J)=|A∪J|, put S=R_0∪C_0 and T=R_1∪C_1. Then
  h(S)=h(T)=1, h(S∪T)=2 and h(S∩T)=1, violating submodularity.
- Give formal R_0 and C_0 the same two independent symbols, R_1 a third
  symbol, and C_1 none. Thus u(A,J)=2·1_{0∈A∪J}+1_{1∈A}.
  The envelope is the modular function h(S)=|S∩C_0|: C_1 is free and
  no other line purchase saves against paying individually for C_0.
  But h(R_0)=1 and h(R_0∪C_0)=2, so recovery fails.

Formal recovery transfers if one additionally proves
h(H_r)=u(ρ(r),∅): buying those rows and column r then proves the
required equality. This does not by itself prove submodularity.

**20.3 (token closure, including loops).** If each cell x has token
neighborhood τ(x) and g(T)=|⋃_{x∈T}τ(x)|, then h is the maximum matching
size from S to the tokens: the minimum in 20.1 is the bipartite
vertex-cover formula. This is a transversal matroid. For x **outside**
a helper set H, x lies in its closure exactly when there are P⊆H and
Ω such that

  τ(P)=Ω,  |P|=|Ω|,  P has a perfect matching to Ω,  τ(x)⊆Ω.   (20b)

One square block Ω_H works for all outside targets at once. To see this,
choose a maximum matching on H and follow alternating paths from the
unmatched tokens. Let Ω_H be the unreachable tokens and P their matched
cells. No unmatched cell is reachable; every token in Ω_H is matched,
and no cell of P has a neighbor outside Ω_H. Thus P is a square block.
Adding x raises rank exactly when it has a reachable token neighbor,
by the augmenting-path criterion. Any square block in (20b) also
suffices, since it already saturates all its possible token neighbors.

Consequently the whole-row criterion requires one such block inside
H_r covering τ(x) for every x∈C_r∖H_r. **Host-loop targets x∈H_r are
exempt.** For example H={x}, τ(x)={a,b} recovers x without any square
block covering τ(x). Cardinality equality alone is not enough either: matchability
is part of (20b).

The linear realization is classical, not a new result. Put independent
indeterminates at allowed cell–token matrix entries. A minor is nonzero
exactly when its support has a perfect matching, since distinct matching terms
are distinct monomials. Specializing a product of finitely many nonzero
minors proves representability over sufficiently large fields of every
characteristic; it does not promise a prescribed small or canonical
field. See [Rutherford–Whitty, Theorems 2–3](https://arxiv.org/pdf/1707.06727v1)
and [Piff–Welsh (1970)](https://doi.org/10.1112/jlms/s2-2.2.284).

**20.4 (the reverse-degree count is a full Shannon bound).** Let h be
any normalized polymatroid satisfying the column equalities, with
h({v})≤a_v and a_v≥0. Let L=⋃_r(C_r∩H_r) be the host-loop cells and
let w′ bound how many helper unions contain any one cell. Then

  (w′+1)h(V) ≤ w′Σ_v a_v + Σ_{v∈L}a_v,
  h(V) ≤ h(L) + w′/(w′+1) · Σ_{v∉L}a_v.                 (20c)

*Proof.* Greedy marginals along any cell order give a modular vector x
with 0≤x_v≤a_v, x(S)≤h(S) and x(V)=h(V); diminishing returns proves
the subset inequality by comparing with the induced order on S.
For every column,

  x(C_r∖H_r)+x(H_r) ≤ h(C_r∪H_r)=h(H_r)≤Σ_{v∈H_r}a_v.

Summing gives h(V)−x(L)≤Σ_v μ_v(a_v−x_v), where μ_v≤w′ is the
reverse multiplicity. This proves the first bound. Contract L in h
and apply the loopless bound to obtain the second. ∎

For unit caps this includes (w′d²+|L|)/(w′+1), but uses no tokens,
linearity or representability. It is not yet a matching-specific gain;
the shared helper slack can still be charged w′ times.

**20.5 (a non-clique token control, with exact Shannon value).** Take
d=4 and ρ(r)={r,r+1 mod 4}. There are eight loop cells. List the others as

  0=(2,0), 1=(3,0), 2=(0,1), 3=(3,1),
  4=(0,2), 5=(1,2), 6=(1,3), 7=(2,3).

Their residual helper sets, in column pairs, are
{2,4,5,6}, {0,5,6,7}, {0,1,3,7}, {1,2,3,4}.
Pair (0,5), (1,4), (2,6), (3,7), and give both cells of pair i
token neighborhood {z,y_i}. On nonempty S the matching rank is
min(|S|,1+number of pairs touched). Each helper set is a square block
covering its two targets. The residual rank is five, and is the graphic
matroid of K_{2,4}: overlapping four-cell circuits connect all four
pairs, so this is not a direct sum of independent clique-parity codes.

There is an explicit code over **every** finite alphabet. Identify it
with ℤ/qℤ and impose

  x_0+x_5=x_1+x_4=x_2+x_6=x_3+x_7=z.

Choose z and one entry of each pair freely. A target reads its mate and
one complete other pair, obtaining z and then itself. With eight free
loops the code has q^13 words. Its entire entropy function agrees with
the token rank: a subset with no complete pair is independent; otherwise
it reveals z and one symbol per pair touched.

For any row order with positions p_0,…,p_3∈{1,2,3,4}, the order bound is

  Σ_r max(p_r,p_{r+1})=10+½Σ_r|p_r−p_{r+1}|≥13.

The natural order attains 13, hence **capacity = Sh(ρ) = order = 13**.
The largest induced acyclic set has three cells by Paper 17's
Proposition `rows`(b). The saved full Shannon LP on the eight nonloop
cells independently attains five. Removing loops is exact here:
contraction gives the upper bound and adjoining free loops gives the
lower bound, for both polymatroids and codes. The
[standard-library replay](../tools/diagonal-calibration/README.md#cyclic-four-row-host)
checks all 256 primal values, 2,824 Shannon inequalities, recovery
equalities, an exact rational dual, and the explicit code. These are
finite certificates, not Lean proofs. This was the single designated
new host test; it found no strict Shannon/order gap.

**20.6 (why one shared symbol does not supply the missing gain).** More
generally, let Q be a deterministic function of a codeword, and Z a
fixed exceptional coordinate tuple. If, after Q is given, every other
scalar coordinate is a function of one other row, 18.3 applied
conditionally gives

  2H(X) ≤ Σ_c H(Y_c)+2H(Q)−Σ_c I(Y_c;Q)+H(Z|Q)
        ≤ N+2H(Q)+|Z|.                                  (20d)

In the four-pair control, Q=z and Z is the loop tuple. If Q is
computable from one union of at most w helper rows, H(Q)≤wdb in scalar
units. Thus this mechanism yields only O_w(db) excess when |Z|=O_w(db).
The conclusion needs the actual common record and conditional recovery;
it does not follow for arbitrary token designs. The next token target
must address distributed, overlapping square blocks without assuming
one cheap common record. A positive asymptotic rate gain needs Ω(d²b)
excess, not merely an excess larger than O(db).

**20.7 (what Shannon/order equality would settle).** Let σ(ρ) be the
exact acyclic/order bound of Paper 17, Proposition `rows`. Its normalized
envelope approaches one even when windows are fixed before d grows:

  sup_w limsup_d sup_{|ρ(r)|≤w} σ(ρ)/d² = 1.             (20e)

*Proof.* Fix 0<ε<1 and an integer w with wε²>2 ln 2. Independently
sample w rows for each column, allowing repetitions, and put t=⌈εd⌉.
A specified t-row, t-column rectangle has no incidences with probability
at most exp(−wt²/d). There are at most 4^d such rectangles, so a relation
with none exists. For every prefix S_j of j≤d−t rows, fewer than t
columns have all their helpers in S_j. Writing this number a(S_j),

  Σ_r max position(ρ(r)) = Σ_{j=0}^{d−1}(d−a(S_j))
                         ≥ (d−t+1)².

This holds for every order. Take d→∞ and then ε→0; σ≤d² gives equality
in (20e). ∎

Therefore full-cell witnesses with Sh(ρ)≥σ(ρ)−o(d²) on just these
families would already refute (19f); equality on every host is a
stronger sufficient target. No such witnesses are constructed here.
A finite strict gap would instead exhibit a Shannon technique beyond
order, without by itself proving any uniform asymptotic deficit. This
alternative is now realized by the [Fano certificate](fano-shannon-certificate.md):
Sh=119/3<41=σ. Universal equality is false; near-order witnesses on the
random-like asymptotic families in (20e) are still not excluded. The basis
controls and 20.5 remain tight.
Writing an arbitrary cap-one h as its own budget extension (g=h) is
tautological, not a classification of the remaining candidates.

## 21. Token blocks: accounting and bounds for fundamental presentations

Fable's proposal, audited and strengthened by Astra, 14 November 2026.
Status: **written proofs, not Lean-verified**. The general two-thirds
claim in 21.5 is open. Sections 21.6–21.8 prove it, and in one regime a
half bound, under an additional fundamental-presentation or paid-token
hypothesis. These are capacity restrictions, not a native machine exclusion.

Use N scalar coordinates, partitioned into row groups and column groups.
For a column group r let U_r be the union of its helper row groups. The
usual grid has N=d²b, with b coordinates per entry. A token presentation
assigns a finite neighborhood τ(x) to each coordinate. Its rank K is its
maximum matching size. Choose, for each r, a square block P_r⊆U_r with
token set Ω_r=τ(P_r), |P_r|=|Ω_r|, and a perfect matching, such that
τ(x)⊆Ω_r for every target x in column group r outside U_r (20.3).
Host-loop coordinates belong to their own helper union; let L count them.

Fix a global maximum matching. After pruning unused tokens as below,
every token ω has a matched coordinate x_ω. Other coordinates are *slack*.
Put B_x={r:x∈P_r}, K_ω={r:ω∈Ω_r}, m(x)=|B_x| and κ(ω)=|K_ω|.

**21.1 (pruning and support cycles).** Deleting tokens unmatched by the
chosen global maximum matching preserves the rank of every coordinate
subset. Indeed, compare it with a matching on any subset. An alternating
path from a token unused globally but used by the subset matching must
end at a globally used token unused by the subset matching; otherwise it
augments the global maximum. Flipping these paths preserves the subset's
matched coordinates and uses only retained tokens.

Every square-block token is already used by every global maximum: if one
were unused, replacing the fewer than |Ω_r| matching edges into Ω_r with
its perfect block matching would increase the global size. No coordinate
of P_r can have been matched outside Ω_r. Thus the block certificates
survive pruning. Every nonloop coordinate covering ω has another coordinate
covering ω in its helper block. If no loop coordinate covers ω, following
these choices produces a directed support cycle. This is only a necessary
condition, not a capacity estimate.

**21.2 (block-size bound without reverse degree).** If L_0 counts loop
coordinates belonging to no block, then

  2K ≤ Σ_r|P_r| + L + L_0 ≤ Σ_r|P_r| + 2L.              (21a)

*Proof.* Tokens in no block are globally matched to loop coordinates in
no block. For a token in exactly one block, its mate in that block's
perfect matching must be a loop: otherwise its own column would give a
second block, or it would itself be a loop in the first column. These
mates are distinct even across blocks. If one coordinate served tokens
with different unique blocks, its whole neighborhood would lie in both
blocks, contradicting uniqueness. The mates also avoid the L_0 coordinates.
Writing n_j for the number of tokens with κ=j gives
2K−Σκ≤2n_0+n_1≤L+L_0. Finally Σκ=Σ|P_r|. ∎

For bounded forward window, L≤wdb. Thus a fixed positive gain above half
requires average block size above db, asymptotically. The earlier dww′
error term is unnecessary.

**21.3 (weighted saturation, including nonlinear sources).** Call a
presentation *saturated* when each helper union resolves all tokens it
touches: its matching rank is |τ(U_r)|. A square subset suffices; the
whole helper union need not be square. Suppose nonnegative column weights
α_r satisfy

  Σ_{r:i∈ρ(r)} α_r = 1 for every row group i.             (21b)

Let E be the number of globally matched coordinates at incidence distance
one or three between their row and column groups. Then

  2K ≤ N+E ≤ N+L+N_3,                                  (21c)

where N_3 counts coordinates at distance exactly three. Disconnected pairs
are far. No regularity, codegree or symmetry is assumed beyond (21b).

*Proof.* Charge each token to every column block whose helper rows touch
it, weighted by α_r. Its matched row gives charge at least one. If its
matched coordinate (c,r) is far, target recovery supplies another covering
coordinate in a helper row i∈ρ(r). Rows c and i have disjoint column
neighborhoods; a common neighbor would give a length-three walk from c
to r. Such a token has charge at least two. On the other hand, saturation
gives |τ(U_r)|≤|U_r|, so total charge is at most
Σ_r α_r|U_r|=N. Thus 2K−E≤N. ∎

Exact positive reverse-regularity supplies α_r=1/degree; forward
regularity is unnecessary. For arbitrary positive weighted row loads
D_i=Σ_{r:i∈ρ(r)}α_r≥a>0, the same proof gives
2aK≤Σ_i |R_i|D_i+aE. This states the imbalance cost explicitly.
In a d-by-d grid, forward degree at most w and reverse degree at most w′
give N_3≤bdw(w−1)(w′−1), hence half rate at fixed degrees. A forward
bound alone is insufficient for this error estimate: ρ(0)={0},
ρ(r)={0,r} for r>0 has w=2, no pair of columns sharing two helper rows,
and (d−1)² entries at distance three. Its capacity is nevertheless exactly
q^{d(d+1)/2}, by symmetric arrays and the row order starting with row zero.

There is also a **nonlinear version with explicit source assumptions**.
Let A be finite with |A|≥2, let F:A^K→A^V be injective, and let τ(v)
be the essential source coordinates on which F_v depends. Assume whole-column recovery and that
each helper union recovers every source it touches. For any source subset,
fix all other sources. Injectivity forces at least as many incident output
coordinates as sources, so Hall gives a global source-to-coordinate
matching. Column recovery forces source-support inclusion, and exact
recovery gives |τ(U_r)|≤|U_r|. The same charge proves (21c). This removes
linearity from this saturated-encoder statement; it does not assert that
an arbitrary code has such a source representation.

**21.4 (exact slack accounting).** Let c_ω be the column group of x_ω and set

  e_ω = |K_ω∖(B_{x_ω}∪{c_ω})|,
  χ_ω = 1 if c_ω∈K_ω∖B_{x_ω}, and 0 otherwise.

Then κ(ω)−m(x_ω)=e_ω+χ_ω. If ℓ tokens are matched to host loops,
χ_ω=1 for all other tokens. Put E_tot=Σ_ωe_ω and X_loop=Σ_{loop-matched ω}χ_ω.
Double-counting block cells and block tokens gives

  Σ_{slack y}m(y) = K−ℓ+E_tot+X_loop,
  2K−N = ℓ+Σ_{slack y}(m(y)−1)−E_tot−X_loop.            (21d)

In particular, slack multiplicities at most one give 2K≤N+L.
If λ≥0 is an integer, any two distinct row groups share at most λ helper column groups,
and y covers a token whose matched row differs from y's row, then

  e_ω ≥ max(0,m(y)−λ−1).                                (21e)

Among y's blocks at most λ can contain x_ω; at most one further block
is c_ω. This proves the estimate. For λ=1 the hypothesis is equivalent
to no two columns sharing two helper rows. For λ>1 the two oriented
codegree bounds are not interchangeable.

**21.5 (what remains conjectural).** For arbitrary token presentations
on a scalar grid with no such four-cycle, the proposed bound is
K≤(2/3)d²+O_w(d). It has three restrictions relative to the unrestricted
wall: linear/transversal recovery and this host condition. The proof below
adds a fundamental-presentation hypothesis; it does not settle 21.5.

The proposed distinct-payment/common-record dichotomy is not yet a proof.
A high-multiplicity slack coordinate may have no covered token matched in
another row. Even when such tokens exist, failure of a Hall assignment does
not show that their union has O_w(db) entropy, or that conditioning on them
leaves single-row recovery. Multiple group records must be charged jointly;
one cheap-record argument does not automatically cover all of them.
A single finite code above two-thirds cannot refute an unspecified O_w(d)
error. A counterexample needs a fixed-window family with unbounded
excess/d; a fixed positive rate gain would be stronger.

**21.6 (a proved constant deficit for fundamental presentations).** Suppose
there is a distinct basis coordinate x_ω for every token, with
τ(x_ω)={ω}. This is the classical *fundamental transversal* condition;
see [Bonin–Kung–de Mier, §2](https://arxiv.org/html/1009.3435v1#S2).
If λ≥0 is an integer and distinct row groups share at most λ helper column groups, then

  (λ+2)K ≤ (λ+1)N+ℓ ≤ (λ+1)N+L.                        (21f)

In particular, λ=1 gives 3K≤2N+L. There is no reverse-degree bound,
no bound on component size, and no symmetry requirement. On a grid,
L≤wdb, so this gives a window-independent two-thirds asymptotic cap at
each fixed w, uniformly in the number of lanes and the field.

*Proof.* Normalize every square block to include all basis coordinates
in its helper union. If a basis token is absent, add its singleton
coordinate and token; if the token is already present, replace its local
matching mate by its basis coordinate. These operations preserve square
matchability and target coverage. Match all these basis coordinates to
their own tokens. Thus x_ω belongs to a block exactly when its row is a
helper of that block, and loop-matched tokens have χ_ω=0.

Within each block, match basis coordinates to their tokens first. The
remaining local matching pairs every slack coordinate of the block with
a token whose basis row lies outside that helper union. Over all blocks,
a slack coordinate y has m(y) local edges, while token ω has exactly
e_ω+χ_ω≤e_ω+1. Every used edge joins different rows. Set
 a_y=max(0,m(y)−λ−1).
By (21e), each token at the end of an edge from y has e_ω≥a_y.
Give that edge weight e_ω/(e_ω+1). A token receives total weight at most
e_ω, while y sends at least m(y)a_y/(a_y+1)≥a_y. Consequently
E_tot≥Σ_y a_y. Substitute in (21d), with X_loop=0:

  K−ℓ ≤ Σ_y[m(y)−a_y] ≤ (λ+1)(N−K).

This is (21f). Repeated paying tokens are allowed; the fractional weights
control their total use. ∎

The proof bounds any linear code whose coordinate matroid is fundamental
transversal; the presentation need not be the decoder originally displayed.
The class name and its characterization are classical, not claimed as new.
Putting an arbitrary linear generator into systematic form does not establish
this hypothesis: its remaining coefficients can have cancellations that a
generic transversal presentation does not preserve.
The finite d=3 host ρ(r)=[3]∖{r}, with six free loop entries and one
sum-zero triple on the diagonal, has K=8 and equality 3K=2N+L. This is
finite sharpness, not an asymptotically sharp fixed-window family.

Even a forward-window bound is unnecessary for an asymptotic consequence
at fixed raw λ: if I=Σ_r|ρ(r)|, counting row pairs and using Cauchy gives
I²/d−I≤λd(d−1), hence I≤d(1+√(1+4λ(d−1)))/2. Since L=bI,
(21f) gives rate at most (λ+1)/(λ+2)+O_λ(d^{-1/2}).

**21.7 (half rate on the far part, under codegree one).** Under 21.6
with λ=1, let T_3 count tokens whose matched coordinate is at incidence
distance exactly three. Then the stronger finite estimate is

  2K ≤ N+ℓ+T_3 ≤ N+L+N_3.                              (21g)

*Proof.* In the normalized blocks, each nonloop token has exactly e_ω+1
local matching edges. It therefore contributes exactly one to the sum
of 1/(e_ω+1) over its edges. Consider an edge from slack y to a token
matched at a far coordinate (c,r), and put J=B_y. If r∈J, y's row is a
helper of r, so its column neighborhood is disjoint from that of c;
at most r is excluded from J when counting e_ω. If r∉J, codegree one
excludes at most one column containing c. Either way e_ω≥m(y)−1.
Each such edge has weight at most 1/m(y). Thus all far tokens together
number at most N−K, one unit per slack coordinate. The other tokens
number ℓ+T_3. Rearranging gives (21g). ∎

At fixed forward and reverse degrees, this is K≤d²b/2+O_{w,w′}(db).
Unlike 21.3, it needs neither saturation nor balancing weights. It proves
a near-cell bound for this fundamental/codegree-one subclass, including
expanding hosts and globally coupled recovery. If reverse degrees are
unbounded and N_3 is large, the separate two-thirds bound (21f) remains
available.

**21.8 (paying to expose a basis; nonlinear scope).** Delete a token set
Q of size t. The restricted global matching shows that the new rank is
K−t. Restrict each helper block's matching to Ω_r∖Q; the remaining matched
coordinates form a square block covering every remaining target token.
Thus recovery in the token presentation is preserved. Coordinates whose
whole neighborhood was in Q are now constant; let c_Q count them.

If every remaining token has a singleton coordinate after this deletion,
apply (21f) on the N−c_Q remaining coordinates:

  (λ+2)(K−t) ≤ (λ+1)(N−c_Q)+ℓ_Q.                       (21h)

At λ=1, (21g) similarly gives
2(K−t)≤N−c_Q+ℓ_Q+T_{3,Q}. The loop and distance-three masses refer to the
original row/column incidence and the surviving matched coordinates.
These are actual deletion certificates, not assertions that t is small.
Deletion is an operation on the token presentation; it need not be a
source record in every linear realization of the same matroid. With a
specified token-source encoding it can also be interpreted by fixing
those sources. No tape implementation or cheap genie is supplied.
For fixed λ, when t=o(N) and loop mass is o(N), (21h) retains the constant deficit;
when t=O_{w,w′}(db), (21g) retains half plus O_{w,w′}(db).

The four-pair K_{2,4} control of 20.5 becomes fundamental after deleting
z. Its eight-coordinate residual matroid is not fundamental in any
presentation: each union of two pairs is a rank-three cyclic flat. A fundamental basis of
size five would have at least three coordinates in every such union.
Summing the six requirements gives 15≥18, a contradiction. Adjoining the
eight free loop coordinates does not repair this: every basis includes
those eight coloops. Thus a basis change is not a valid way to erase the
added hypothesis. The cyclic-flat characterization is the standard one
in the cited §2.

The same bounds also apply to a restricted nonlinear source model.
Let A be finite with |A|≥2 and F:A^K→A^V injective, with systematic
coordinates F_{x_ω}=z_ω.
For each column assume some helper-coordinate tuple depends only on a
source set Ω_r and recovers that whole source set; Ω_r must also contain
all essential sources of the nonloop targets. Fixing the other independent sources
proves Hall's condition on this tuple's essential-support graph; choose a
square matching subset. The support graph is then a fundamental token
design of rank K, so (21f) and (21g) apply. The support-level normalization
need not leave the actual helper tuple bijective; the proof does not
require that. These source-block assumptions do not follow merely from
systematic encoding or from whole-row recovery.

**21.9 (twins and the remaining target).** All of 21.6–21.8 use only the
two partitions of the scalar coordinate set, not equal row sizes or one
coordinate per intersection. Merge exact twin row and column classes,
retaining all scalar coordinates in each intersection. Identical helper
unions admit one common square block covering all the targets in their
column class, by 20.3. Hence the results apply directly when the **quotient**
incidence graph has codegree one, with N and L counted with their actual
scalar masses. This is a twin-invariant normalization for the proved class.

A uniform k-by-k twin blowup supports k² independent copies of any base
code, preserving that construction's rate. Arbitrary blowup codes instead
correspond to coupled k²-lane codes on the base; optimal scalar rate is
not automatically unchanged. The theorem already permits this coupling.
A small fixed quotient can have positive loop or near-cell mass. The
two-thirds asymptotic conclusion requires L=o(N); half rate requires
L+N_3=o(N), not merely bounded degrees of an unweighted quotient.

The [exact finite controls](../tools/diagonal-calibration/README.md#fundamental-token-blocks)
check the matching identities and fractional payments on specified
examples only. No new host search is used in these proofs.

The bounded pass stops here. The next missing implication is whether
putative high-rate token designs on these hosts can expose a fundamental
basis at small total cost, or whether a distributed nonfundamental structure
evades both payments. A positive rate excess above the proved cap forces
every such deletion certificate to have linear cost; large cost alone does
not imply high rate. General 21.5 and the unrestricted whole-row wall remain
open. Further work should remove this hypothesis or test that implication,
not optimize the constants inside the proved subclass.

## 22. Alignment, bicircular presentations and a uniform constant deficit

Fable's graph proposal, audited and extended by Astra, 14 November 2026.
Status: **reviewed written proofs and exact finite controls, not Lean-verified**.
Front D1. The alignment repair in 22.1 retains a geometric premise.
The separate theorem in 22.5–22.6 removes alignment, fundamentalness and
codegree assumptions for **every two-token presentation**: at fixed forward
window w its rate is at most 5/6+o(1), uniformly in the lane count. Its
Hall-matching proof also gives a constant deficit for bounded support size
with average support size bounded by a fixed μ<5/2. General transversal codes and the
unrestricted whole-row question remain open.

**22.1 (alignment needs a row condition).** Call a presentation *weakly
aligned* if a global matching of all tokens extends to a perfect matching
of every square block P_r: each global pair lying inside P_r is retained.
Equivalently, the block's slack cells can be matched along support edges
to its tokens whose global mates lie outside P_r. Require additionally
that every such local pair y→ω has row(y)≠row(x_ω). Call this *alignment
across different rows*. Under this condition the bounds are

  (λ+2)K ≤ (λ+1)N+ℓ−X_loop ≤ (λ+1)N+ℓ,
  2K ≤ N+ℓ+T₃ ≤ N+L+N₃  when λ≤1.                     (22a)

Here λ bounds common helper columns of distinct rows; the other quantities
are those of 21.4 and 21.7. Fundamental presentations have this alignment
after the normalization of 21.6.

*Proof.* Token ω has e_ω+χ_ω≤e_ω+1 local edges. Every block containing a
slack cell y contains all its tokens. Different rows and codegree λ give
e_ω≥m(y)−λ−1 on each used edge. With a_y=max(0,m(y)−λ−1), the weights
e_ω/(e_ω+1) therefore give E_tot≥Σ_y a_y as in 21.6. Substitute in the
exact identity K−ℓ=Σ_y m(y)−E_tot−X_loop. This proves the first inequality,
without assuming X_loop=0.

For a far nonloop mate x_ω=(c,r), put J=B_y. If r∈J, y's row helps r
and has no common helper column with c, or there would be a length-three
incidence path. If r∉J, different rows and λ≤1 exclude at most one
column from the count. In both cases e_ω≥m(y)−1. Each far token has
e_ω+1 local edges, and gives each weight 1/(e_ω+1); each slack cell
receives at most one. Thus far tokens number at most N−K, proving (22a). ∎

**Why weak alignment alone is insufficient for this proof.** Take d=3,
ρ(r)={0}, y=(0,0) with support {a,b}, x_a=(0,1) with {a}, and x_b=(0,2)
with {b}; all other supports are empty. Match a to x_a and b to x_b.
Let P₁={y,x_b}, P₀=P₂={y,x_a}. These are valid weakly aligned squares,
but m(y)=3 and e_a=0. The local pair y→a has both coordinates in row 0,
and the claimed inequality e_a≥m(y)−1−1 fails. This is a proof
counterexample, not a counterexample to the capacity bound: normalizing
this already fundamental presentation repairs its alignment.

**22.2 (the classical bicircular model).** With at most two tokens per
coordinate, a two-token coordinate is a graph edge, a singleton is a
graph loop, and empty support is a constant coordinate. Parallel edges
are allowed. The matching rank of S is

  rank(S) = |tokens touched by S| − |tree components of S|.

The component count uses only touched token vertices. A tree has matching
rank one less than its vertex count; a cyclic
component has a spanning unicyclic subgraph matching all its vertices.
Ranks add over components. For x outside S, adding x preserves rank
exactly when all its endpoints lie in cyclic components of S; empty
support is automatic. Coordinates already in S are always in its closure.
These are classical bicircular-matroid facts:
[Zaslavsky (1982), Theorem 1(a,c,g,j)](https://people.math.binghamton.edu/zaslav/Tpapers/bglf.qjm1982.pdf).

Thus whole-row recovery requires every endpoint of each non-helper target
in column r to lie in a cyclic component of the helper-row graph Γ_r.
A square block is a disjoint union of unicyclic components. Its local
token-to-edge matching is forced towards the cycle off that cycle; on
each cycle it chooses a coherent orientation.

**22.3 (precise graph consequences).** A fundamental *presentation* has
a singleton at each token. Another presentation of the same matroid may
have that property even when the displayed graph does not. Weak alignment
requires each block's matching to extend the global assignments on its
internal basis cells, including coherent cycle orientations. Merely lying
on the cycle is insufficient: for a triangle ab,bc,ca, match a globally
to ab, c to bc, and b to an outside singleton. The slack edge ca cannot
match the outside token b.

Overlaying local and global matchings gives alternating paths from slack
cells to outside tokens. Their endpoints need not be adjacent in the
support graph. A bad path for one local choice alone does not rule out
another local matching. The four-pair control in 20.5 is a **doubled
hub–leaf star**, with no singleton leaf loops. Whichever pair supplies
the global mate of its hub token z, the helper block recovering its
opposite coordinate has that mate as the leaf token's only occurrence.
It cannot retain the global assignment to z. This presentation is not
weakly aligned, and deleting z exposes a fundamental presentation.

Under codegree one, any fixed token-graph cycle occupying at least two
raw rows can be wholly contained in at most one helper union: choose
two of those rows. A cycle within one row is available whenever that
row helps, and resolves its own tokens; this does not resolve every other
token touched by the row. Different cycles through a token may serve
different columns.

Hereafter a token's *occurrence degree* counts incident coordinates, so
a singleton graph loop counts **once**. Degree-one tokens are possible,
but their sole occurrence must be a host loop. A degree-two token makes
either nonloop occurrence read the other's row. Mutual helping follows
only if both occurrences are nonloops. For example ρ(0)=ρ(1)={0}, with
the same sole token at (0,0) and (1,1), gives recovery only in the
direction from the nonloop coordinate to the loop coordinate.

**22.4 (the alignment question remains open).** Can two-token designs on
codegree-one hosts be brought to alignment across different rows by
deleting O_{w,w′}(db) tokens? Such a certificate, with bounded original
forward and reverse degrees, gives half plus O_{w,w′}(db) by 22.1.
In general the actual loop and near-cell masses must be paid. Large
alignment cost alone does not give a code above half. The next theorem
obtains a constant deficit without resolving this alignment question.

**22.5 (finite bound from support incidences).** Let V be any
finite scalar coordinate set with row and column partitions. For each
column r specify helper rows, whose union of coordinates is U_r. Let
τ(x) be token supports of size at most a, where a≥2 is an integer, and
write I=Σ_x|τ(x)|. Assume the matching
matroid satisfies

  rank(U_r∪{x})=rank(U_r)  for every x in column r.

Write N=|V|, K=rank(V), L for the number of coordinates in their own
helper union, and N₃ for the number at incidence distance exactly three
between their row and column. Then

  6K ≤ 2I+N+(2a+2)L+(a−1)N₃.                            (22b*)

In particular, for every two-token presentation,

  6K ≤ 5N+6L+N₃.                                        (22b)

No alignment, codegree, symmetry, component-size or row-relation degree cap
is assumed.

*Proof.* Prune unmatched tokens using 21.1, preserving every subset rank
and the support-size bound while only decreasing I. Now all K tokens are
matched globally. Let n₁,n₂ count tokens of occurrence degree one and two.
Degree-one tokens force distinct host-loop coordinates, so n₁≤L.
Counting incidences gives

  3K ≤ I+2n₁+n₂.

For each coordinate x let k_x be its number of degree-two tokens. Then
2n₂=Σ_x k_x≤N+Σ_x(k_x−1)_+. We bound the last sum using square blocks,
so this step does not require the graph interpretation.

Consider a nonloop coordinate e containing distinct degree-two tokens
u,v, with other occurrences p,q. Its recovery square must match u and v
to p and q, so both coordinates are helpers and p≠q. If p is nonloop,
its recovery square must contain e, the only remaining occurrence of u,
and match e to u. Because the square contains every token of e, it must
then match v to q. Therefore both e and q help p, giving the walk

  row(e) — column(p) — row(q) — column(e).

Since e is nonloop, its incidence distance is exactly three. Consequently
if e is far (neither a host loop nor at distance three) and k_e≥2,
the other occurrence of **every** degree-two token at e is a host loop.
These k_e loop–token incidences cannot be charged by another far
coordinate: each token has just one other occurrence. There are at most
aL such incidences. Since k_e≤a gives k_e−1≤(a−1)k_e/a, the far
contribution to Σ_x(k_x−1)_+ is at most (a−1)L. The loop and near
contributions are at most (a−1)(L+N₃). Thus

  2n₂ ≤ N+2(a−1)L+(a−1)N₃.

Combining this with 6K≤2I+4n₁+2n₂ proves (22b*). For a=2, I≤2N
gives (22b). Equivalently, in that case at most N₃+2L coordinates
have two degree-two tokens. ∎

**22.6 (forward window alone gives a uniform deficit).** On a d×d grid
with d,b≥1, b scalar lanes per entry and |ρ(r)|≤w, every whole-row
two-token presentation satisfies, for each integer R≥1,

  K/(d²b) ≤ 5/6 + 2w/(R+1) + w/d
                    + w(w−1)(R−1)/(6d).                 (22c)

In particular, for every fixed w,

  K/(d²b) ≤ 5/6 + O_w(d^(−1/2)),                         (22d)

uniformly in b, in the relation, and in any field representing this
coordinate matroid. There is **no reverse-degree assumption**. Section 23.4
improves this two-token asymptotic cap to 2/3 by a core reduction.

More generally, if maximum support size is at most a and I/N≤μ, then

  K/N ≤ (1+2μ)/6 + aw/(R+1) + (a+1)w/(3d)
                      + (a−1)w(w−1)(R−1)/(6d).          (22c*)

For fixed a,w and μ<5/2, this gives the positive asymptotic deficit
(5−2μ)/6. The mean support size may be measured after pruning unused
tokens. This includes presentations with three or more tokens on some
coordinates; bounded maximum arity remains a hypothesis of this corollary.

*Proof.* Set N=d²b and prune unused tokens first. Let H contain rows
whose reverse degree exceeds R. Since Σ_r|ρ(r)|≤wd,
|H|≤wd/(R+1). Delete all tokens touched by coordinates of H. Each such
row has db coordinates, each with at most a tokens, so the cost t
is at most adb|H|≤awN/(R+1).

By 21.8, restricting the global and local square matchings preserves
recovery and leaves rank K−t. Every H-row coordinate now has empty
support. Remove H from every helper set: retained local matched cells
lie outside H, and targets in H are constant, so recovery still holds.
Keep all N coordinates, including constants. The new host has forward
degree at most w and reverse degree at most R. Thus its loop and near
counts obey

  L′≤wdb,  N₃′≤db·w(w−1)(R−1).

For the second count, a length-three path chooses a helper of its target
column, another column using that row, and a different helper of the
second column. These choices bound every distance-three endpoint.
The surviving support-incidence count is at most I. Apply (22b*) to
K−t, divide by N, and add t/N to obtain (22c*). With a=2, μ≤2 this
is (22c). Taking R=⌈√d⌉ proves (22d) and the general asymptotic claim. ∎

**Paid extension to larger supports.** In any pruned whole-row token presentation,
if deleting t tokens leaves every support of size at most two, then 21.8
and (22d) give

  K/N ≤ 5/6+t/N+O_w(d^(−1/2)),  N=d²b.                  (22e)

The same finite error as in (22c) applies. Hence a family of rates tending
to one at fixed forward window requires at least (1/6−o(1))N deletions
for **every** such reduction.
No cheap reduction is asserted, and an expensive reduction alone does
not imply high rate. This is presentation-level rank accounting.

**Scope and next step.** These are bounds for matching-matroid recovery,
and therefore for linear whole-row codes with the stated transversal
presentations. Arbitrary two-sparse coefficient matrices
can have nongeneric cancellations and do not automatically satisfy this
hypothesis. No restriction on alignment, row codegree, coupling or symmetry
remains. The finite theorem permits arbitrary coordinate masses; the
forward-only estimate uses the full balanced grid in its deletion cost.
This is a common deficit for the entire two-token subclass, and for
bounded-arity presentations of mean support size at most any fixed μ<5/2.
It is not a half bound, an unrestricted transversal theorem, or a
native-machine exclusion. Section 28 now proves the corresponding finite
bound and exact core reduction directly for arbitrary field-linear
generators, removing the matching-matroid premise.

The [exact controls](../tools/diagonal-calibration/README.md#two-token-presentations)
check graph versus matching ranks, recovery, the loop charge and the
high-reverse trimming step. They supplement the proof rather than replace
it. The bounded two-token pass is complete, and its low-degree forcing
step already extends to arbitrary supports. The next missing ingredient
is a charge that remains useful at mean support size at least 5/2, or
an argument without the transversal restriction. Improving constants
inside the two-token class is not the next target.

## 23. Block cores and a paid reduction to minimum occurrence three

Fable's core proposal, corrected and proved with an explicit payment by
Astra, 14 November 2026. Status: **reviewed written proofs and exact
controls, not Lean-verified**. Front D1, linear/transversal. The clean
reduction permits arbitrary token supports; the small payment on general
fixed-window hosts uses a bound on support size. Degree means the number
of coordinates containing a token. Prune globally unused tokens first.

**23.1 (what stripping a square actually requires).** Let P be a square
block with token set Ω and a perfect matching. Call tokens of global
degree at most two *low*, the others *high*. Suppose every low token in
Ω occurs in exactly one coordinate of P. Those coordinates are distinct
forced matching mates. Removing them leaves a square on Ω's high tokens:
every remaining coordinate has only high tokens, and the restricted
matching covers every high token. This is a local lemma under the stated
uniqueness condition, not a license to ignore exceptional helpers.

**Raw core deletion can break far recovery.** At d=4 put

  ρ(0)={1,2}, ρ(1)={0,2}, ρ(2)=ρ(3)={0,1}.

Give a=(0,0), b=(1,1) support {h,l}, and q=(2,2), e=(3,3) support {h};
all other supports are empty. The original rank is two and all columns
recover: a uses b,q; b uses a,q; q and e use the square a,b. All active
coordinates are nonloops, and e is far (row 3 is isolated). Token h has
degree four and l degree two. The pure-high core keeps only q,e, so it
loses every nonconstant helper of e. Near helpers were essential to a
far target. Removing their coordinates without a rank payment is invalid.

**23.2 (the exact global defect).** Let H be the high tokens, C the
coordinates with no low token (including constants), D=V∖C, and n₁ the
number of degree-one tokens. For x∈D write k_low(x) for its number of
low tokens. Every pruned presentation, even without recovery, satisfies

  K = rank(C)+|D|/2 + (|H|−rank(C)) + n₁/2
                         + ½Σ_{x∈D}(k_low(x)−1).         (23a)

All three correction terms are nonnegative. Indeed K=|H|+n₁+n₂ and
Σ_D k_low=n₁+2n₂; substitution proves the identity. Thus the proposed
uncharged upper bound is generally in the opposite direction. The
eight-coordinate four-pair control of 20.5 has rank five, no pure-high
active coordinate, and eight noncore coordinates, so five exceeds four.
Padding its other eight coordinates with constants does not change this
comparison. A successful reduction must eliminate or pay all three terms.

**23.3 (clean global core and exact peeling).** Fix a pruned whole-row
token presentation on V, with its row and column partitions and helper-row
relation. Suppose all nonconstant
coordinates are *far*: neither host loops nor at incidence distance three.
Then the pure-high core C is a whole-row token design, all its high
tokens can be matched inside C, and

  K = (|V|−|C|)/2 + rank(C).                              (23b)

Repeatedly applying this operation, with degrees recomputed each time,
gives a retained coordinate set V_* and a whole-row presentation on it
whose every remaining token has degree at least three, with

  K = (N−N_*)/2 + K_*,  N_*=|V_*|, K_*=rank(V_*).         (23c)

Initial constant coordinates are retained. Removed coordinates are kept
out of the later counts; the row relation is unchanged.

*Proof.* A degree-one token would force its sole occurrence to be a host
loop, so there are none. If a degree-two token occurs at x,y and both
coordinates lie in one helper union U_r, recovery of nonloop x forces
y into U_col(x). The walk

  row(x) — r — row(y) — col(x)

has length three, contrary to farness. Thus each low token occurs at most
once in each helper union. Moreover no coordinate has two low tokens:
the forcing step of 22.5 would put their other occurrences on host loops,
whose supports are empty. Therefore |V∖C|=2n₂.

Apply 23.1 to every recovery square. The resulting pure-high squares
cover all high tokens: each high token occurs in a far target, and the
square recovering that target contains it. Their union matches all of H.
For completeness, take a maximum matching on C. If it omits a token of
one square (P,Ω), remove all its edges into Ω, fewer than |Ω| edges.
All P coordinates are then free, since their supports lie in Ω. Inserting
the square's perfect matching enlarges the global matching, a contradiction.
Thus rank(C)=|H|. The same pure-high squares recover every retained target,
so C is itself a valid whole-row design. Equation (23a) now has zero
correction terms and proves (23b).

Core token degrees may have fallen: a formerly high token can become
degree two. Recompute them and repeat. Recovery and farness persist;
degree one is again impossible. Each nontrivial step removes tokens and
exactly twice as many coordinates. The process terminates, and summing
the identities proves (23c). ∎

**23.4 (paying for a clean core).** Let Q contain every token touched by
a loop or distance-three coordinate. Deleting Q preserves recovery and
reduces rank exactly by t=|Q|, by 21.8. Every surviving nonconstant
coordinate is now far. Consequently every whole-row token presentation
has the exact paid decomposition

  K = t+(N−N_*)/2+K_*                                   (23d)

for such a minimum-occurrence-three core. If maximum support size is a,
one can pay t≤a(L+N₃). No small payment is asserted for arbitrary
unbounded supports.

On the balanced grid N=d²b with forward window at most w and maximum
support size at most a≥2, first delete tokens touching rows of reverse
degree greater than an integer R≥1, as in 22.6. In that trimmed relation
pay for all loop and distance-three coordinates. The combined payment is

  t/N ≤ aw/(R+1) + aw/d + aw(w−1)(R−1)/d.                 (23e)

The first term pays the high-reverse rows. The other two follow from
L′≤wdb and N₃′≤db·w(w−1)(R−1). Each deletion preserves recovery and
has the exact token rank cost; recompute the exceptional coordinates
after trimming the relation. With R=⌈√d⌉, t/N=O_{a,w}(d^(−1/2)),
uniformly in the lane count. No reverse-degree assumption is needed.

For two-token presentations, incidence counting in the terminal core
gives 3K_*≤2N_*. Substitution into (23d) gives the direct consequence

  K/N ≤ 2/3 + 2w/(R+1) + 2w/d
                            + 2w(w−1)(R−1)/d,
  K/N ≤ 2/3+O_w(d^(−1/2))  at fixed w.                   (23f)

This improves the two-token cap of 22.6 as a consequence of the structural
reduction. No alignment, codegree, symmetry or component-size assumption
is added, and no two-thirds sharpness claim is made.

**Normalization and the next target.** The core has an inherited coordinate
mask; its rows need not have equal remaining sizes. A future bound
K_*≤(1−δ)N_* gives rate at most max(1/2,1−δ)+t/N for the original
design. A bound only against the full padded grid, K_*≤(1−δ)N, gives
rate at most 1−δ/2+t/N: combine it with K_*≤N_* in (23d). Both statements
assume 0≤δ≤1. Thus a common padded-grid deficit for minimum-degree-three
cores would suffice within the bounded-arity class, with the stated loss.
It does not follow merely by renaming globally high tokens: degrees must
be recomputed, exceptional tokens paid, and the coordinate mask retained.

The [fixed controls](../tools/diagonal-calibration/README.md#block-core-controls)
check raw-core failures, the paid repair, two successive clean peeling
steps, and peeling ordinary pairs to rank zero. The bounded reduction
pass is complete. What remains is a deficit for higher-degree cores,
especially at larger support sizes. Section 28 removes the transversal
restriction by linear elimination and strengthens the bounded-arity
mean-support threshold to three. No higher-degree core deficit or general
machine exclusion follows.

## 24. Cores of supports three: boundary counts and their limitation

Fable's boundary count, audited and extended by Astra, 14 November 2026.
Status: **written proofs and exact finite controls, not Lean-verified**.
Front D1 (linear, transversal). These statements do not give a new
window-independent deficit for cores of support size three.

Work with a pruned presentation on N retained coordinates, of rank K,
maximum support size three and minimum token occurrence three. Write
F=N−K, σ_x=3−|τ(x)| and δ_ω=deg(ω)−3. All are nonnegative, and
Σ_x σ_x+Σ_ω δ_ω=3F. Choose one square block (P_r,Ω_r) in each helper
union that resolves every non-helper target in column r, as in 20.3.
Let m(x)=#{r:x∈P_r}, κ(ω)=#{r:ω∈Ω_r}, and let L be the number of
retained host-loop coordinates. Constants remain in the coordinate count.

**24.1 (weighted boundary inequality).** Put I_loop=Σ_{host loops x}|τ(x)|.
Then

  W := Σ_ω κ(ω)δ_ω + Σ_x (m(x)+1)σ_x
       ≥ 3N−I_loop ≥ 3(N−L).                            (24a)

In a clean core from 23.3–23.4 the loop supports are empty, so W≥3N.

*Proof.* The incidences from Ω_r to coordinates outside P_r number exactly

  Σ_{ω∈Ω_r} deg(ω) − Σ_{x∈P_r}|τ(x)|
    = Σ_{ω∈Ω_r}δ_ω + Σ_{x∈P_r}σ_x,

since |Ω_r|=|P_r| and τ(P_r)=Ω_r. Every **nonloop** target of column r
is outside P_r and has all its tokens in Ω_r. Summing counts at least
Σ_{nonloops x}|τ(x)|. Add Σ_x σ_x to obtain 3N−I_loop. Host-loop targets
are exempt from the square condition and cannot be included in that
boundary lower bound. ∎

**24.2 (what the inequality implies).** Suppose reverse window is at most
w′. Then m(x)≤w′ and κ(ω)≤w′deg(ω): each block resolving ω contains
an occurrence of ω in its helper rows. If every κ(ω)≤κ₀, (24a) gives

  F ≥ (N−I_loop/3)/max(κ₀,w′+1).                       (24b)

For F>0 the defect-weighted average multiplicity is at least
R=(N−I_loop/3)/F. **Only if R>w′+1** does this force some positive token
defect δ_ω>0 with κ(ω)≥R. Otherwise support defects can pay the displayed
lower bound. This is an existence assertion, not a lower bound on every
high-degree token.

Deleting the t tokens of degree greater than an integer D≥3 preserves
recovery and costs t ranks. If w′≥1, applying (24b) afterward yields only

  F ≥ (N−L)/(w′D)−t.

The coarse estimate t≤3N/(D+1) makes this net bound nonpositive. Paying
from the original defect instead gives t(D−2)≤Σδ≤3F, and hence

  F ≥ (D−2)(N−L)/(D(D+1)w′).                           (24c)

In a clean core N replaces N−L. For example D=4 gives (N−L)/(10w′).
This is weaker than the reverse-window Shannon bound (20c), which gives
F≥(N−L)/(w′+1). Truncation therefore repairs the accounting but supplies
no improvement over the existing rate bound. In a clean core the loop
coordinates are constant; deleting them in (20c) gives the stronger
comparison F≥N/(w′+1).

**24.3 (bounded occurrence does not bound reuse).** For any integers
w,m≥2 set d=mw and partition the indices into m classes of size w. A
column reads exactly the rows of its own class. For each unordered pair
of distinct classes A,B, take w² new tokens arranged in a simple cycle.
Place one copy of its w² two-token edges on A×B and another on B×A,
in any cyclic enumerations of those coordinates. Make all diagonal
class blocks constant. This is a pruned whole-row presentation with

  N=d², L=dw, K=(N−L)/2, deg(ω)=4, κ(ω)≥2w.            (24d)

Every active coordinate is far. Canonical square choices have κ(ω)=2w
and m(x)=w on active coordinates, and therefore

  Σκδ=2wK,   Σδ=K,
  W=(2w+1)(N−L)+3L,
  Σκδ/(N−K)=2w(m−1)/(m+1).                            (24e)

*Proof.* The incidence graph is a disjoint union of complete bipartite
graphs on corresponding classes, so off-class cells have disconnected
row and column endpoints. Each token occurs twice in each cycle copy.
One copy matches all its tokens, proving the rank count. The helper rows
of any column in A contain the entire A×B copy, which resolves all its
targets in B×A; use the opposite copy for a column in B.

A nonempty proper edge subset of a simple cycle touches strictly more
tokens than edges. Within one helper union there is only one copy of
each relevant cycle, and different cycles have disjoint token sets.
Their imbalances cannot cancel. Thus a square resolving any target
token of this component must contain the whole helper cycle. Each of
the 2w columns in A∪B has such targets, forcing κ(ω)≥2w regardless of
block choices. Taking just the required cycles gives equality and the
stated m(x). Substitution proves (24e). ∎

Replacing one cycle copy by one singleton occurrence of each token is
also a valid whole-row presentation: either copy resolves the full token
set. Its rank is unchanged, all active coordinates remain far, and every
token now has degree three. Thus δ vanishes and support defects alone
pay (24a). The finite controls check both versions.

The doubled-cycle family rules out a universal bound of Σκδ by a constant
times Σδ or N−K, independently of w, even after excluding occurrence
degrees above four. At each fixed w its rate tends to **one half** as
m grows. It is already within the class bounded in 23.4, not a new
high-rate construction or a counterexample to a common deficit. A
rate-sensitive argument could still work. The bounded boundary-charge
pass found no such argument and stops here; arbitrary higher-support
cores remain open.

## 25. A full-cell Shannon calibration beyond the basis hosts

Astra, 14 November 2026. Status: **written argument with an exact finite
computer-checked certificate, not Lean-verified**. Fronts D0/G4. The
higher-support charge in section 24 supplied no new rate bound. This
single calibration removes the transversal and linearity premises from
the upper-bound question; it does not settle the asymptotic wall.

**25.1.** On the cyclic five-element index set, let ρ(c)={c,c+1}.
Then its full-cell Shannon value, defined in (19e), is

  Sh(ρ)=19=σ(ρ),                                       (25a)

where σ is the exact order bound. Section 27 now gives a code of size
q¹⁹ over every finite alphabet and identifies its full rank function
with this witness.

*Proof of the upper bound.* If p₀,…,p₄ are the positions 1,…,5 in a
row order, then

  Σ_c max(p_c,p_{c+1}) = 15 + ½Σ_c |p_c−p_{c+1}| ≥ 19.

The two paths around the cycle between the positions 1 and 5 each have
variation at least four. The natural order attains equality. Thus the
whole-row order proposition of
[Paper 17](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex)
gives σ=19. Its six-cell DAG is

  {(2,0),(3,0),(3,1),(4,0),(4,1),(4,2)}.

The chain-rule argument in 19.4 gives h(V)≤19 for every feasible h.

*Exact witness for the lower bound.* The ten loop cells can be removed
exactly: Sh(ρ)=10+Sh_residual. For the upper direction contract their
joint entropy, which is at most ten. For the lower direction adjoin ten
independent unit coordinates to any residual witness. A loop target is
already in its helper rows, so this preserves all original recoveries.

Label the fifteen remaining cells by j=3c+k−2 at (c+k,c), where
c=0,…,4, k∈{2,3,4}, and arithmetic on coordinates is modulo five.
A subset is encoded by the integer whose bit j indicates membership.
The [compact witness](../tools/diagonal-calibration/cyclic5-rank-witness.json)
supplies fifteen pairs (subset mask, assigned rank). Apply the ten maps

  (r,c) ↦ (r+a,c+a),   (r,c) ↦ (1−r+a,−c+a),  a∈ℤ/5,

to obtain a family ℱ of 68 subsets with consistent assigned ranks q_F.
Define on **every** residual subset S

  h(S)=min_{F∈ℱ} [q_F+|S∖F|].                          (25b)

This formula is not assumed to be submodular merely because it is a
minimum. The [standalone verifier](../tools/diagonal-calibration/verify_cyclic5_rank_witness.py)
reconstructs all 32,768 values using integers and checks normalization,
all 15 singleton caps, all 245,760 one-element monotonicity inequalities,
all 860,160 elemental submodularity inequalities, and all five column
recovery equalities. These elemental inequalities imply full monotonicity
and submodularity by telescoping. The computed total is h(V_residual)=9.
This proves the feasible lower bound 10+9=19. The same checks show that
the integral witness is a matroid rank function and that ℱ is exactly its
set of cyclic flats; neither assertion is needed as a shortcut for the
entropy checks. ∎

The witness was found by one full-cone LP solve, using recovery closure
and the displayed symmetries to reduce the variables. Its published
verification uses no optimizer, floating-point arithmetic or truncated
subset family. It reproduces the certificate in under a second on the
development machine; runtime is not part of the proof.

**Scope and next use.** Shannon/order equality on this host is not
equality for every whole-row host. Section 27 supplies the formerly
missing graphic and entropic realization; independent copies also attain
Sh_b(ρ)=19b for scalar lanes, as bounded in 19.4. Fano's
scalar-linear value 39 over F₂ and F₃ is a different kind of result:
its known three-bit construction implies Sh(Fano)≥119/3, and the later
[exact Shannon certificate](fano-shannon-certificate.md) gives the matching
upper bound, below order 41. Token-matching counts cannot be imposed on arbitrary
feasible polymatroids without proving their additional premises.

The next useful step would be a full-cell extension rule that produces
feasible polymatroids on growing hosts, or an inequality showing why such
a rule fails. For a Shannon barrier to a common deficit, windows must
remain fixed before dimension grows and the attainable rates must tend
to one as the window grows. The cyclic construction still has asymptotic
rate one half. This calibration ends the one-host LP experiment; no larger
LP search is justified by equality at one more instance.

## 26. Row-closure budgets: audit and a finite completion

Fable's proposal, audited and extended by Astra, 14 November 2026.
Status: **reviewed written arguments and exact finite checks, not
Lean-verified**. Front G4. The original inclusion–exclusion prescription
fails. A modified envelope reproduces the entire cyclic-five witness;
section 29 refutes its validity on general hosts.

**26.1 (the row-order envelope).** For row sets A let
J(A)={r:ρ(r)⊆A} and F_A=R_A∪C_{J(A)}. Define g(∅)=0 and

  g(A)=min_{orders i₁,…,i_a of A}
          Σ_{ℓ=1}^a [d−|J({i₁,…,i_{ℓ−1}})|].

This is the cost of the specified row-order procedure, not necessarily
of the smallest arbitrary generating set. For example, at d=3 with
ρ(r)={0} for every column, g({1,2})=6, but the three cells of row zero
already generate those rows. Global order optimality also need not force
h(F_A)=g(A): keep row zero free and all other rows constant on this host.
This attains total entropy three while h(F_{ {1,2} })=0.

Put h₀(X)=min_A[g(A)+|X∖F_A|]. It is normalized, monotone, has singleton
caps one, satisfies all column recoveries, and has h₀(V)=σ(ρ).

*Proof.* Append the rows of B∖A to an optimal order of A. Since J only
increases along an order,

  g(A∪B)≤g(A)+|B∖A|(d−|J(A)|)
         =g(A)+|R_B∖F_A|.                              (26a)

Apply this with B=ρ(r) and A minimizing h₀(R_B). The set F_{A∪B}
contains both R_B and C_r, so h₀(R_B∪C_r)≤h₀(R_B); monotonicity gives
equality. With B all rows, (26a) shows σ=g([d])≤g(A)+|V∖F_A|, while
A=[d] gives equality. Nonnegativity, A=∅, and the individual terms prove
the remaining claims. ∎

Adding purchases of extra columns at their raw uncovered-cell cost
cannot lower this envelope: their cost is at least the number of newly
covered cells of X. This does not assert that columns cannot be bought
more cheaply through a different coding argument.

**26.2 (the submodularity obstruction).** At d=2 with ρ(r)={r}, the
sets F_{ {0} },F_{ {1} } have h₀-values two, their union has value three,
and their two-cell intersection has value two. Submodularity fails.
For general A,B, one sufficient uncrossing condition is

  g(A)+g(B) ≥ g(A∪B)+g(A∩B)
       +|A∖B|·|J(B)∖J(A)|+|B∖A|·|J(A)∖J(B)|.          (26b)

Indeed J(A∩B)=J(A)∩J(B). The last two terms count precisely
(F_A∩F_B)∖F_{A∩B}, while F_{A∪B} contains F_A∪F_B. Apply those two
sets to minimizers of h₀(X),h₀(Y), and charge at most that many extra
intersection cells. This proves submodularity if (26b) holds for all
A,B. It is a sufficient condition for this proof, not a necessary
characterization of submodularity of the minimum envelope.

**26.3 (inclusion–exclusion is not intersection rank).** For a nonempty
family 𝒜 of row sets write

  F(𝒜)=⋂_{A∈𝒜} F_A,
  b(𝒜)=Σ_{∅≠𝒯⊆𝒜}(−1)^{|𝒯|+1}g(⋃_{A∈𝒯}A).          (26c)

On cyclic five, g(A) depends only on |A|, with values
(0,5,10,14,17,19). Three distinct singleton row closures are disjoint,
yet their empty intersection gets budget 15−30+14=−1. Two singleton
closures give the same empty set budget zero. The inconsistency persists
away from negative budgets:

  F_{ {1,2} } ∩ F_{ {0,1,3} }
    = F_{ {0,1,3} } ∩ F_{ {1,2,3} } ∩ F_{ {1,2,4} }

is an eight-cell set with respective budgets seven and eight. Clipping
to the interval [0,|F|] does not make those two assignments equal.
The actual witness gives this set rank seven.

This failure is not evidence of a Shannon/order gap. Already at cyclic
d=3, g has values (0,3,6,8), so three singleton closures give −1 to
the empty intersection. Six free loop cells and one sum-zero relation
on the other three cells attain q⁸ over every finite alphabet; their
row-union entropies equal every g(A). Thus even exact, entropic input
budgets do not satisfy the proposed intersection formula. Pairwise
submodularity gives only an upper bound on an intersection rank; higher
inclusion–exclusion is not a universal bound of that kind.

More generally suppose every helper set has size at least k≥2, and
some has size k<d. Choose S consisting of that helper set and one more
row. Every proper A⊂S has g(A)=d|A|, whereas

  g(S)=d(k+1)−M,
  M=max_{B⊂S, |B|=k} #{r:ρ(r)⊆B}≥1.

Only the final row can save any cells in this order. The singleton
closures indexed by S have empty intersection, but (26c) gives it
(−1)^{k+1}M. The raw valuation is inconsistent for every k; for even k
it is negative. For odd k this particular positive empty-set value is
removed by the cardinality cap, so it alone does not refute the capped
rule.

The identity window-one case is different: g(A) counts the independent
unordered-pair symbols touched by A in a symmetric matrix. Inclusion–
exclusion then really counts the symbols in an intersection. Its
minimum envelope is the symmetric-array rank: unions of selected
complete off-diagonal pairs are intersections of row closures, and
remaining singleton cells cost one. This argument concerns ρ(r)={r}
up to bijective relabelling, not arbitrary window-one maps.

**26.4 (a well-defined repair, exactly checked on cyclic five).** Instead
set

  b_*(F)=max(0, min(|F|, min_{𝒜:F(𝒜)=F} b(𝒜))),
  h_*(X)=min_F [b_*(F)+|X∖F|].                          (26d)

The original presentation-independent formula is false; (26d) is a
different rule. On cyclic five, it equals the full rank witness of
section 25 on **every subset of the 25-cell grid**.

*Finite certificate.* Removing a repeated row set, or a set containing
another set of 𝒜, preserves both F(𝒜) and b(𝒜). For the latter, pair
the inclusion–exclusion terms containing the larger set according to
whether the smaller one is present. Hence the 7,580 nonempty antichains
of subsets of [5] cover every presentation. The
[exact checker](../tools/diagonal-calibration/row_closure_completion.py)
evaluates them all, giving 919 intersection sets. All 68 cyclic flats
of the witness, embedded with no loop coordinates, occur among them;
all 32 original row-closure ranks equal g(A).

Let h be that full witness, with its ten independent loop coordinates.
For each of the 919 sets the checker verifies b_*(F)≥h(F), and it checks
h_*(F)=h(F) on all 68 defining cyclic flats. These tests prove equality
on every subset, without enumerating 2²⁵ sets. First,
h(X)≤h(F)+|X∖F|≤b_*(F)+|X∖F|, giving h≤h_*. Second the envelope itself
satisfies h_*(X)≤h_*(F)+|X∖F|. Minimize this over the defining flats in
(25b), now with loop cells paid at unit cost, to obtain h_*≤h. ∎

No general submodularity or recovery theorem for (26d) follows. Section
29 now refutes both on a window-three host. Section 27 identifies the
cyclic witness as a graph-difference code, providing a constructive
explanation of this positive calibration.

**Why nonnegative coverage profiles cannot be the general repair.** If an
actual feasible polymatroid has row entropies
h(R_A)=Σ_{T:T∩A≠∅}a_T with a_T≥0, then

  2h(V)≤Σ_i h(R_i)+Σ_i h(R_i | R_{[d]∖{i}})≤N+L.

The first inequality holds termwise: a symbol counted in m rows
contributes m, and contributes one more exactly when m=1. The second
uses singleton caps and recovery: given the other rows, only host-loop
coordinates in row i can remain undetermined. This is the coverage
case of the signed-synergy argument in section 18, not a new frontier
bound. It needs only the stated entropy profile, not an independent-
source realization. A completion aimed at rates approaching one must
allow the joint dependencies that inclusion–exclusion does not treat
as independent set atoms.

## 27. Exact capacity at window two

Astra, 14 November 2026. Status: **reviewed written proof with exact
finite controls, not Lean-verified**. This supplies all-d attainment of
Paper 17's whole-row window-two bound and realizes the cyclic-five
witness. It does not improve the asymptotic half-rate bound.

**27.1 (cyclic difference code).** Let d≥2 and let the alphabet have
q≥2 symbols. For ρ(r)={r,r+1 mod d}, the maximum whole-row code size is

  q^{d(d+3)/2−1}.                                      (27a)

Since Paper 17's Proposition `order`(b) bounds every whole-row host of
window at most two by this same number, (27a) is also the exact maximum
over **all** such hosts and codes, with arbitrary nonlinear recovery.

*Construction and recovery.* Identify the alphabet with any abelian
group Q of order q, for example ℤ/qℤ. Take source values z_{ij}=z_{ji}
for unordered distinct i,j, and two private values a_i,b_i for each row.
All indices below are cyclic. Define

  X[c,r]   = z_{c,r}−z_{c,r+1}  if c∉{r,r+1},
  X[c,c]   = a_c−z_{c,c+1},
  X[c,c−1] = b_c−z_{c,c+1}.                             (27b)

Row c gives the consecutive differences along the path
z_{c,c+1},z_{c,c+2},…,z_{c,c−1}, and the differences from a_c,b_c to
its first vertex. Hence it determines every difference among these
d+1 source values. For a nonloop target X[c,r], row r determines
z_{r,c}−z_{r,r+1} and row r+1 determines
z_{r+1,c}−z_{r+1,r}. Their difference is exactly X[c,r]. The two loop
targets of column r are already in its helper rows. This proves recovery.
For d=2 the path has one vertex and no edges, and all targets are loops;
the same construction and count apply.

*Size.* Regard each source value as a vertex and each cell as its
oriented difference edge. The row edges form a tree on that row's d+1
source vertices. The trees for distinct rows i,j meet at z_{ij}, so the
global graph is connected. It has binom(d,2)+2d vertices. Two source
assignments give the same array exactly when their difference is one
common additive constant on this connected graph. Every fiber therefore
has q elements, proving the size q^{binom(d,2)+2d−1}. The private edges
are leaves, so their 2d loop coordinates are independently free.

*Upper bound.* For the cyclic relation the order expression is

  Σ_r max(p_r,p_{r+1})
    =d(d+1)/2+½Σ_r |p_r−p_{r+1}|.

The two paths between positions 1 and d force total variation at least
2(d−1), attained by the natural cyclic order. Thus σ=d(d+3)/2−1;
the Shannon/order argument proves the upper bound. The universal
window-two upper bound is already proved in
[Paper 17](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex),
Proposition `order`(b) and the following whole-row paragraph. ∎

**27.2 (the entropy witness is graphic).** After deleting the private
leaves, the auxiliary graph has vertices {i,j} and edges
{c,r}—{c,r+1} for c∉{r,r+1}. For d≥3 this is the classical two-token
graph F₂(C_d), as defined by
[Fabila-Monroy et al., *Token Graphs*](https://arxiv.org/abs/0910.4774).
That reference concerns the graph, not the capacity application here.
Take the source values independently and uniformly in Q, which induces
the uniform distribution on the code. For any subset S of cell edges,
use the full auxiliary graph, including private leaves; for residual
subsets one may equivalently delete those leaves. Its normalized entropy is

  h(S)=|V_graph|−components(V_graph,S),                  (27c)

where isolated vertices are counted. Indeed each component permits
one independent constant shift of the source values. This is the graphic
matroid rank, over every field and also as an entropy profile over any
finite abelian alphabet.

At d=5, the [exact checker](../tools/diagonal-calibration/cyclic_difference_code.py)
compares (27c) with all 32,768 residual subset values in section 25;
they agree exactly. Thus the earlier certificate has an explicit
all-alphabet realization, not merely an achievable total value.
At d=3 this is the sum-zero triangle with free loops; at d=4 its
nonprivate graph is K₂,₄, recovering section 20.5.

**Scope.** These are functions of two **whole rows**. A recovered entry
may use a path of growing length inside each row; this does not settle
the sparse one-class problem with only two scalar helpers per entry.
The gain over ordinary transpose pairing is exactly d−1, so the rate
still tends to one half. Pair-source variables and O(d) private variables
cannot supply a positive limiting excess by themselves. No linear-time
tape implementation or window-three capacity bound follows. The bounded
literature check identified the underlying token graph and the existing
d=3,4 special cases; no novelty claim for the full application is made.

## 28. Arbitrary-coefficient source bounds and exact core reduction

Fable's extension, audited and strengthened by Astra, 14 November 2026.
Status: **reviewed written proofs, not Lean-verified**. The transversal
premise in sections 22–23 is removed here. What remains is linearity and,
for inexpensive exceptional-cell deletion, a bound on generator support.
The mean-support consequence improves the earlier threshold 5/2 to 3.

**Later extension.** [Sparse encoders](sparse-encoder-cores.md) removes
linearity over finite alphabets: injective encoders of a full independent
source cube satisfy the same exact core reduction, asymptotic two-source
2/3 bound, and mean-support threshold three with bounded maximum support.
The proof replaces subtraction by relative permutations. The source and coordinate alphabets must have the
same finite size; arbitrary correlated-source fibres are not covered.
The infinite-field result proved here remains separate.

**Setup.** Let G be an N×K matrix of column rank K over any field F.
Its image is a linear whole-row code on a coordinate set V, with the
specified row and column partitions; write ℓ_x for its coordinate
functionals. A *source* is one of these K independent generator columns.
Its degree counts nonzero entries in that column. Put

  I=Σ_x |supp(ℓ_x)|,

and let a≥2 bound every coordinate support. The finite clean-core
statement will not need a. Zero coordinates are retained in V. L and
N₃ count coordinates at incidence distance one and exactly three,
respectively, in the row-helper bipartite graph, as in section 22.

Recovery may initially be nonlinear: on a linear code it implies that
ℓ_x lies in the linear span of the helper functionals. Indeed their
common kernel is contained in ker(ℓ_x), so ℓ_x factors linearly through
the helper map. We use these exact linear identities below. Source
counts require a full-rank generator, not a redundant parametrization.

**28.1 (low-source forcing, with arbitrary coefficients).** A source
occurring once forces its sole cell to be a host loop. Distinct such
sources have distinct sole cells, since two generator columns supported
on the same cell would be proportional. Thus n₁≤L.

Suppose a nonloop cell e contains two degree-two sources u,v, whose
other occurrences are p,q. Recovery forces p,q into e's helper union.
They are distinct: if p=q, recovery makes the coefficient pair at e a
scalar multiple of the pair at p; the two source columns, supported only
there, would be proportional. If p is nonloop, its recovery uses e with
nonzero coefficient to supply u, then must use q to cancel v. Hence

  row(e) — column(p) — row(q) — column(e)

is a length-three walk. A far e, meaning neither a loop nor distance
three, therefore has p and q on host loops. The argument applies to
every pair of degree-two sources at e, regardless of its support size.

The incidence count in 22.5 now applies without square matchings:
3K≤I+2n₁+n₂, and the same loop/near charge gives

  2n₂≤N+2(a−1)L+(a−1)N₃.

Consequently

  6K≤2I+N+(2a+2)L+(a−1)N₃.                             (28a)

For a=2 this is 6K≤5N+6L+N₃. This proves Fable's extension of the
finite theorem over every field; the sharper consequences below also
remove genericity from the core argument.

**28.2 (source deletion).** Fixing t selected source values to zero
restricts G to the other K−t columns. They remain independent, so the
new dimension is exactly K−t; every recovery identity survives. If the
deleted columns contain J nonzero entries in total, the new incidence
count is I−J, with J≥t. This is deletion in the same source basis, not
an uncharged rebasing or coordinate deletion.

**28.3 (clean elimination and exact peeling).** Suppose every nonzero
coordinate is far. Call degree-two sources low and the others high.
There are no degree-one sources. A low source occurs at most once in
any helper union: if its two cells x,y both help a column r, recovery
of x also requires y to help column(x), giving
row(x)—r—row(y)—column(x), a forbidden length-three walk. No cell
contains two low sources, by 28.1 and the absence of nonzero loops.
Their coordinate pairs are therefore disjoint.

Let C retain the pure-high and zero coordinates. For a low source u
at x,y with coefficients α_x,α_y, recovery of x must use y with
coefficient α_x/α_y. Every other helper carrying a low source has
coefficient zero: that source appears only once in the helper union
and not in x. It follows that

  ℓ_x−(α_x/α_y)ℓ_y ∈ span{ℓ_z : z∈C}.                 (28b)

Modulo this span each low pair contributes at most one dimension, and
exactly one by projection to its distinct low-source coordinate. As all
coordinate functionals span F^K,

  rank(G restricted to C)=K−n₂=number of high sources.

For a pure-high target, all low-bearing helper coefficients likewise
vanish. Thus C itself recovers using only its pure-high helper cells.
Its original high-source columns remain a full-rank generator; no basis
change increases the supports. In particular

  K=(N−|C|)/2+rank(G restricted to C).                  (28c)

Recompute degrees on C and repeat. Each nontrivial step removes one
source and two cells per low pair. The inherited coordinate mask keeps
all initial constants, and removed cells are not counted again. The
process ends at a code with minimum source occurrence three and

  K=(N−N_*)/2+K_*.                                    (28d)

This is the complete linear counterpart of 23.3, with no maximum-support
bound, in every characteristic. Hall squares are replaced by (28b).

**28.4 (payment and strengthened consequences).** Delete every source
touched by a loop or distance-three coordinate; this costs at most
a(L+N₃). The surviving code is clean, so 28.2–28.3 give the exact
paid decomposition

  K=t+(N−N_*)/2+K_*.                                  (28e)

More generally t may include a preliminary deletion making designated
helper rows zero and removing them from the relation. No payment is
needed for the clean case; no cheap payment is asserted without a
support bound or a separate estimate for t.

If the maximum support is two, the terminal incidence count gives
3K_*≤2N_*. Substitution into (28e) yields K≤2N/3+t.

There is a stronger mean-support bound than (28a). In the first clean
step, K=n₂+|H|, N≥2n₂+|H|, and I≥2n₂+3|H|, because the pure-high
coordinate restriction has rank |H|. Adding the last two inequalities
gives 4K≤N+I. After the payment of 28.2, with its actual incidence loss J,

  4(K−t)≤N+I−J,
  4K≤N+I+4t−J≤N+I+3t.                               (28f)

On a balanced d×d grid with b scalar lanes and forward window w,
first delete sources touched by rows of reverse degree greater than an
integer R≥1, then delete those touched by the loop/near coordinates
of the trimmed relation. Exactly as in 23.4, N=d²b and

  t/N≤aw/(R+1)+aw/d+aw(w−1)(R−1)/d =: E_{a,w,d}(R).   (28g)

The high-reverse rows become zero, so removing them from every helper
set preserves recovery. The remaining relation has reverse degree at
most R and exceptional masses at most wdb and db·w(w−1)(R−1).
These counts and literal source deletion prove (28g).

Thus two-sparse full-rank generators satisfy

  K/N≤2/3+E_{2,w,d}(R),

and generators with I/N≤μ satisfy

  K/N≤(1+μ)/4+(3/4)E_{a,w,d}(R).                      (28h)

For fixed a,w, take R=⌈√d⌉. The bounds are uniform in the field,
coefficients, lane count and chosen generator. In particular every
fixed-window family with a uniformly bounded maximum support and
mean support μ<3 by a fixed margin has a common positive deficit.
A family of rates tending to one must have liminf I/N≥3 in every
sequence of bases satisfying that maximum-support condition. Arbitrary
bases with unbounded maximum support are not covered by this deduction.
For maximum support two, the separate 2/3 bound is stronger.
This does not force density growing with d: maximum and mean support
three remain unexcluded.

For a selected linear fibre with K≥N−B, a subsequent clean source
restriction of cost t and incidence I′ must therefore satisfy
3N−I′≤4(B+t). A native extraction contradicts the fibre only if it
reverses this inequality on that same paid fibre. Neither a sparse
recovery relation nor an unspecified bounded generator mean supplies it.

**What changed and what remains.** Genericity, alignment, row codegree,
reverse-degree bounds and bounded coupling are not premises. Linear
codes with special cancellations, including graphic difference codes,
are included. The exact core reduction holds at arbitrary support size;
only its inexpensive payment uses bounded maximum support. The full
nonlinear question and linear generators of mean at least three remain
open. Bounded recovery degree is a different property, as section 30
shows. The [fixed exact controls](../tools/diagonal-calibration/README.md#arbitrary-coefficient-source-controls)
check actual coefficient ranks and recovery, not matching ranks.

## 29. The repaired completion rule fails at window three

Astra, 14 November 2026. Status: **exact finite certificate with written
argument, not Lean-verified**. This closes the specific rule (26d), not
the full Shannon question. The first control already decides it; no LP
or further host search was run.

Take d=4 and ρ(r)=[4]∖{r}. Then g(A)=4|A| for proper A and g([4])=15.
For example, with indices zero through three,

  F_{ {0,1} } ∩ F_{ {1,2} } ∩ F_{ {1,3} } ∩ F_{ {0,2,3} }
    ={(1,1)}

has inclusion–exclusion budget zero. The exact minimum/clipping rule
of (26d), including **all** 167 nonempty antichain presentations, has
49 intersection sets and simplifies to

  h_*(X)=|X|−1_{X contains a diagonal cell}.             (29a)

The [finite checker](../tools/diagonal-calibration/completion_window3_counterexample.py)
verifies the following complete certificate: every
clipped budget is at least |F|−1; every discounted intersection meets
the diagonal; each diagonal singleton has budget zero; and the empty
set has budget zero. These facts prove (29a) on every subset by the
envelope formula: buy one diagonal singleton when present, and use
unit costs otherwise.

Two distinct diagonal singletons have h_*-value zero while their union
has value one, violating submodularity. Recovery fails too: the union H
of rows 1,2,3 has h_*(H)=11, whereas H∪C₀ adds the cell (0,0) and has
value 12. Nevertheless h_*(V)=15 equals the order value.

This host is **order-tight and entropic**, so the failure again proves
no Shannon/order gap. Let its twelve off-diagonal cells be independent
and impose one sum-zero relation on the four diagonal cells. The other
three rows determine the missing diagonal entry of each column, so this
is a code of size q¹⁵ for every alphabet size q≥2. The order expression
is 4+4+4+3=15 in every row order, giving the matching Shannon upper bound.
Its true entropy profile is |X|−1_{X contains all four diagonal cells};
it attains h(F_A)=g(A) for every row set A. The proposed rule has turned
a four-way parity dependence into a false discount on every nonempty
diagonal subset. The natural minimum/clipping repair is therefore
retired; no universal entropy inequality follows from its failure.

## 30. Sparse recovery and cheap circuits need not give sparse generators

Astra, 14 November 2026. Status: **written proof using classical graph
existence, not Lean-verified**. This is a limitation of a proposed native
extraction, not a whole-row or tape construction. No novelty is claimed
for the cycle-code facts.

Let Γ be a finite connected r-regular simple graph, r≥3, with N edges
and girth g. Orient its edges arbitrarily. Over any field, let C be the
kernel of its signed vertex-edge incidence matrix. A spanning tree
shows that the matrix has rank |V(Γ)|−1, and hence

  K=dim C=N−|V(Γ)|+1=(1−2/r)N+1.                       (30a)

At either endpoint, the zero-divergence equation recovers an edge from
the other r−1 incident edges. Choose one endpoint for each recovery;
its reverse recovery degree is at most 2(r−1). Every nonzero codeword
has support containing a cycle: an acyclic nonempty support has a leaf
where zero divergence forces its sole nonzero edge coefficient to
vanish. Therefore its weight is at least g.

Each column of **any** full-rank generator is a nonzero codeword. Thus
its total source incidence I obeys

  I/N≥gK/N.                                           (30b)

Connected r-regular graphs of arbitrarily large girth exist for every
fixed r≥3: [Erdős–Sachs, *Reguläre Graphen gegebener Taillenweite mit
minimaler Knotenzahl* (1963), Satz 2](https://www.renyi.hu/~p_erdos/1963-16.pdf),
p. 257; take a connected component if needed. At fixed r, recovery
degree stays bounded while the minimum mean generator support tends
to infinity. By choosing r large first, the rates can be arbitrarily
close to one as well. Constants depend on that choice of r.

**Linear advice cannot make this cheap.** A nonempty fibre of at most
t linear advice symbols is an affine translate of a subcode of
dimension K′≥K−t, still with minimum nonzero weight at least g. Every
generator of its translation space therefore has mean support at least
g(K−t)/N. To lower that mean to M one must pay

  t≥K−MN/g.                                           (30c)

This concerns linear/affine advice, not arbitrary nonlinear fibres.

**Even linear-size encoding is possible.** Choose the cotree edge flows
as K independent source values. Compute their divergences b_v at all
vertices, then subtree sums s_v=b_v+Σ_{children u}s_u in a rooted
spanning tree. Orient tree edges from child to parent and set that flow
to −s_v. Every nonroot divergence is zero; the root is zero because
Σ_v b_v=0. This gives a bounded-fan-in arithmetic encoding circuit with
O(N) gates (XOR gates over F₂), despite (30b). Each source enters its
two endpoint sums, and each subtree sum feeds its parent and one output,
so bounded fanout can be retained. This counts arithmetic, not tape
movement or the delivery of values to those gates.

**Native scope.** Bounded read-degree alone, even combined with a
linear-size linear encoding circuit, cannot supply a source basis of
bounded mean support after an inexpensive linear reveal. These graphs
have not been given a fixed-window balanced grid labelling or realized
as native tape cones. Any native extraction must use an additional
property of that geometry or paid computation. Moreover an unspecified
finite mean-support bound would not suffice for (28h): it must lie
below three by a fixed margin, or supply another core-deficit premise.

## 31. Shift covariance: existing bounds and the native gap

Fable and Astra, 14 November 2026. Fronts D0/D2/D4. The algebra in the
original proposal is correct, but the commuting and cut-shift cases are
already covered by Paper 17. The claim that unit-speed tape motion supplies
their premises is withdrawn. Statements below distinguish those existing
results from the written native countercontrol; no new machine exclusion
or novelty claim is made.

**31.1 (commuting blocks; existing flag theorem).** In the host equation
x_r=Σ_i Φ_{r,i}y_i, where x_r is column r and y_i is row i as a column
vector, pairwise commuting blocks give dim C≤d(d+1)/2 over every field,
with no restriction on helper rows or window. This is explicitly
[Paper 17, Corollary “One triangularizable side”](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/order.tex),
a written corollary of its formal flag bound FL.

For clarity, extend the field to its algebraic closure, preserving the
dimension of the linear code, and choose G making Λ_{r,i}=G⁻¹Φ_{r,i}G
upper triangular. Put Z=G⁻¹XG^{−T} and (A_{χψ})_{ri}=(Λ_{r,i})_{χψ}.
The transformed equations are exactly

  row_χ(Z)ᵀ = Σ_{ψ≥χ} G⁻¹ A_{χψ} G col_ψ(Z).

Reveal Z[a,b] for a≤b. Descending in χ, every column ψ≥χ is known, so
the equation determines row χ. This is an injective projection onto
d(d+1)/2 entries. When the blocks are simultaneously diagonal, Zᵀ
(rather than Z in the original convention) is a window-one whole-row
code. Twisted-swap Theorem 4, with its arbitrary U_g and nondegeneracy
premises, is not the corresponding citation.

Commutation can be weakened to two compatible flags: P⁻¹Φ_{r,i}Q all
upper triangular, with independent P and Q. Compatible partial flags
with block sizes s_j give dim C≤(d²+Σ_j s_j²)/2 by the same descending
block argument. These strengthenings are also already instances of FL.

**31.2 (cyclic and physical shifts; existing half bounds).** A cyclic rule

  X[c,r]=Σ_m α_m(r) X[i_m(r),c+j_m(r) mod d]

has commuting shift-polynomial blocks. Its exact pairing bound is also
formalized directly by Paper 17's
`IsClassUniformCode.two_mul_finrank_le_of_const`. Offsets, helper rows
and coefficients may depend on r, but not on c.

Physical row boundaries do not invalidate the conclusion for a linear
rule with that position independence. A stream starting at address id+s,
0≤s<d, contributes at running position c

  α(r)(1_{c+s<d} X[i,c+s] + 1_{c+s≥d} X[i+1,c+s−d]).

Writing (T_e y)[c]=y[c+e] when the index is in range, and zero otherwise,
this is α(r)(T_s y_i+T_{s−d} y_{i+1}); omit the zero second term at s=0,
and zero-pad source rows outside the array (or keep all streams inside it).
Thus even phases varying with stream and r give the one-class line rule

  X[c,r]=Σ_i Σ_{j=0}^{d−1} A_i[r][j−c] X[i,j].

[Paper 17, the line form of TP](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex)
gives dim C≤d(d+1)/2 for this entire Toeplitz span, despite its
noncommutativity. Its formal coefficient adapter is
`isLineUniformCode_of_coeff`, and its bound is
`IsLineUniformCode.two_mul_finrank_le` in
[Line.lean](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/lean/SwapRigidity/Line.lean).
No phase-size assumption or alignment payment is needed for this model.

The specialization of that proof is short. Let T shift each source row
left with zero padding and C′=C∩T⁻¹C. Then dim C′≥2 dim C−d². If the
first column of X∈C′ is zero, comparison of the rules for TX at c and X
at c+1 gives X[c+1,r]=X[c,r+1], where X[c,d]=0. Following anti-diagonals
to the zero first column or zero right boundary gives X=0. Hence the
first-column projection on C′ is injective, dim C′≤d, and the bound follows.

There is a further existing distinction: the **source** must be a linear
subspace for this intersection argument, but the shared decoders need not
be linear. [Capacity and Composition of Shared Transposition Decoders](../../Capacity-and-Composition-of-Shared-Transposition-Decoders/paper/sections/appendix-set-capacity.tex),
Theorem “Deterministic line rules on linear sources”, formalizes the line
extension as `IsDeterministicLineCode.two_mul_finrank_le`; its deterministic
translate lemma does the same on a cycle. Those results do not apply to
arbitrary advice fibres, or even arbitrary affine sources, without further
premises. Nonlinearity of the decoder alone is therefore not a new case
when the code is a subspace.

Two other meanings of “one phase” are also settled. With one global
phase σ(c)=c+s mod d, all helpers of row c lie in source column σ(c).
Permuting source columns by σ makes each row a function of its own
column. The upper-triangle reconstruction proves |C|≤q^{d(d+1)/2} for
**arbitrary nonlinear codes over any finite alphabet**. With instead one
fixed interval mask and arbitrary cyclic shifts, coefficients constant
on its two pieces form the broader two-class TP family, bounded by
d²/2+d. The algebra generated by a shift and a mask can be much larger
than either direct decoder span; its size does not produce a counterexample.

**31.3 (a native control, and the cost of literal covariance).** Unit speed
in time does not mean unit stride between appends. For even input length N,
a four-phase oblivious transducer visits positions

  2k, 2k+1, 2k, 2k+1

and appends only on the second and third visits, then advances to 2k+2.
It outputs adjacent pairs in reverse order in 2N+O(1) steps, with fixed
alphabet, fixed states and no work tape. A parked work tape may be added.
There are no data-dependent moves. For N=d², even d≥4, the read position
within a row is c xor 1, not c plus one common offset, including far from
the row ends. This is a transduction control, **not a transposer**.

The failure cannot be repaired cheaply by replacing this map with an
affine unit-shift-equivariant map in the same coordinates. Here is a
written proof, not a new Lean formalization. On F^d set
(Sv)_c=v_{c+1 mod d} and (Pv)_c=v_{c xor 1}. The kernel of PS−SP consists
exactly of vectors constant on the even positions and constant on the
odd positions: its equations are v_{c+2}=v_c, in every characteristic.
Thus rank(PS−SP)=d−2. On d rows put F₀=I_d⊗P and R=I_d⊗S. Any linear
map A commuting with R satisfies

  d(d−2)=rank[F₀,R]=rank[F₀−A,R]≤2 rank(F₀−A).        (31a)

Over F_q, suppose an arbitrary advice function with M possible values
selects affine maps Ax+v with AR=RA. If each selected map agrees with F₀
on its entire fibre except at at most z output coordinates fixed for
that advice value, that fibre is contained in an affine solution set
of codimension at least d(d−2)/2−z. Covering all q^N inputs gives

  log_q M + z ≥ d(d−2)/2 = N/2−d.                    (31b)

The advice need not be linear. The ignored coordinates may vary between
advice values, but not within one value without further accounting.
This only rules out cheap **literal unit-shift affine replacement** for
this computation. The pair swap commutes with S², so coarsening, periodic
classes, other bases or flag arguments are not ruled out. Neither are
nonlinear replacement decoders or correctness-dependent normal forms.

**31.4 (the remaining target).** B1 supplies bounded helper-row spread,
not a stride, a common coefficient pattern, or a cheap decoder-change
invoice. Its cuts fix records; their values can still select different
functions at different positions. Work-return paths also compose maps
with distinct time changes. None of this is removed by unit head speed.

Paper 17's actual Problem 9.4(b) is **cyclic**. Its open cases drop the
linear-subspace source premise or allow functions varying with c, or both.
Its shared-decoder bound on linear sources is explicitly settled there.
Physical carries alone are not its missing case. Problem 9.4(a), separately,
asks for a paid transfer to real
cone decoders. Its existing affine entry-change bound is useful only
after proving a count on the actual selected fibre. A fixed transition
table or cheap revealed word does not itself prove that count.

The proposed shift/projection-algebra search therefore stops without
an experiment. A next D2 attempt must specify an unresolved source/recovery
class (and keep its native tie conditional), or prove a genuinely new
native extraction premise with its payment. These corrections do not
weaken B1 or the sparse-generator theorems in section 28.
