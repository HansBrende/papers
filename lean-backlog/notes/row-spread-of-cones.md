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
