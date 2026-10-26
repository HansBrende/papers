# TCP and Information-Cheap Depth Reduction

Hans Brende and GPT-6 Astra (OpenAI), October 2026.

Depth-reduction memo to *Curved Motion, Depth Reduction, and Storage Codes for
Matrix Transposition on Tapes*, by Hans Brende and Claude Opus 5.5 [1].
**Status: written proof; not formalized in Lean.** No external priority claim
is made. Hans Brende directed the research and publication; GPT-6 Astra
developed the arguments and prepared this memo.

## The result

Here **TCP means the trajectory cut problem** of Paper 4. The following two
universal statements are equivalent:

1. TCP holds for every fixed number of walks.
2. Every fixed resource class of linear-time oblivious native computations
   admits constant-depth revelation sets with arbitrarily small joint
   entropy per input bit, when revelations consist of whole step values.

The equivalence still holds with whole state/work-symbol fields, with depth
required only from output steps, and after the precise local argument pruning
defined below. It also holds when the machine class is restricted to
bijections with linear-time native inverses and logarithmic visited work span.

Thus replacing the number of revealed steps by the information in their
values does not remove the universal TCP obligation in these models. The
negative direction is conditional: **if TCP fails**, one fixed, computationally
easy native bijection requires a positive linear amount of genie entropy at
every fixed depth, eventually at every input length. Neither TCP nor the
linear-time transposition question is decided here.

## Definitions and quantifiers

Use Paper 4's native model: fixed finite control and alphabet, a fixed number
of work tapes initially blank, all heads initially at the origin, unit head
moves, two-way read-only raw input, and append-only output with at most one
bit appended per transition. Write $L$ for input length. At canonical matrix
sizes, $L=d^2b(d)$, where $b(d)=\max(1,\lceil\log_2 d\rceil)$.

For $k$ integer walks with increments in $\{-1,0,1\}$ on $T$ time vertices,
the walk DAG has state edges $t\to t-1$ and previous-visit edges on each
walk. Edges are identified by endpoints. A previous visit at the immediately
preceding time is already a state edge; every other previous-visit edge is
a **long hop**. A cut has long-hop depth at most $D$ when every surviving
path contains at most $D$ long hops. The assertion $\mathrm{TCP}(k)$ is

$$
\forall\eta>0\ \exists D\ \forall T\ \forall\text{ such }k\text{-walks},
\quad \exists F:\ |F|\le\eta T
\text{ and the cut }F\text{ has long-hop depth at most }D.
$$

Let $\mathrm{TCP}_{\mathrm{all}}$ mean this assertion for every fixed $k\ge1$.

For a native machine oblivious at length $L$, its halting time, head positions,
and output times are independent of the input bits. Its step value $v_t$
comprises its post-state, every written work symbol, and its appended bit
or the symbol for no output. Fix a width bound $\beta$ such that each whole
value can be encoded in $\beta$ bits. The dependency DAG points from a step
to its preceding state and previous work-cell writers. Raw input is a local
argument, not an additional time vertex.

A **whole-step genie** chooses a set $\Gamma$ of times and reveals
$G_\Gamma(X)=(v_t(X))_{t\in\Gamma}$. The choice may depend on the machine
and input length, but not on the realized input $X$. Revealing time $s$
blocks edges whose target is $s$. A surviving path may start at a revealed
vertex; all its later vertices must be unrevealed. **Full depth** counts
every edge, including state edges. Global depth bounds all surviving paths;
output-started depth bounds only paths starting at an appended output.

The information cost is the **joint Shannon entropy** $H(G_\Gamma(X))$ in
bits, with $X$ uniform on $\{0,1\}^L$. It is neither a sum of marginal
entropies nor a claim that the genie can be computed or compressed cheaply.

Define $\mathrm{INFO}_{\mathrm{whole}}$ as follows. For every pair of integers
$K\ge1$, $\beta\ge2$, and every $C,\epsilon>0$, there is a finite $D$ such
that every fixed native machine with $K$ work tapes and value width at most
$\beta$ has a threshold $d_0$ with this property: for every $d\ge d_0$ at
which it is oblivious, runs in at most $C(L+1)$ steps, and appends exactly
$L=d^2b(d)$ bits, some whole-step genie has global full depth at most $D$ and

$$
H(G_\Gamma(X))\le\epsilon L.
$$

The depth $D$ may depend on $K,C,\beta,\epsilon$, but **not** on the machine
or input length. The eventual threshold may depend on the machine. No uniform
algorithm for finding the genie is required. The version quantified over all
sufficiently large positive lengths, rather than just canonical lengths,
will have the same equivalence.

**Theorem I (universal equivalence; not formalized).**
$\mathrm{TCP}_{\mathrm{all}}$ holds if and only if
$\mathrm{INFO}_{\mathrm{whole}}$ holds. The variants specified after the
proof have this same equivalence.

## Proof: cuts give information-cheap genies

Assume $\mathrm{TCP}_{\mathrm{all}}$. Fix $K,C,\beta,\epsilon$, put
$C_0=\max(C,1)$, and choose

$$
\alpha=\min\!\left(1,\frac{\epsilon}{4\beta C_0}\right),
\qquad
Q=\max\!\left(2,\left\lceil\frac{4\beta C_0}{\epsilon}\right\rceil\right).
$$

Apply $\mathrm{TCP}(K)$ to obtain a cut of at most $\alpha T$ edges and
long-hop depth $D_0=D_0(K,\alpha)$. Reveal its target times and the times
$Q-1,2Q-1,\ldots<T$. There are $\lfloor T/Q\rfloor$ of the latter.
Every surviving path has at most $D_0$ long hops. Between them, a run of
state edges has at most $Q-1$ edges, even when its initial vertex is revealed.
Its full depth is therefore at most

$$
D=(D_0+1)Q-1.
$$

Entropy is at most encoded length, so for every $L\ge1$,

$$
H(G_\Gamma(X))
\le\beta|\Gamma|
\le\beta(\alpha+1/Q)T
\le\epsilon(L+1)/2
\le\epsilon L.
$$

This is Paper 4's cut-to-genie conversion with its periodic state cuts [1],
applied to arbitrary walks under TCP. It does not require bijectivity or a
particular input law for the encoded-length bound.

## Proof: a TCP failure gives a native entropy obstruction

We prove the following stronger conditional statement.

**Theorem H (conditional obstruction; not formalized).** If
$\mathrm{TCP}(k)$ fails for some fixed $k$, there are fixed $K,C,\beta$,
$\delta>0$, and one uniform oblivious native machine $M$ with $K$ work
tapes, value width at most $\beta$, and runtime at most $C(L+1)$, such that:

- At every length $L$, $M$ computes a bijection of $\{0,1\}^L$ and has a
  uniform native inverse. Both take $O(L+1)$ time and visit total work span
  $O(\log(L+2))$, excluding input and output tapes.
- For every fixed $D$, at all sufficiently large lengths $L$, every admissible
  whole-step or whole-field genie of output-started full depth at most $D$
  has $H(G(X))>\delta L$, even after the local pruning defined below.

The machine and $\delta$ are fixed before $D$ and $L$; the eventual length
threshold may depend on $D$.

### Finite witnesses with a paid, uniform search

Fix a positive rational $\eta$ smaller than a TCP failure rate. For every
$j\ge1$ there is a finite $k$-walk instance on $m\ge1$ vertices for which every
cut of long-hop depth at most $j$ has more than $\eta m$ edges. This is a
decidable finite property: enumerate edge subsets and check the remaining
finite DAGs. Encode the walks, translated to start at zero, by their $m-1$
vector moves and a final zero vector. The alphabet $\{-1,0,1\}^k$ is fixed.

One fixed multitape search program enumerates witnesses for stages
$j=1,2,\ldots$. On success, it copies the word and metadata into an inactive
persistent slot, then changes an active-slot flag in one transition. Two
slots suffice, and an interrupted copy cannot destroy the preceding commit.
Word markers and metadata use separate tracks or tapes, so playback does
not repeatedly traverse a header.

On an input of length $L$, first count its length and return the input head
to zero. A binary counter returned to its low end has amortized linear
increment cost; the reset uses an equally amortized countdown. Place
external guards at distance $\ell=\operatorname{bitlength}(L)$ on every
search tape, including certificate scratch and both slots. Simulate exactly
one search transition per raw input position, ignoring the bit value.
Stop before interpreting a guard cell; on an early guard, preserve the last
commit and finish the input sweep in an idle mode. All candidate checking
and partial copying is metered by this $L$-transition clock.

The search sees its ordinary blank tapes until a guard stops it. Under TCP
failure, the unguarded prefix through any fixed stage $j$ takes some finite
time $t_j$ and span $s_j$. Eventually $L>t_j$ and $\ell>s_j$, so that
commit is reached. Consequently the last committed stage $j(L)$ tends to
infinity, while its explicitly stored word has length $m=O(\log(L+2))$.
No efficiency bound for witness discovery is assumed. All search, setup,
arithmetic, and input resets cost $O(L+1)$ time and logarithmic work span.

### Replay with one fresh bit at every actual transition

Reserve $k$ replay tapes whose heads stay at zero during setup. Read the
selected word forward, moving these heads by its vector moves, then backward
with negated moves to return them to zero. Controller work parks these heads.
Use an origin-return binary countdown for

$$
R=\left\lfloor\frac{L}{hm}\right\rfloor
$$

cycles. Its total borrow work is $O(R+\log(R+2))$, not a full-width scan
per cycle. Including marker turns, all returns, and controller transitions,
the untruncated replay length $S_0$ satisfies

$$
S_0\le aRm+b\log_2(L+2)+c
$$

for fixed implementation constants $a\ge1,b,c\ge0$. Fix the tape count
$K$ and playback routine first, then choose a fixed integer $h\ge4a$.
Computing $R$ and preparing its counter occurs before replay, using ordinary
binary tape arithmetic. Eventually

$$
S_0\le L/2,\qquad Rm\ge L/(2h).
$$

Add a tag bit to the state and every work symbol. All tags are zero during
setup. Rewind the raw input to zero before replay. At **every actual replay
transition**, including countdowns, turns, and pauses, read the next fresh
bit $x_r$ and set

$$
z_r=x_r\oplus\bigvee_{p\in A_r}z_p.
$$

Here $A_r$ is the set of distinct earlier replay times supplying the old
state or scanned work-symbol tags; setup and first-visit tags are zero.
Write $z_r$ into the post-state and every scanned work-symbol tag, append
$z_r$, and advance the input head. The machine just ORs the fixed number
of available tags; duplicate predecessors need no runtime deduplication.

Public control and symbol components ignore the payload and tags. Their
transition lookup uses a fixed end-marker input argument, while the physical
input bit is used only for the tag update and an end guard. Thus tagging is
one fixed finite transition-table modification, not an unpaid simulation.
Every actual replay step is now an output step, with the same work-head
geometry as the public replay.

If the input ends early, halt without another append. Otherwise copy the
untouched suffix after the planned cycles. Missing witnesses and $R=0$ use
the identity map; small guard-truncated prefixes still use the same encoding.
The end guard ensures the time bound at every length. Eventually it never
interrupts replay, by the bound on $S_0$. The total work span is logarithmic:
search and arithmetic are guarded, and each replay head travels at most $m$
from zero before returning. The case $L=0$ emits the empty word.

### Inversion and joint entropy

The inverse runs the identical length-dependent public setup and replay.
On incoming bit $z_r$, it emits

$$
x_r=z_r\oplus\bigvee_{p\in A_r}z_p,
$$

then stores the **incoming $z_r$**, not the recovered $x_r$, in all current
tags. Induction keeps its tag configuration identical to the encoder's.
Copying the suffix completes inversion, including guard-truncated inputs.
The same time and space bounds hold. Thus the map on the full input cube
is a triangular bijection.

Under uniform input, the replay tags and copied suffix are jointly uniform.
In particular the tags at distinct replay times are independent fair bits.
Every whole post-state or written work-symbol field at replay time $r$
contains $z_r$ and otherwise only public, length-dependent data. Revealing
any nonempty collection of these fields at each time in a fixed set $A$
of replay times has entropy exactly $|A|$. Multiple fields at one time
contribute only one bit. Additional revelations elsewhere can only increase
joint entropy.

### Local pruning and field paths

A **whole-field genie** reveals complete post-state or written work-symbol
fields. An argument edge is blocked when its target field is revealed.
Allowing appended output fields as revelations also preserves the conclusion.

An admissible **local pruning** replaces each field's local expression by
an exact expression using a subset of its original predecessor fields,
its current raw input symbol, and public constants. It must agree on all
attained local tuples, before conditioning on a realized genie value. It
cannot add ancestors, projected helpers, or computations from other steps.

For an internal replay predecessor $p\in A_r$, the tuple consisting of
$x_r$ and the distinct predecessor tags has full product support. Hold
$x_r$ fixed, set every other predecessor tag to zero, and toggle $z_p$.
The current $z_r$ changes. Therefore every exact local expression for
every field produced at $r$ must retain at least one field from predecessor
time $p$. Duplicate fields from the same time are a single group; the
claim does not require them to be independently variable.

Consequently any internal time path lifts, edge by edge, to a field path
after admissible pruning. Start at the appended output field; at each step
choose a retained representative of the next predecessor-time group.
Every reached field carries its own time's tag and has the same essential
predecessor groups, so this process continues for the entire path.

Let $A$ now denote all times where a genie reveals anything. Enlarging its
revelations to whole steps at those times blocks at least as many paths.
An internal time path avoiding $A$ after its first vertex therefore lifts
to a field path avoiding the original revelations. The first vertex may
be revealed, in accordance with Paper 4's convention. Since every replay
time appends, output-started depth already controls every such internal path.

### The localized cut count

In one forward window, represent logical time $t$ by an actual boundary
$f(t)$, with all designated heads at their logical positions throughout
$[f(t),f(t+1))$. A logical state edge lifts along the native state chain.
A logical long hop $u\to p$ lifts as

$$
f(u)\longrightarrow f(p+1)-1\longrightarrow\cdots\longrightarrow f(p).
$$

The first edge is an actual previous-visit edge: there was no intervening
logical visit, and the last visit in block $p$ was its final transition.
Pauses use the state edge. For coincident logical hops select one head.
An internal block-state edge belongs to at most one lifted state edge and
one next-return lift per designated head. A native long edge identifies
its logical endpoints. Thus lift congestion is at most $k+1$. Paths lift
to strictly decreasing native paths with at least as many long hops.
All lifts lie inside the forward window; different windows have disjoint
selected native edge sets. Earlier cycles cannot change an internal
consecutive-visit pair.

Let $B_L$ be the actual replay interval, and suppose a genie has surviving
output-started depth at most $D$. In each forward window, delete selected
native edges whose target lies in $A$. Pull the deletion back to logical
edges whose lifts meet it. A surviving logical path with more than $D$
long hops would lift to an internal native path of length greater than
$D$, and then to a surviving field path from an actual output. Hence the
logical cut has long-hop depth at most $D$.

Eventually $j(L)\ge D$, so each window requires more than $\eta m$
pulled-back edges and hence more than $\eta m/(k+1)$ deleted native
edges. Summing the $R$ disjoint selected edge sets gives more than
$\eta Rm/(k+1)$ deleted edges. Each native vertex has at most $K+1$
incoming deduplicated edges: the next state use and at most one next
visit per work tape. All these targets lie in $B_L$, so

$$
(K+1)|A\cap B_L|>
\frac{\eta Rm}{k+1}
\ge\frac{\eta L}{2h(k+1)}.
$$

The original revealed fields determine the tags at these distinct times.
Their joint entropy therefore satisfies

$$
H(G(X))\ge |A\cap B_L|>\delta L,
\qquad
\delta=\frac{\eta}{2h(k+1)(K+1)}>0.
$$

This charges revealed replay times once globally; it assumes neither
vertex-disjoint windows nor additive marginal entropies. Reveals outside
replay cannot block the selected internal paths. The constants were fixed
before $D,L$, proving Theorem H.

## Completing the equivalence and its variants

If $\mathrm{TCP}_{\mathrm{all}}$ fails, choose the one machine in Theorem H,
its fixed resource bounds, and $\epsilon=\delta/2$. Every fixed $D$
eventually violates the information bound, including at canonical lengths.
This contradicts $\mathrm{INFO}_{\mathrm{whole}}$ and proves Theorem I.

The same argument applies if the universal information assertion:

- requires depth only from output fields;
- permits whole-field revelations or the admissible local pruning;
- restricts machines to bijections with uniform linear-time native inverses
  and logarithmic visited work span; or
- uses all sufficiently large input lengths instead of canonical lengths.

These changes may be combined. For the positive direction, the preceding
whole-step cuts already bound global depth. Replacing each revealed step by
all its post-state and written work-symbol fields blocks the same time
dependencies and costs at most $\beta$ bits per selected time. Further
pruning only removes edges. The negative direction is already proved for
the strongest combination above. The equivalence is universal over resource
bounds; it does not preserve a prescribed resource triple or equate entropy
with cardinality for each individual machine.

## Consequences for Paper 4 and transposition

Paper 4's Theorem D combines a cheap depth-reduction hypothesis with a
separate index-coding lower bound for the induced transpose demands [1].
The present equivalence supplies a limitation on a proposed relaxation of
the first hypothesis. It is neither a replacement for Theorem D nor a
proof of its coding hypothesis. In particular, the conditional hard
computation is a bijection with a simple native inverse, not a transposer.

The remaining useful target is a demand-specific connection between the
computation, its revelations, and the resulting code. For an actual correct
oblivious transposer, Paper 4's cone lemma makes each genie fibre a storage
code for the actual transpose-demand relation. If every such fibre has size
at most $2^{(1-\rho)L}$, then

$$
H(X\mid G)\le(1-\rho)L,
\qquad H(G)=L-H(X\mid G)\ge\rho L.
$$

A genie of entropy at most $\epsilon L$ with $\epsilon<\rho$ would then
give a contradiction. This memo supplies neither that all-code bound nor
such a transpose-specific genie.

Arbitrary projections that discard the tags, separately computed helpers,
cross-step recomputation, changed schedules, conditioning-specific pruning,
and adaptive executions fall outside the revelation and pruning models
proved here. These remain possible directions for a different method.

## Reference and license

[1] Hans Brende and Claude Opus 5.5 (Anthropic), *Curved Motion, Depth
Reduction, and Storage Codes for Matrix Transposition on Tapes*, October
2026, pinned revision `d45b85ac335063dc60f7efc235076a505a411b6a`.
See [the decomposition, genie conventions, Theorem D, and long-edge conversion](https://github.com/HansBrende/papers/blob/d45b85ac335063dc60f7efc235076a505a411b6a/Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/decomposition.tex)
and [the trajectory cut problem](https://github.com/HansBrende/papers/blob/d45b85ac335063dc60f7efc235076a505a411b6a/Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/depth.tex).
Those source sections provide written proofs, not Lean formalizations.

This memo is licensed under CC BY 4.0; the
[full license text](../paper/LICENSE) is included with the parent paper.
