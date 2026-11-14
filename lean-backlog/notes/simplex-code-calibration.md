# Simplex-code calibration

Hans Brende and GPT-6 Astra, 13 November 2026.

**Status: written proofs; not Lean-formalized.** This note supplements the
projective construction in [Section 9 of the row-spread note](row-spread-of-cones.md#9-rates-at-growing-windows-simplex-codes-fable-13-november-2026).
A random helper relation supports the same limiting rate $2/3$ at a smaller
window exponent. The window still grows with dimension, so this does not
settle the fixed-window question or construct a tape transposer.

## 1. A random relation with almost all cells in triangles

A whole-row relation assigns each column $c$ a set $\rho(c)$ of helper rows.
A code $C\subseteq A^{[d]\times[d]}$ is compatible if every coordinate in
column $c$ is recoverable from the entries in those rows. Its rate is
$\log_{|A|}|C|/d^2$.

**Theorem 1 (random triangle codes).** There is a sequence of whole-row
relations $\rho_d$ such that every column's helper count and every row's
number of occurrences as a helper are

$$ (1+o(1))d^{1/3}\log d,$$

uniformly over rows and columns. For every finite alphabet $A$ of size at
least two there are compatible codes of rate at least $2/3-o(1)$, with the
error independent of $A$. Every coordinate is either constant or is
recovered from two other coordinates in its allowed rows. The construction
works directly over $A$, without subdividing entries into lanes.

Precisely, for every $\eta>0$, all sufficiently large integers $d$ admit
such relations with helper counts at most $(1+\eta)d^{1/3}\log d$ and codes
of rate at least $2/3-\eta$ for every finite $A$. Both the relation and the
choice of coordinate triples can be independent of $A$.

## 2. Proof

Write $\ell=\log d$ and $p=d^{-2/3}\ell$. For sufficiently large $d$, choose
a random bipartite graph $G$ on $d$ rows and $d$ columns, with independent
edge probability $p$. Set $\rho(c)=N_G(c)$. An edge means that row $r$ is
available to column $c$; the coordinates we will pack are the **nonedges**.

We first establish three simultaneous properties with probability tending
to one. Set $\delta=\ell^{-1/4}$.

1. Every row and column has degree $(1\pm\delta)dp$. This follows from
   the binomial Chernoff bound and a union bound over $2d$ vertices:
   $\delta^2dp=d^{1/3}\ell^{1/2}\gg\log d$.
2. Every pair of distinct rows, and every pair of distinct columns, has at
   most $K=7$ common neighbours. A fixed count has distribution
   $\operatorname{Bin}(d,p^2)$. A union bound over pairs and eight-element
   common-neighbour sets bounds the failure probability by
   $O(d^2(dp^2)^8)=O(d^{-2/3}\ell^{16})=o(1)$.
3. For every nonedge $(r,c)$, the bipartite graph between
   $R=N_G(c)$ and $S=N_G(r)$ has
   $E_{r,c}=(1+o(1))d^2p^3=(1+o(1))\ell^3$ edges, uniformly in $(r,c)$.
   To prove this, expose only the edges incident to $r$ or $c$, including
   the event that $(r,c)$ is a nonedge. The remaining edges in $R\times S$
   are independent Bernoulli variables. Whenever the two exposed degrees
   satisfy property 1, their conditional edge-count mean is
   $|R||S|p=(1+O(\delta))\ell^3$. The conditional probability of a relative
   deviation greater than $\delta$ is at most
   $2\exp(-c_0\delta^2\ell^3)$ for an absolute $c_0>0$ and all large $d$.
   Since $\delta^2\ell^3=\ell^{5/2}\gg\log d$, a union bound over $d^2$
   cells proves the assertion. This conditioning is only on the two
   exposed neighbourhoods, not on the global events in properties 1 or 2;
   intersecting the three high-probability events afterwards is valid.

Fix a graph with these properties. Form a three-uniform hypergraph
$\mathcal H$ whose vertices are the nonedge cells. Its edges are triples

$$\{(r_1,c_1),(r_2,c_2),(r_3,c_3)\}$$

with distinct rows and columns, with all three displayed cells nonedges
and all six cross cells $(r_i,c_j)$, $i\ne j$, edges of $G$. Each such
triple allows every cell to read the other two.

For a fixed nonedge $(r,c)$, its incident hyperedges correspond bijectively
to induced two-edge matchings in the graph on $R\times S$ from property 3.
Indeed, the two matching edges are cross cells, and their two missing
opposite corners are the other two vertices of the hyperedge. The
remaining four required cross edges are supplied by $R=N_G(c)$ and
$S=N_G(r)$.

That graph has maximum degree at most $K$: a row's degree in $S$ is a
common-neighbour count with $r$, and a column's degree in $R$ is a
common-neighbour count with $c$. In any bipartite graph with $E$ edges and
maximum degree $K$, the number $I$ of induced two-edge matchings satisfies

$$\binom E2-K(K-1)E\ \le I\le\binom E2.$$

To see the lower bound, at most $(K-1)E$ unordered edge pairs share a
vertex. A disjoint pair that is not induced has a cross edge; summing over
that cross edge counts at most $(K-1)^2E$ such pairs. Multiple counts only
strengthen this upper bound on the excluded pairs. Therefore every
hypergraph vertex has degree

$$\deg_{\mathcal H}(r,c)=(1+o(1))\ell^6/2,$$

uniformly over the nonedges.

The codegree of two distinct hypergraph vertices is at most $K^2$. It is
zero if they share a row or column, or lack either required cross edge.
Otherwise, for vertices $(r,c),(r',c')$, a third vertex $(s,t)$ must have

$$s\in N_G(c)\cap N_G(c'),\qquad
t\in N_G(r)\cap N_G(r').$$

There are at most $K^2$ choices, and requiring $(s,t)$ to be a nonedge can
only reduce the count. Thus $\mathcal H$ has asymptotically equal minimum
and maximum degrees tending to infinity, and maximum codegree negligible
relative to its maximum degree.

The [Pippenger–Spencer theorem, *Asymptotic behavior of the chromatic index
for hypergraphs*, JCTA 51(1), 24–42 (1989)](https://doi.org/10.1016/0097-3165(89)90074-5)
gives an edge colouring with $(1+o(1))\Delta_{\mathcal H}$ colours. Since
the vertex degrees are $(1+o(1))\Delta_{\mathcal H}$, the largest colour
class is a matching covering all but $o(N)$ of the $N$ nonedge cells.
Property 1 gives $N=(1-o(1))d^2$.

Identify $A$ with the cyclic group of order $|A|$. On each matched triple
impose one sum-zero constraint; fix every other coordinate to zero,
including the edge cells. If the matching has $\nu$ triples, then
$3\nu=(1-o(1))d^2$ and the code has exactly $|A|^{2\nu}$ words. Its rate
is $2\nu/d^2\to2/3$. Each nonconstant coordinate is recovered from its
two companions, whose rows are allowed by the triple's six cross edges.
All packing and error estimates are independent of $A$. Since a suitable
graph exists for every sufficiently large integer $d$, this proves the
stated quantifiers. ∎

## 3. What this changes

The maximum helper count satisfies
$\log w_d/\log d\to1/3$. At this exponent the rate $2/3$ exceeds
$1/(2-1/3)=3/5$, so the formula through the projective examples cannot be a
general upper bound. More directly, the projective plane gives limiting
rate $2/3$ at exponent $1/2$; the random construction attains the same
rate at exponent $1/3$.

This remains a growing-window result. It supplies neither a rate above
one half for a fixed window nor a counterexample to the common-deficit
condition used in the native machine reduction. It provides a calibration
that any proposed growing-window capacity bound must respect.

## 4. Finite projective controls

The projective field $\mathbb F_q$ and the coding alphabet are independent.
The following constructions use a cyclic group for an arbitrary finite
alphabet, or the field's additive group when linearity is desired. Their
stated dimensions are literal linear dimensions over every coding field.

| Projective plane | $d$ | Window | Free incident cells | Nonincident cells | Best disjoint-clique code dimension |
|---|---:|---:|---:|---:|---:|
| Fano, $q=2$ | 7 | 3 | 21 | 28 | 39 |
| $q=3$ | 13 | 4 | 52 | 117 | 130 |

**Proposition 2 (projector obstruction).** In $\operatorname{PG}(m-1,q)$,
with $m\ge3$, let $N=dq^{m-1}$ be the number of nonincident cells. A packing
of $t$ disjoint projective simplexes satisfies

$$\operatorname{char}(\mathbb F_q)\nmid t\quad\Longrightarrow\quad N-mt\ge m.$$

*Proof.* Associate to a cell $([v],[\ell])$ with $\ell(v)\ne0$ the
rank-one matrix $P(v,\ell)=v\ell/\ell(v)$. It is independent of the chosen
representatives. The projectors of a simplex sum to $I_m$, because its
normalized hyperplane covectors are dual to its basis points.

The sum over all nonincident cells is zero. For each fixed point change
basis to $v=e_1$; the normalized covectors are $(1,x_2,\ldots,x_m)$.
Their first-coordinate sum is $q^{m-1}=0$ in the field, and each other sum
is $q^{m-2}\sum_{x\in\mathbb F_q}x=0$. Here $m\ge3$ is essential.
The $N-mt$ uncovered rank-one projectors therefore sum to $-tI_m$.
When $t$ is nonzero in the field this has rank $m$, so at least $m$
projectors remain. ∎

For the Fano plane, nine triangles would leave one cell, contradicting
Proposition 2. Eight triangles and two mutually helping pairs partition
all 28 nonincident cells. One parity constraint on each of these ten
blocks, with the 21 incident cells free, gives dimension $49-10=39$.
For $q=3$, an explicit partition into 39 triangles gives dimension
$52+2\cdot39=130$. The certificates are in
[the reproduction folder](../tools/simplex-calibration/README.md).

These disjoint-clique baselines are optimal within that family. In a
mutually helping set of $s$ nonincident cells, the matrix
$[\ell_j(v_i)]$ is nonsingular diagonal but factors through
$\mathbb F_q^3$, so $s\le3$. A gadget containing a nonincident coordinate
loses at least one alphabet symbol, since deleting that coordinate is
injective on its code. Thus at least $\lceil28/3\rceil=10$ losses are
needed in the Fano plane, and at least $117/3=39$ in the next plane.
This argument does not bound codes that couple different gadgets.

**Vector baseline.** Each Fano nonincident cell belongs to three simplexes.
Give each entry three binary lanes, assign each nonincident entry's lanes
to these simplexes, and put one parity constraint on the three assigned lanes of
each simplex. There are 28 disjoint checks on 147 bits; incident-entry
lanes remain free. The resulting binary linear code has dimension 119,
or $\log_8|C|=119/3=39\tfrac23$ normalized entries. Its entry width is
exactly the canonical $b(7)=3$. This is the fractional clique-cover
construction described and credited in
[the row-spread note](row-spread-of-cones.md#9-rates-at-growing-windows-simplex-codes-fable-13-november-2026),
not a new coding mechanism or a scalar $\mathbb F_8$-linearity claim.

## 5. Scalar Fano optimality over two fields

**Computer-assisted result; not Lean-verified.** The largest dimension of
a scalar $\mathbb F_2$-linear or $\mathbb F_3$-linear whole-row code on the
Fano relation is 39. The certificates and their Boolean encoders are
independently checked; this statement does not assert nonlinear optimality
or optimality over other fields.

Here is the reduction checked by the certificate. Freeze the 21 incident
coordinates. On the remaining 28 cells, a fitting matrix $H$ has diagonal
one and $H_{(r,c),(s,t)}=0$ whenever $s\notin\rho(c)$ and the two cells
differ. The minimum rank of such a matrix is the codimension of a largest
linear code: recovery equations give the rows of $H$, and $\ker H$ gives
the converse construction. Coupling the incident coordinates cannot
improve the full dimension beyond 21 plus this residual optimum.

An explicitly checked set $J$ of eight cells induces a directed acyclic
graph. Hence every fitting $H[J,J]$ is invertible: it is triangular with
unit diagonal in a topological order. If $\operatorname{rank}H\le9$, its
row space has a basis beginning with the eight rows indexed by $J$.
Subtracting their interpolation on columns $J$ makes every additional
basis row vanish there. Padding by zero when necessary yields

$$H=UV,\qquad U[J,:]=[I_8\ 0],\qquad V_{\mathrm{extra},J}=0,$$

where $U$ has size $28\times9$, $V$ has size $9\times28$, and
$V_{\mathrm{extra},J}$ is its ninth row restricted to columns $J$. Conversely such
a factorization has rank at most nine. This normalization selects no
particular ninth pivot and loses no possible fitting matrix.

The binary formula imposes exactly these conditions and the fitting
constraints, using explicit AND/XOR gates. The ternary formula uses two
Boolean indicators per scalar and checked addition/multiplication tables
modulo three. LRAT certificates derive contradiction in both cases; a
separate Python checker replays each positive-hint reverse-unit-propagation
step and rejects unsupported RAT steps. A rank-ten fitting matrix from
Section 4 satisfies both corresponding encodings and is independently
checked by modular elimination. Thus each minimum rank is ten, and the
full code dimension is $49-10=39$.

The small binary certificate is stored in the reproduction folder. The
larger ternary trace was also replayed successfully; the folder supplies
its exact generator, solver command and receipt, rather than the large
trace itself. These are computer-assisted proofs with written encoding
arguments, not Lean theorems.

The eight-cell acyclic witness gives the weaker bound
$\log_{|A|}|C|\le41$ for every alphabet and nonlinear code. The later
[Fano Shannon certificate](fano-shannon-certificate.md) sharpens the
unrestricted bound to $119/3$ and proves that this is the full Shannon
value. The existing three-bit construction attains it: alphabet-eight
capacity is exactly $8^{119/3}=2^{119}$. The new upper certificate is
computer-assisted, independently replayed, and not Lean-verified.
The $13\times13$ disjoint-clique baseline remains only a lower bound for
unrestricted codes; no larger plane was tested in that Shannon pass.
