# Hosts without mutual triangles, and the soft form of the order bound

Claude Fable, with corrections and independent proof review by GPT-6 Astra,
14 November 2026. **Status:** Sections 1 and 3–5 are reviewed written arguments;
Section 2 records exact finite counts; Section 6 is numerical and heuristic.
None is Lean-verified. No literature novelty claim is made.
Tools: [host-probe](../tools/host-probe/).

An incidence host has points as rows, lines as columns, and all points of a line
as the helper rows of that column. The array need not be square. A cell (p, ℓ)
is *incident* if p∈ℓ; its self-recovery is trivial. Incident coordinates can be
adjoined independently when constructing a code, but need not be independent
in a particular code. We condition on them before studying the residual,
nonincident cells. Unless stated otherwise, H_v below contains only residual
cells in the helper rows of v's column.

Two residual cells (p, ℓ), (q, m) are *mutual* if q∈ℓ and p∈m. A *mutual
triangle* consists of three pairwise mutual residual cells. Entropies use one
fixed base; a unit-capacity coordinate has entropy at most one in that base.

## 1. An explicit code beyond pairing on the 3×3 grid

Take points (i,j)∈Z₃² and the six horizontal and vertical lines R_k and C_k.
This is a **9-row, 6-column array**, with 54 cells, 18 incident and 36 residual.
It has no mutual triangle: three distinct horizontal or vertical lines cannot
meet pairwise at three distinct points. Pairing gives exponent 18 on the
residual cells; their order bound is 23.

Write A_j[i,k]=X[(i,j),R_k] for i≠k and B_i[j,k]=X[(i,j),C_k] for j≠k.
Take free symbols S_j[i,k], T_i[j,k] and D[a,b], with the two displayed indices
in increasing order, in an abelian group of order q. Define

- A_j[i,k]=S_j[i,k] and A_j[k,i]=S_j[i,k]−D[i,k] for i<k;
- B_i[j,k]=T_i[j,k] and B_i[k,j]=T_i[j,k]−D[j,k] for j<k.

**Proposition.** These arrays form a whole-row code with q²¹ residual words,
for every integer q≥2.

*Proof.* The helper rows of R_k are (k,0),(k,1),(k,2). They contain row k of
every A_j and all of B_k. Opposite entries of B_k have differences D, so they
recover A_j[i,k] from A_j[k,i] and the appropriate signed difference. Exchanging
A and B gives recovery from the helpers of C_k. The nine S and nine T symbols
are upper entries of the word; the three D symbols are differences of opposite
entries. Thus all 21 parameters are recoverable, proving injectivity. ∎

Adjoin the incident cells freely to obtain q³⁹ full words. The later
[triangle-free Shannon certificate](triangle-free-shannon-gap.md) gives

\[
21\le \log_q |C_{\max,\mathrm{res}}|\le114/5<23,
\qquad
39\le \log_q |C_{\max,\mathrm{full}}|\le204/5<41.
\]

The upper inequalities hold over every finite alphabet; equality at 114/5 or
204/5 is not proved. In particular residual linear dimension 23 is excluded;
whether dimension 22 can be attained remains open.

The construction's gain is one shared three-symbol object revealed by every
line's helper rows. On the m×m point grid, with m² point rows and 2m line
columns, the same argument adds m(m−1)/2 symbols to a residual pairing value
m²(m−1). This is a lower-order gain, not a positive-density asymptotic one.
The script `grid_code_check.py` checks all recovery and parameter-extraction
formulas as integer coefficient-vector identities. Together with the helper-row
support check, these verify the construction over every abelian group.

## 2. Order values (exact finite counts)

| Host | Residual cells | Largest acyclic set | Residual order bound | Known construction |
|---|---:|---:|---:|---:|
| Fano | 28 | 8 | 20 | 56/3, attained with three lanes |
| PG(2,3) | 117 | 29 | 88 | 78, attained by triangle codes |
| 3×3 point grid | 36 | 13 | 23 | 21, by Section 1 |
| Generalized quadrangle of order (2,2) | 180 | 62 | 118 | 90, by fractional pairing with lanes |

The tools compute the acyclic/order values by integer subset recurrences; the
plane values also have the proofs in the
[projective-plane calibration](projective-plane-order-calibration.md).
These order bounds are not assertions of exact Shannon value or capacity.
The grid upper bound has since improved to 114/5 by the linked certificate.

The generalized quadrangle is smallest **within linear incidence structures
having three points on each line and three lines through each point**, with
no mutual triangle. Here linear means that two distinct points lie on at most
one common line. Its incidence graph is cubic, bipartite, and has no cycles
of length four or six. The breadth-first count from an edge gives at least
30 vertices, or 15 points and 15 lines, attained by this quadrangle. Without
linearity or these regularity assumptions, no such minimality is claimed.

## 3. The soft form of the order bound

For finite random variables on a loopless residual host V and common
conditioning Z, write

\[
\operatorname{TC}(X_V\mid Z)=\sum_{v\in V}H(X_v\mid Z)-H(X_V\mid Z).
\]

**Lemma.** If A⊆V is acyclic for the helper relation, then

\[
\sum_{v\in A}I(X_v;X_{H_v}\mid Z)\le\operatorname{TC}(X_V\mid Z).
\]

*Proof.* Order A with its helpers in A first, and put V∖A before it. Data
processing bounds each helper mutual information by the information in the
preceding variables. Summing and applying the chain rule gives

\[
\sum_{v\in A}H(X_v\mid Z)-H(X_A\mid X_{V\setminus A},Z)
=\operatorname{TC}(X_A\mid Z)+I(X_A;X_{V\setminus A}\mid Z)
\le\operatorname{TC}(X_V\mid Z).
\]

The omitted difference is TC(X_{V∖A}|Z), which is nonnegative. ∎

This proof also holds for normalized monotone submodular functions, with
conditional entropies interpreted as rank increments. Exact recovery makes
I(X_v;X_Hv|Z)=H(X_v|Z), recovering the usual acyclic-set bound.

Define c_ent(host) as the supremum, over all finite joint distributions with
TC>0, of

\[
\frac{\sum_{v\in V}I(X_v;X_{H_v})}{\operatorname{TC}(X_V)}.
\]

Define c_Sh(host) by the same expression over normalized monotone submodular
functions, without imposing recovery equalities. Use zero for the ratio when
TC=0: on a loopless host all the numerator's terms then vanish. Both constants
are zero on an edgeless host. Self-loops must be removed first; one independent
self-loop variable would otherwise give positive numerator and TC=0.
Conditional versions follow by contraction or by averaging conditional laws.

A fractional cover of V by acyclic sets gives an upper bound on both
constants, by summing the lemma with its nonnegative cover weights. If the
residual directed host is vertex-transitive, its fractional acyclic chromatic
number is N/α, where N=|V| and α is the largest acyclic-set size. Thus

\[
c_{\rm ent}\le c_{\rm Sh}\le N/\alpha.
\]

Indeed, average a maximum acyclic set over automorphisms; the reverse bound
for the fractional-cover cost follows because every acyclic set has size at
most α. With uniform singleton caps this gives the usual order price on a
transitive host. Weighted coordinate bounds can matter, so no blanket claim
is made that every weighted use of acyclic sets is equivalent.

A mutual s-clique, s≥2, gives c_ent≥s by a sum-zero law on that clique and
constant variables elsewhere. The [paid Fano inequality](fano-soft-recovery.md)
therefore gives c_ent(Fano)=c_Sh(Fano)=3, against N/α=7/2. For the residual
grid, the [new certificate](triangle-free-shannon-gap.md) gives

\[
12/5\le c_{\rm ent}(\mathrm{grid})\le c_{\rm Sh}(\mathrm{grid})
\le30/11<36/13.
\]

The lower bound uses the uniform 21-symbol code: all 36 marginals have entropy
one, so the ratio is 36/(36−21). Neither grid constant is determined exactly.

For c>0, a proved inequality with constant c bounds every exact code by
H(X_V)≤(1−1/c)Σ_v H(X_v); the c=0 edgeless case is handled separately and has
only constant codes. Consequently a bounded c_Sh on a family with N/α→∞ is
one sufficient soft-Shannon target for high-order bases. It is **not** asserted
to be equivalent to a unit-capacity exact-recovery Shannon bound: that bound
alone does not supply a uniform penalty for imperfect recoveries. Returning
to a full incidence host also requires charging its incident coordinates.

## 4. Fractional triangle packings at bounded window

**Proposition.** Consider an incidence host with m columns, any number of rows,
and at most w helper rows per column. Let T be the total weight of a fractional
packing of mutual triangles, with total load at most one per cell. If w≤1,
then T=0. For w≥2,

\[
T\le\sqrt2\,w\sqrt{w-1}\,m^{3/2},\qquad T\le N/3,
\]

where N is the number of cells available to the packing. In particular, for
a square d×d host this gives O(w^{3/2}d^{3/2}).

*Proof.* Choose θ>0 and call a row heavy when it helps more than θ columns.
There are at most wm/θ heavy rows. A triangle with at most one heavy row has
a cell (p,ℓ) whose two partner rows are light. For one of these rows q∈ρ(ℓ),
the rows p and q share a column. A light q shares a column with at most
(w−1)θ other rows. There are at most w choices of q per column, hence at most
mw(w−1)θ possible witness cells. Charge each such triangle to one witness;
its fractional load is at most one.

Each remaining triangle has at least two cells in heavy rows, so its total
weight is at most wm²/(2θ). Combining and taking θ=√(m/(2(w−1))) proves the
first bound. Summing all cell loads gives 3T≤N. ∎

The earlier choice ε=d^(−1/2) in the heavy-row sketch did not establish the
claimed dependence on w. The balanced threshold above supplies the written
proof. This limits triangle-packing constructions, **not arbitrary codes**.
The amplification theorem carries a Fano Shannon upper bound to fixed window
without asserting that its triangle lane code lifts. The original matching
lifts contain a perfect matching and therefore have the usual pairing lower
bound; their exact capacity remains unknown.

## 5. What two line closures say in a projective plane

Work in a plane of order n≥2, **after conditioning on all incident cells**,
with exact whole-row recovery and conditional singleton entropies at most b.
Two distinct lines ℓ₁,ℓ₂ meet at o. Let O be the residual row of o, and A_i
the n residual point rows of ℓ_i∖{o}. Let K₁₂ be the n cells (a,ℓ₁) with
 a∈ℓ₂∖{o}, and define K₂₁ symmetrically. Thus K₁₂⊆A₂, K₂₁⊆A₁, and each
cross tuple is recoverable from the other line's rows.

Given O and the already conditioned incident cells Z, (K₁₂,K₂₁) is a common
function of A₁ and A₂. Therefore
I(A₁;A₂|O,Z)≥H(K₁₂,K₂₁|O,Z). Purchasing the n³−n remaining coordinates of
each A_i gives

\[
H(A_1,A_2\mid O,Z)
\le2(n^3-n)b+I(K_{12};K_{21}\mid O,Z).
\]

The ordinary order estimate follows from I(K₁₂;K₂₁|O,Z)≤nb. In the normalized
triangle lane code, b=1 and the mutual information is 2n/(n+1): the n²
triangles through o each contribute one shared conditional lane, divided by
binom(n+1,2). Other independent lanes contribute no cross information. This
quantity measures conditional dependence between the cross tuples; it need
not be implemented by a literal pairing construction.

For the triangle code, submodularity on sets A,B is tight exactly when no
triangle lies in A∪B without lying in A or B. Two line closures satisfy this:
if a triangle has a vertex outside both lines, its opposite side must be one
of the two lines; otherwise two of its vertices lie on one line. In either
case the triangle is contained in that line's closure.

Here closure means repeated application of the host's whole-column recovery
rules, not all functional dependencies that a particular code may satisfy.
The closure of a set of complete point rows is everything exactly when at
most one point is missing, for **every** plane order n≥2, including Fano.
If two points p,q are missing, row p lacks the n columns through q other than
pq, and no outside row becomes complete. If only p is missing, all of its
nonincident columns have their helpers among the available rows.

This obstructs the literal five-point recipe, not every two-closure argument.
In PG(2,3), split the four lines through one point into two pairs. Their two
seven-point unions together contain all thirteen points, so their closures
join to the entire residual host. A larger-plane proof is not forced to use
many closures by this observation alone. The missing ingredient remains a
useful bound on the cross-tuple information, coupled across the host.

### 5a. Why line pairs through one point cannot give a constant (Fable, unreviewed)

Fix o. A cell (a, m) is *radial* for o if o ∈ m. The cells shared by the closures of two lines
through o, beyond the row of o, are radial for o, and there are (n+1)n² radial cells in all: a
fraction 1/(n+1) of the n²(n²+n+1) cells. Every decomposition of the point set into unions of
lines through o therefore gains at most about n³ of n⁴.

More generally a single closure gains little at any density. If the point set S misses a set B,
the lines inside S are the lines missing B, and by the expander mixing lemma for the incidence
graph (degree n+1, second eigenvalue √n) there are fewer than n·d/|B| of them. Their columns add at
most |B| cells each outside the rows of S, so every row closure exceeds its rows by fewer than n·d
cells, about a fraction 1/n. A proof of a constant deficit for planes has to compose closures
around all centres to a depth that grows with n. I have no such argument; the route is closed in
the roadmap as X30.

## 6. Numerical leads (heuristic only)

Fable's earlier alternating least-squares searches reported:

- On Fano and PG(2,3), runs above the triangle value stopped near squared
  losses following 3K−2N: Fano K=19 gave about 1; PG(2,3) K=80,84,90 gave
  about 6,18,36. These are observations, not certified minima or a proof
  that an optimal triangle packing explains the losses.
- On the grid, small numerical residuals appeared at K=19,20,21, with no
  exact construction at K=22 or23. Section 1 supplies an independent written
  construction at21; the new Shannon upper bound excludes dimension23.
- Small residuals also appeared at grid dimension24, which even the older
  order bound excludes. Approximate convergence cannot certify a code.

No result in Sections 1–5 relies on these searches. A positive construction
requires an exact verified recovery/rank certificate; failure to find one
proves no upper bound. The current grid range is 21≤Sh_res≤114/5, with the
same lower/upper range for its capacity exponent; neither optimum is known.
