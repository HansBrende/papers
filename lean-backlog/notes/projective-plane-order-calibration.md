# Projective-plane order calibration

Hans Brende and GPT-6 Astra, November 2026.

**Status:** complete written proofs and exact integer checks; not
Lean-verified. For the whole-row host of the projective plane $PG(2,3)$,
the exact order bound is **140**, while the triangle construction gives
**130** normalized symbols. This establishes the comparison needed to
test an extension of the [Fano Shannon bound](fano-shannon-certificate.md);
it does **not** prove a new Shannon upper bound for $PG(2,3)$.

| Quantity | Value |
|---|---:|
| Point rows and line columns | 13 each |
| All cells | 169 |
| Incident cells, which have self-loops | 52 |
| Nonincident cells | 117 |
| Maximum induced acyclic set | 29 |
| Full order bound $\sigma$ | 140 |
| Residual order bound after freezing the loops | 88 |
| Six-lane triangle code, normalized residual dimension | 78 |
| Six-lane triangle code, normalized full dimension | 130 |

Thus the full Shannon value lies in $[130,140]$. Proving residual upper
bound $78=(2/3)117$ would improve the full order bound by 10. No exact
scalar binary capacity is claimed.

## The host and its order bound

Rows are points and columns are lines of $PG(2,3)$. A cell $(p,\ell)$
recovers from every cell whose point row lies on $\ell$. Each line has
four points, each point lies on four lines, and two distinct points or
lines have a unique join or intersection. Incident cells have self-loops
and may be freely adjoined to any code on the remaining 117 cells.

For a point order $\pi$, retain the cells $(p,\ell)$ for which $p$
precedes every point of $\ell$. Helpers of retained cells have strictly
later point rows, so this set is acyclic. If $S_k$ is the prefix of
$k$ points and $u(S)$ counts lines disjoint from $S$, its size is
$\sum_{k=1}^{13}u(S_k)$.

Every acyclic cell set is contained in one of these order sets. On its
active point rows, draw $p\to q$ if a selected cell $(p,\ell)$ has
$q\in\ell$. A cycle of active rows would lift to a cell cycle by choosing
one witnessing cell per edge. Topologically order the active rows and
put inactive rows last. Every selected cell then precedes all its helper
rows. Hence maximizing over point orders gives the full maximum induced
acyclic set, not merely a restricted version of that bound.

The maximum number of disjoint lines for a prefix of each size is:

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10–13 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Maximum disjoint lines | 9 | 6 | 4 | 3 | 2 | 2 | 1 | 1 | 1 | 0 |

Here are upper bounds requiring only the plane axioms.

- One point meets four lines; two points meet seven.
- Three noncollinear points meet nine lines, and three collinear points
  meet ten. Thus at most four lines are disjoint from three points.
- Four distinct lines cover at least $16-\binom42=10$ points. They
  cannot all avoid four chosen points, whose complement has size nine.
- Three lines cover at least nine points, so five or more chosen points
  leave at most two disjoint lines.
- Two lines cover seven points, so seven or more chosen points leave at
  most one disjoint line. Ten chosen points leave none.

One nested order attains all these bounds. In the affine chart
$(1,x,y)$, take the four points with $x,y\in\{1,2\}$, ordered as
$(1,1),(1,2),(2,1),(2,2)$. Next take $(1,0),(2,0)$, then
$(0,0),(0,1),(0,2)$, and finally the four points at infinity. After the
square, the disjoint lines are $x=0$, $y=0$, and infinity; after six
points they are $x=0$ and infinity; after nine only infinity remains.
The intermediate counts are those in the table. Their sum is 29, so

$$\sigma=169-29=\boxed{140}.$$

## Triangle lower bound and incidence checks

Three noncollinear points $a,b,c$ give a mutual triangle
$(a,bc),(b,ac),(c,ab)$, where $bc$ denotes the joining line. Every
nonincident cell $(a,\ell)$ belongs to exactly $\binom42=6$ such
triangles: choose two points on $\ell$. There are consequently
$117\cdot6/3=234$ triangles. Giving each triangle weight $1/6$
is a perfect fractional packing.

For an exact code, give each cell six lanes, one per incident triangle.
On each triangle impose a sum-zero equation on its three private lanes.
Any lane is recovered from the other two; different triangles use
different lanes. This gives $2\cdot234=468$ independent base symbols on
the residual, and $6\cdot52$ additional free symbols on the loops.
The total is 780, or **130** after division by the six lanes per cell.
This works over every finite field, or using a finite cyclic group on
any finite base alphabet. The resulting cell alphabet has size $q^6$,
not $q$; the normalized Shannon lower bound is nevertheless 130.

The following checks identify potential sets for an upper proof, without
claiming one. The residual closure of a line's point rows consists of
those rows together with that line's column. The closures of three
nonconcurrent lines intersect in exactly their opposite-cell triangle.
Two line closures meet in 15 residual cells: nine cells of their common
point row and six cross cells. This intersection is the union of nine
mutual triangles. In the six-lane code its normalized entropy is
$15-9/6=27/2$.

Under the uniform law on this code, write $h$ for entropy in units of one
six-lane symbol. For any set $S$ of residual cells,

$$h(S)=|S|-\frac{\#\{\text{triangles contained in }S\}}6.$$

This follows by summing the independent triangle entropies
$\min(2,|S\cap T|)$. It is an attainment formula for this code, not an
inequality for arbitrary codes.

## What happens on growing planes

For any projective plane of order $n\ge2$, put $d=n^2+n+1$. The residual
has $dn^2$ cells, each in $\binom{n+1}{2}$ mutual triangles, giving
the same normalized rate $2/3$ by lanes. Its order bound instead has
rate tending to **one**.

To see this, for a $k$-point set $S$ write $a_\ell=|S\cap\ell|$.
The plane axioms give
$\sum_\ell a_\ell=k(n+1)$ and
$\sum_\ell a_\ell^2=k(n+k)$. Cauchy–Schwarz on the hit lines therefore
gives

$$u(S)\le \frac{n(d-k)}{n+k}.$$

Summing along any point order, with $H_j=\sum_{i=1}^j1/i$, bounds the
maximum acyclic set by

$$n(d+n)(H_{d+n}-H_n)-nd=O(n^3\log n).$$

Dividing by $dn^2=\Theta(n^4)$, the residual order rate is at least
$1-O(\log n/n)$, and hence tends to one. A general residual Shannon
upper bound of $2/3$, if proved, would thus give a nonvanishing gap
from order. These plane hosts have growing window $n+1$; this paragraph
does not establish a fixed-window or native tape exclusion.

## Exact reproduction

Run from the repository root without disabling assertions:

```sh
python3 lean-backlog/tools/fano-shannon/pg3_order.py
```

The standard-library checker uses the existing
[plane constructor](../tools/simplex-calibration/plane_controls.py),
recomputes all 8,192 point-subset states, and compares the result with
[the saved receipt](../tools/fano-shannon/pg3-order-receipt.json).
It verifies the geometric order, its 29 acyclic cells, the triangle
counts, and the closure intersections. No optimizer is imported.

The main recurrence is

$$F(\varnothing)=0,\qquad
F(S)=u(S)+\max_{p\in S}F(S\setminus\{p\}).$$

It gives $F(\text{all points})=29$. Independently, if $c(S)$ counts
lines contained in $S$, the recurrence

$$G(\varnothing)=0,\qquad
G(S)=\min_{p\in S}\bigl(G(S\setminus\{p\})+
|S|\,[c(S)-c(S\setminus\{p\})]\bigr)$$

minimizes the sum of line-completion positions and returns 140. These
recurrences enumerate subsets, not all $13!$ orders. To regenerate the
receipt, add `--write`; `--receipt FILE` selects a different receipt path.
