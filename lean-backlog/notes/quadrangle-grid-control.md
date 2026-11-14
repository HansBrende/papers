# A two-lane grid code on the smallest generalized quadrangle

Hans Brende and GPT-6 Astra, 14 November 2026, using Claude Fable's
[explicit grid code](triangle-free-hosts.md#1-an-explicit-code-beyond-pairing-on-the-33-grid).
**Status:** written proof with an exact finite checker; not Lean-verified.
No literature novelty claim is made.

The generalized quadrangle of order (2,2) already refutes the proposed
residual soft-Shannon constant 2. Ten copies of the existing grid code
give **105 information symbols in 180 residual cells** over a two-lane
alphabet. Consequently

$$c_{\rm ent}(\mathrm{GQ}(2,2))\ge12/5,
\qquad c_{\rm Sh}(\mathrm{GQ}(2,2))\ge12/5>2.$$

This is a finite construction. It does not determine either constant,
the capacity, or the behaviour of larger generalized quadrangles.

## 1. The incidence model and its ten grids

Take the 15 two-element subsets of a six-element set as points. A line
is a perfect matching of that set: three disjoint pairs. There are 15
lines, each with three points, and every point lies on three lines.
Two distinct points lie on a common line exactly when their pairs are
disjoint. If a point p is not on a line, its two elements belong to two
different matching pairs. Exactly one pair of that matching is disjoint
from p. This verifies the generalized-quadrangle axiom directly.

There are 45 incident cells and 180 nonincident, or residual, cells in
the 15-by-15 whole-row array. The helpers of column l are the three
point rows belonging to the matching l.

An unordered partition of the six elements into sets A and B of size
three selects nine points, the pairs meeting both A and B. Its six
selected lines are the perfect matchings between A and B. After
ordering A and B, identify these matchings with the permutations of
three elements. The even and odd permutations form two parallel
classes of three lines. Lines in one class are disjoint; a line in one
class and a line in the other meet in exactly one selected point.
This is the 3-by-3 point grid, including all three points of each of
its six lines. Its residual array has 36 cells.

There are binom(6,3)/2=10 such grids. **Every residual quadrangle cell
lies in exactly two of them.** To see this, fix a matching l. There
are 2^3/2=4 unordered bipartitions crossing all three pairs of l. A
point p not on l joins elements in two different pairs. Exactly half
of those four bipartitions also put p's two elements on opposite
sides. These, and only these, select both p and l.

## 2. Independent grid codes use two lanes per cell

Let Q be any finite abelian group of order q>=2. The existing grid
construction has q^21 words on its 36 residual cells, recovers each
target from its line's three helper rows, and has a uniform marginal
on Q at every cell when its 21 parameters are independent and uniform.

Use independent sources for a copy of this code on each of the ten
grids. A residual quadrangle cell lies in exactly two grids, so store
their two symbols as its entry in Q^2. Fix an ordering of the two grid
labels at each cell so that every decoder knows which lane belongs
to which grid. Each lane is recovered by its grid decoder: all of
that grid line's point rows are actual helpers in the quadrangle.
Recovery of the two lanes gives recovery of the entry.

All ten grid parameter tuples can be recovered from their respective
lanes, so the combined encoder is injective. It has q^210 residual
words. Adjoin two independent Q symbols at each of the 45 incident
cells, whose self-recovery is automatic, to obtain q^300 full words.
In units of the entry alphabet Q^2, these are exponents 105 and 150:

$$\frac{105}{180}=\frac7{12}\quad\hbox{residually},
\qquad \frac{150}{225}=\frac23\quad\hbox{on the full array}.$$

These lower bounds hold for every square alphabet cardinality q^2,
using a cyclic group of order q if no group structure was specified.
Over a finite field Q the construction is vector-linear, with two
Q-symbols per entry. No equality with
the known order bounds 118 and 163 is claimed.

For the soft constant, use the uniform law on the residual code and
measure entropy in base q. Its total entropy is 210. Every residual
entry has entropy two because its lanes come from independent grid
sources. Hence the singleton entropy sum is 360 and total correlation
is 150. Exact recovery gives a helper-information sum of 360, proving
the ratio 360/150=12/5. This uses the residual, loopless definition of
[the soft constants](triangle-free-hosts.md#3-the-soft-form-of-the-order-bound).

Even one grid, with all other residual coordinates constant, gives
the same lower bound on the soft constant. The ten-grid construction
also supplies uniform nonconstant marginals across the entire
residual host and improves its previous fractional-pairing lower
bound from 90 to 105 entry-symbols.

## 3. Scope corrections for the proposed family

For a generalized quadrangle of order (s,s), the number of point rows
and line columns is d=(s+1)(s^2+1). Each column has s+1 incident cells.
The residual size is therefore

$$d\,[d-(s+1)]=s^2(s+1)d,$$

not s^3d. At s=2 this is 180. There are no mutual triangles, but the
absence of such triangles does not force the soft constant to be two.
The present argument addresses s=2 only.

A residual bound with soft constant c would bound a full regular base
of side d and incidence degree w by rate

$$1-1/c+w/(cd).$$

This coarse-base correction does not disappear from the inherited bound
when only the clone count of a fixed base grows, even if the actual
incident-cell density of a sparse refinement vanishes. It vanishes
when the base family itself has w/d tending to zero. Likewise, the fixed-base order upper bound in
the [amplification theorem](finite-shannon-gap-amplification.md#4-every-fine-row-order-still-pays-almost-the-base-order-cost)
uses balanced helper-containment refinements. Direct Kronecker
products of incidence relations satisfy that containment; other
graph-product or code-product conventions require a separate check.

For random incidence at a fixed probability p strictly between zero and
one, mutual cliques of unbounded size do rule out a uniform soft constant:
for each fixed m, disjoint m-row/m-column blocks independently realize
the pattern with missing diagonal and all off-diagonal incidences with
probability (1-p)^m p^(m(m-1))>0. A clique of size m carries a sum-zero
code with soft ratio m. This does not itself show that the capacity of
the entire random host tends to one, and says nothing about the random
fixed-window regime p of order w/d.

## 4. Reproduction

From the repository root:

```sh
python3 lean-backlog/tools/host-probe/gq_grid_control.py
```

The checker enumerates only the 15 points, 15 lines and ten grids. It
verifies the generalized-quadrangle axiom, each grid's exact incidence
identification, and the multiplicity two of every residual cell. It
then reuses `grid_code_check.py` to check all grid recovery and source
extraction identities over the integers. No optimizer, floating-point
rank calculation or general-quadrangle search is involved.
