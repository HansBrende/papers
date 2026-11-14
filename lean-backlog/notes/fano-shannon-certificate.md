# A strict Shannon improvement on the Fano whole-row host

14 November 2026. Fable proposed testing row-closure intersections; Astra
constructed the bounded relaxation and extracted the certificate. Two
independent reviews reconstructed its inequalities from the incidence
relation. **Status:** the paid residual inequality, full 49-cell contraction,
exact Shannon values 56/3 and 119/3, and order value 41 are Lean-verified in
[FanoCertificate.lean](../FanoCertificate.lean),
[FanoFull.lean](../FanoFull.lean),
[FanoAttainment.lean](../FanoAttainment.lean) and
[FanoOrder.lean](../FanoOrder.lean). The attaining polymatroids are formalized;
their three-lane code realizations remain written proofs with exact checks.
The general order/acyclic-set identification also remains a written theorem
of Paper 17. No literature novelty claim is made.

## 1. Exact statement

Index the seven rows by the points of the Fano plane and the seven columns
by its lines. The helpers of a column are the three rows incident with its
line. Let Sh denote the maximum of h(V) on all 49 coordinates, over every
normalized, monotone, submodular function h with singleton capacities at
most one and the column-recovery equalities. Then

$$\boxed{\operatorname{Sh}=119/3<41=\sigma.}$$

Here σ is the order bound, equivalently 49 minus the maximum size of an
induced acyclic set, by Paper 17's
[whole-row order proposition, part (b)](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex).
The strict gap is 4/3.

Consequently every whole-row code C on this host, over every finite alphabet A
with |A|≥2,
satisfies |C|≤|A|^(119/3). There is no linearity, source-independence,
encoder-support or decoder-symmetry assumption. The existing three-lane
triangle construction attains the bound: over any base alphabet of size
a≥2 it has a^119 words on 49 entries with three lanes each. Thus equality
holds for every entry alphabet of size a³. In particular the optimal binary
dimension at the canonical three-bit entry width is 119 out of 147 bits.
For arbitrary non-cube scalar alphabet sizes, only the upper bound is
asserted here. The earlier scalar-linear optimum 39 over F₂ and F₃ is
consistent with this result.

This answers the finite G4 question affirmatively: full-cell Shannon
inequalities can improve strictly on every acyclic/order certificate for
a whole-row host. It does not prove a common deficit as the window grows,
or exclude a new class of native transposers.

## 2. Remove the free loops exactly

Let Z be the 21 incident cells and W the 28 nonincident cells. Contracting
Z in any feasible polymatroid gives a feasible residual polymatroid on W:
h_Z(S)=h(S∪Z)−h(Z). Hence Sh_full≤21+Sh_res. Conversely a residual feasible
polymatroid extends by 21 independent unit loops. Every loop cell is its
own helper, and the nonloop recovery conditions survive. Therefore

$$\operatorname{Sh}_{\rm full}=21+\operatorname{Sh}_{\rm res}.$$

Each residual row has four cells. A residual column is recoverable from
the twelve cells in its three helper rows. For S⊆W, write cl(S) for the
closure obtained by repeatedly adjoining any column whose helper union
is already included. The recovery equalities and submodularity imply
h(cl(S))=h(S) for every feasible h.

The group GL₃(F₂), of order 168, acts on points by M and on line normals
by M^(−T). It preserves the directed helper relation. Average h over this
group and denote the result by h̄. This preserves feasibility and h(W);
it does **not** assume that the original code or its distribution has any
symmetry.

## 3. A 33-term certificate

All terms use just the following valid inequalities, applied to h̄.
For A a subset of point rows, let R_A be their residual row union, with
|R_A|=4|A|.

| Kind | Inequality |
|---|---|
| N | −h̄(S)≤0 |
| S | h̄(S∩T)+h̄(cl(S∪T))−h̄(S)−h̄(T)≤0 |
| I | h̄(S)−h̄(T)≤|S∖T| |
| J | h̄(cl(S∪T))−h̄(S)≤|T∖S| |
| B | h̄(S)≤4|A|+|S∖cl(R_A)| |

The submodular terms use closed S and T. Types I and J follow by adding
the indicated actual coordinates, each of capacity at most one; a cover
in a set lattice is never assigned unit cost without justification.
Type B purchases the rows R_A and then the remaining coordinates. The
certificate uses A=∅ twice and one three-point line A, so it needs no
general row-order-budget computation.

The explicit masks and nonnegative integer weights are in
[certificate.json](../tools/fano-shannon/certificate.json), with a
[numeric orbit table](../tools/fano-shannon/dual-orbits.md) and a
[geometric dictionary of all 34 orbits](../tools/fano-shannon/orbit-dictionary.md).
The latter also displays all 33 inequalities in named orbit variables.
Points and line normals are the nonzero binary triples in lexicographic
order; residual cells are the nonincident (point,line) pairs in lexicographic
order. A mask has bit i precisely when the i-th residual cell is selected.
Point-row subsets use seven-bit masks in the same point order.

There are 23 type-S inequalities, three each of types I, J and B, and one
type-N normalization term. Their weighted sum is exactly

$$264\,\bar h(W)\le4928,$$

giving h(W)≤56/3. Only 34 distinct set orbits appear, including ∅ and W.
The type-N term is −117h̄(∅)≤0 and can instead be discharged by normalization;
thus there are 32 nontrivial inequalities.

The only recovery-dependent type-B row is h̄(S)≤13: S is the closure of
the three collinear point rows with seven-bit mask 42, plus one cell.
The rows cost 12 and the extra cell costs one. The other two type-B rows
are ordinary cardinal bounds on five and eight cells. Thus the proof uses
only singleton caps, Shannon inequalities and the seven column-recovery
constraints; it assumes no scalar-field rank inequality or attainable
entropy model.

[verify_certificate.py](../tools/fano-shannon/verify_certificate.py)
independently reconstructs the plane, its 168 automorphisms, every recovery
closure, all 33 inequalities and the exact coefficient identity. It uses
integer and rational arithmetic and imports neither the LP generator nor
a solver. In particular the proof does not rest on a floating-point bound.
The generated Lean proof independently derives every semantic inequality
and checks the same integer combination in the kernel. Python is used for
reproduction, not as a trusted proof premise.

## 4. The matching lower bound

Each noncollinear triple of points gives a triangle of mutually helping
cells: each point paired with the line through the other two. There are
28 such triangles, and every nonincident cell occurs in three of them.
Give each cell one lane for each of its triangles. On each triangle put
one sum-zero check over a cyclic group of size a. All 28 checks use
disjoint lane coordinates; the 21 incident cells are free in all three
lanes. Hence the code has 147−28=119 independent base symbols and satisfies
the full whole-row recovery condition.

Equivalently the residual polymatroid

$$h_\triangle(S)=\frac13\sum_T\min(2,|S\cap T|)$$

is feasible and has h_△(W)=56/3. It is the normalized entropy of the
three-lane construction, not a hypothetical polymatroid extension.
Every positive certificate row is tight at h_△. The construction was
already recorded in the
[simplex calibration](simplex-code-calibration.md#4-finite-projective-controls);
the new result is its unrestricted Shannon upper bound.

## 5. The order bound is exactly 41

For an order of the seven points let A_a be its a-point prefix and J(A)
the number of Fano lines entirely in A. The sum of the last-helper
positions, which is the order cost, equals

$$49-\sum_{a=0}^6 J(A_a).$$

The seven prefix terms are bounded respectively by 0,0,0,1,1,2,4. Two
distinct lines have a five-point union, so four points contain at most
one line. Omitting two points leaves exactly two complete lines, and
omitting one leaves four. Beginning the order with a collinear triple
attains all seven bounds at once. The maximum prefix sum is eight, so
σ=41. Paper 17's exactness result then gives maximum acyclic-set size eight.
This proves the 4/3 gap without an acyclic-set optimization.

## 6. Discovery scope and next question

The literal instruction to close all row closures under intersections
and closed unions generates the entire residual closed-set lattice.
Indeed, for a point p not on a line ℓ, the closures of row p and of the
three rows on ℓ intersect in the singleton (p,ℓ). Once all singletons are
present, closed unions generate every closed set. Every set of at most
eleven cells is already closed, so the family has at least 46,295,513 sets
and at least 275,569 symmetry orbits. It is not a small LP.

The bounded test instead used the 121 distinct initial row closures,
their two-fold intersections and the 28 triangle triple-intersections:
3,159 sets in 51 orbits. It added exactly one round of meets and closed
joins of pairs from that base. With implicit orbit completion this gave
2,668 variables and 66,163 distinct inequalities. The single solve took
about two seconds and yielded the certificate above. No extra host or
larger family was searched.

A truncated-family optimum would not usually determine the full Shannon
value. Here it does because its **valid global upper certificate matches
an actual code**. The independently replayed 33-term certificate is all
that the upper proof needs; the larger discovery LP is retained only for
reproduction.

The [paid-recovery form](fano-soft-recovery.md) now states the exact cost
of imperfect applications. A separate
[amplification theorem](finite-shannon-gap-amplification.md) turns this
finite Shannon/order gap into a positive-density gap on growing hosts
of fixed window. Those hosts already have an order deficit; a uniform
whole-row deficit and a new native-machine exclusion remain open.

## 7. Reading the geometry and its limits

The [dictionary](../tools/fano-shannon/orbit-dictionary.md) specifies each
orbit by a labelled row-closure expression, its number of cells, and its
attained entropy in the triangle code. Its expressions are checked up to
one simultaneous collineation, not independent changes of their operands.
Thirty-one orbits are row closures or two-fold intersections; two more
are intersections of such sets and one is a closed union. No three-cell
triangle orbit itself occurs in the positive dual. The triangles supply
the matching code, not a separate triangle inequality in the upper proof.

For two lines meeting at a point o, their residual closures intersect
in the four cells of row o and four cross cells. That eight-cell set
has triangle-code entropy 20/3. Their union has entropy 52/3 in the code,
while its five rows have row-order purchase cost 18. These are values
of the attaining code, not unconditional lower bounds on intersections;
the constant code shows why any such lower bound must involve other
entropy terms. The certificate supplies the coupled inequalities.

The corresponding incidence descriptions hold in every projective
plane: three nonconcurrent line closures meet in a mutual triangle,
and two line closures meet in a union of triangles. They do not make
all 33 Fano inequalities portable. For example, the three diagonal
points of a complete quadrangle are collinear in characteristic two;
the representatives [1:1:0], [1:0:1], [0:1:1] have determinant −2, so
that identity fails over F₃. The exact seven-point orbit equalities
cannot simply be assumed in the thirteen-point plane.

The [PG(2,3) calibration](projective-plane-order-calibration.md) proves
order value 140 with a short geometric argument, checked by two integer
subset recurrences. The known triangle code gives 130. No new Shannon
upper below 140 for that plane is asserted, and no second LP was run.
