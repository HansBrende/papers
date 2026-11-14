# A Shannon improvement on the triangle-free grid host

Hans Brende, GPT-6 Astra and Claude Fable 5.2, 14 November 2026.
Fable proposed this test and constructed the lower code; Astra extracted
and independently checked the upper certificate. **Status: written proofs
with exact finite checks, not Lean-verified.** No literature novelty claim.

The grid has **nine point rows and six line columns**. It is a rectangular
calibration, not itself a square matrix family. On its 36 nonincident
cells the best order bound is 23, whereas Shannon inequalities prove

$$\boxed{21\le\operatorname{Sh}_{\rm res}\le114/5<23.}$$

There are no mutual triangles among these cells. Thus mutual triangles
are not necessary for a Shannon improvement over every acyclic/order
bound. The inequalities are strict improvements of an upper bound;
neither the exact Shannon value nor the exact capacity is determined.

## 1. Host, lower code and order

Points are (i,j)∈{0,1,2}². The six lines are the three sets with fixed
first coordinate, Rₖ, and the three with fixed second coordinate, Cₖ.
Column ℓ recovers from all entries in the three point rows on ℓ. Of the
54 cells, 18 are incident and 36 are nonincident. Contracting the incident
cells leaves four residual cells per row, six per column, and twelve
cells in each column's helper union.

The self-recovery constraints of incident cells are vacuous. Conditioning
on them gives the residual upper bound, and adjoining independent symbols
there extends any residual code. Thus
Sh_full=18+Sh_res. The
[explicit shared-difference code](triangle-free-hosts.md#1-an-explicit-code-beyond-pairing-on-the-33-grid)
has q²¹ residual words for every finite alphabet size q≥2, using an abelian
group of that size. Its 18 private symbols are read from entries and its
three shared symbols from opposite-entry differences. Therefore

$$39\le\operatorname{Sh}_{\rm full}\le204/5<41.$$

No three nonincident cells are pairwise mutual. Such a triple would need
three distinct grid lines whose pairwise intersections are three distinct
points. Among three grid lines, two are parallel, so this cannot happen.

For completeness the order value needs no optimization. If a point prefix
has k elements, the maximum numbers of complete lines for k=0,…,8 are
0,0,0,1,1,2,2,3,4. The union of x horizontal and y vertical lines has
3x+3y−xy points, which gives these upper bounds. The point order

$$ (0,0),(0,1),(0,2),(1,0),(2,0),(1,1),(1,2),(2,1),(2,2) $$

attains them simultaneously. Their sum is 13, so the maximum acyclic set
has size 13 and the full order bound is 54−13=41, or 23 after removing
the 18 loops. The row-order exactness argument of
[Paper 17, the whole-row order proposition (b)](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex)
works unchanged for rectangular arrays: an acyclic cell set induces an
acyclic dependency order on its active point rows, and is contained in
the corresponding row-order acyclic set.

## 2. An 18-term certificate

Let W be the 36 residual cells. For a cell set S, cl(S) repeatedly adjoins
a column when all twelve cells of its helper union have been included.
The recovery equalities imply h(cl(S))=h(S). Average h over the 72 grid
automorphisms: independent permutations of the two axes and their exchange.
This preserves the helper relation, feasibility and h(W); it imposes no
symmetry on the code.

The certificate uses only fifteen submodular inequalities

$$\bar h(S\cap T)+\bar h(\operatorname{cl}(S\cup T))
\le\bar h(S)+\bar h(T),$$

one empty-set normalization, a three-cell singleton cap, and one purchase
of 18 cells. Here is the purchase, without relying on a general row-budget
algorithm. Take the five point rows forming the cross R₀∪C₀. Purchase
all four residual cells in each of (0,0),(0,1),(0,2), costing twelve.
These rows recover column R₀. For each of (1,0),(2,0), purchase its other
three residual cells, costing six more. Their R₀ cells are already known.
The three rows of C₀ are now complete, so column C₀ is also recovered.
This generates the cross's entire 28-cell closure from 18 coordinates.

The [exact certificate](../tools/grid-shannon/certificate.json) specifies
all operands and their nonnegative integer weights. Point (i,j) has
index 3i+j; lines R₀,R₁,R₂,C₀,C₁,C₂ have indices 0,…,5. Nonincident
cells are in lexicographic order, and a bit mask selects those coordinates.
There are 18 set orbits in the identity. After orbit averaging, the weighted
sum cancels every other rank variable and gives

$$5\bar h(W)\le2\cdot3+6\cdot18=114.$$

The [standalone checker](../tools/grid-shannon/verify_certificate.py)
reconstructs the host, automorphisms, recovery closures, purchase set and
every inequality from those operands. It checks the integer identity
without importing a solver or the discovery generator. This is an ordinary
exact Python verification, not a Lean proof.

## 3. A paid inequality and an information constant

The certificate also applies without exact recovery. Let X_v, v∈W, and
Z be arbitrary jointly distributed finite random variables. Write H_v
for the twelve residual cells in v's helper rows, and put
ε_v=H(X_v∣X_Hᵥ,Z). Then

$$\boxed{H(X_W\mid Z)\le\frac{19}{30}\sum_v H(X_v\mid Z)
                      +\frac{11}{30}\sum_v\varepsilon_v.}$$

If δ_ℓ=H(X_column ℓ∣X_helper union ℓ,Z), a second valid error term is
(8/15)Σ_ℓδ_ℓ in place of (11/30)Σ_vε_v.

**Proof.** Retain the true conditional rank increment at each use of
combinatorial closure, just as in the
[paid Fano proof](fano-soft-recovery.md). The submodular terms numbered
3,5,6,8 add respectively 1,2,2,1 cells, each at weight one. The cross
purchase at term 17 adds six cells by R₀ and four by C₀, at weight six.
The weighted totals are 114 purchased singleton coordinates, 66 recovered
coordinates, and 16 productive column firings. At each firing the full
helper union is known; its entropy increment is bounded either by the
column's δ_ℓ or by the sum of the newly added cells' ε_v. Transport all
paths by the 72 automorphisms. Transitivity on cells and on columns gives
coefficients

$$\frac{114}{5\cdot36}=\frac{19}{30},\qquad
\frac{66}{5\cdot36}=\frac{11}{30},\qquad
\frac{16}{5\cdot6}=\frac8{15}.$$

The standalone checker verifies each transported charge, not only these
totals. No recovery assumption has been used in this paid version. The
coefficient 11/30 cannot be decreased while retaining singleton price
19/30: independent variables make the inequality an equality. This does
not assert optimality of either price when both are allowed to change.

Equivalently, with TC(X∣Z)=Σ_vH(X_v∣Z)−H(X_W∣Z),

$$\sum_v I(X_v;X_{H_v}\mid Z)\le\frac{30}{11}\operatorname{TC}(X\mid Z).$$

All steps are Shannon inequalities, so the same statement holds for
monotone normalized submodular functions and contractions. Define c_ent
using distributions, and c_Sh using all such functions, as the supremum
of this mutual-information sum divided by positive total correlation on
the **loopless residual host**. The explicit code has 36 unit-entropy
coordinates and total entropy 21, giving ratio 36/15=12/5. Thus

$$\frac{12}{5}\le c_{\rm ent}\le c_{\rm Sh}\le\frac{30}{11}
   <\frac{36}{13},$$

where 36/13 is the soft order bound. These are bounds, not an equality
claim. Free loops must be contracted first: a single independent self-loop
variable would have positive recovered information and zero total correlation.

## 4. Discovery limits and reproduction

There was exactly **one LP solve**, on 872 orbit variables and 14,613
inequalities. Its exact relaxation value was 114/5; a rational primal and
dual were both checked. That proves optimality for the chosen relaxation,
not for the full Shannon problem. Only the independently reconstructed
18-term upper certificate is needed for the global upper bound.

The unchanged Fano family did not fit the previous budget: all grid row
closures and their intersections already gave 40,634 sets in 716 orbits,
and its auxiliary round exceeded 100,000 stored masks before solving.
Without increasing that cap, the test used the closures of unions of the
six helper lines, the nine singleton point rows, empty and full sets;
their pair intersections formed 779 sets in 36 orbits. One auxiliary
meet/closed-join round then fit. No refinement was run after its result.

The known 21-symbol code is not assumed invariant under the 72 symmetries.
For calibration its rank function was averaged over its six distinct
translates. The rank is elementary: each of three independent sectors
consists of six pairs (y_i,y_i−D); a subset has rank equal to its number
of touched pairs, plus one if it contains a complete pair. This supplies
a genuine lower witness for all retained inequalities.

The conditional quadrangle test was stopped at its family census. The
same line-union profile has 3,264 distinct initial closures and exceeded
100,000 sets before finishing their pair intersections. No quadrangle LP
was run, and this resource limit has no capacity implication.

From the repository root, without disabling assertions:

```sh
python3 lean-backlog/tools/grid-shannon/verify_certificate.py
python3 lean-backlog/tools/grid-shannon/closure_relaxation.py \
  --verify lean-backlog/tools/grid-shannon/search-receipt.json
```

The first replays the small proof and paid coefficients. The second
reconstructs the saved discovery relaxation and its exact primal/dual.
Both use only Python's standard library. See the
[tools README](../tools/grid-shannon/README.md) for the bounded solve command.

## 5. Relation to the square and growing questions

There is a square adapter that preserves all normalized values. Replace
each of the nine point rows by **two** clones and each of the six line
columns by **three** clones. Replace every base incidence by all six
incidences between the corresponding groups. The result is an 18×18
host with both incidence degrees six and six fine cells per macro cell.

Macro aggregation divided by six gives a feasible rectangular polymatroid,
so Sh_square≤6 Sh_grid. Conversely, take six independent copies of any
feasible base polymatroid, one for each (row-clone, column-clone) pair.
Every required base helper coordinate of a target's copy is available
among its fine helper rows. This gives the reverse inequality. For order,
let τ_p be the time when both clones of point p have been visited.
The kth group-completion time is at least 2k; each of a base column's
three clones pays its latest helper-group completion. Thus
σ_square≥6σ_grid, with equality by contiguous row groups. Consequently

$$234\le\operatorname{Sh}_{\rm square}\le1224/5<246=\sigma_{\rm square}.$$

Six independent copies of the explicit code give q²³⁴ words on the square
host for every alphabet size q. Every nonincident fine cell projects to a
nonincident base cell because the incidence blocks are complete. Two
mutual cells cannot share a base point or a base line. A fine mutual
triangle would therefore project to a base mutual triangle; none exists.

More generally an a×b incidence host can be balanced this way: with
g=gcd(a,b), use b/g row clones and a/g column clones. Both Sh and σ
scale by ab/g², and residual triangle-freeness is preserved. The same
construction on codewords supplies the corresponding product lower bound.

The [finite-gap amplification theorem](finite-shannon-gap-amplification.md)
therefore applies to this square base whose residual relation has no mutual
triangles. Its short-cycle deletion version also gives growing fixed-window
hosts with incidence girth Ω(log d), while keeping a positive-density gap
below their best order bound. This supplies a gap with neither triangles
in the chosen residual base nor in the eventual fine relation. It does
not assert that no alternative coarse presentation has triangles.

Neither the grid base nor the Fano base has order rate approaching one.
The result removes a proposed limitation of the Shannon method, not the
remaining requirement for a uniform deficit on high-order hosts. The
projective-plane upper conjecture and the general native crux remain open.
