# Two-sided whole-row codes and the one-sided deficit

Claude Fable 5.2 and GPT-6 Astra, directed by Hans Brende, 14 November 2026.
**Status:** the finite upper-bound adapter, common-deficit equivalence and native
consequences are Lean-verified in [TwoSidedCodeTransfer](../TwoSidedCodeTransfer.lean).
The symmetry normalization, exact examples and Section 7 are reviewed written
proofs; their formalization is not claimed. No literature novelty claim.
Front D10 of the [roadmap](../wall.md).

Fix a helper map ρ on [d] and a finite alphabet Q of size q≥2. A set C of
d×d arrays over Q is **two-sided** if column r is determined by rows ρ(r), and row r is determined
by columns ρ(r), for every r. Equivalently, C and Cᵀ are both one-sided
whole-row codes for the **same** ρ. Neither C=Cᵀ nor linearity is required.
The window is max_r|ρ(r)|.

The two-sided condition is stricter on an individual code and reduces some
exact capacities. However, **existence of a common positive deficit is
equivalent for the two classes**, up to a factor of two.

## 1. Translation and intersection

**Finite transfer.** Every one-sided code C has a two-sided code D on the
same host and alphabet satisfying

$$|D|\ge |C|^2/q^{d^2}.$$

**Proof.** Identify Q with the cyclic group of order q; this imposes no
algebraic assumption on C. Coordinatewise alphabet bijections preserve
functional recovery, as do subsets. Thus

$$D_z=C\cap(z+C^{\mathsf T})$$

inherits forward recovery from C and reverse recovery from z+Cᵀ. Every pair
(x,y)∈C×C contributes exactly once, at z=x−yᵀ; y is uniquely determined by
x and z. Therefore Σ_z|D_z|=|C|². There are q^(d²) translations, so one
intersection has at least the average size. Neither z nor D must be
transpose-invariant. ∎

Let κ₁ and κ₂ be the maximal logarithm-base-q code sizes in the one-sided
and two-sided classes on this fixed host. Then

$$\max(0,2\kappa_1-d^2)\le\kappa_2\le\kappa_1,\qquad
  \frac{d^2-\kappa_2}{2}\le d^2-\kappa_1\le d^2-\kappa_2.$$

A two-sided upper bound q^a gives a one-sided bound q^((d²+a)/2), without
changing dimension, alphabet, helper map or window. A common two-sided
deficit δ₂ thus gives a one-sided deficit δ₂/2, preserving the canonical
growing-alphabet quantifiers. The converse implication loses nothing.
Two-sided half rate would give one-sided rate at most 3/4, enough for the
common-deficit route; it would **not** prove one-sided half rate.

These are statements about actual finite codes, not a comparison between
one-sided and two-sided **Shannon relaxation optima**. A two-sided Shannon
upper bound remains useful because it bounds actual two-sided codes.

## 2. Advice, exceptions and the native reduction

The original observation is valid. An oblivious transposer uses the same
schedule on A and Aᵀ. Fixing a(A) and a(Aᵀ) gives the two recovery
directions with the same ρ. With B advice bits and no exceptions or other
observations, some fibre has at least 2^(N−2B) words, N=d²b.

**Exceptions must be paid in both directions.** Freeze exceptional
columns E_c and exceptional rows E_r. Their union has
d(|E_c|+|E_r|)−|E_c||E_r| entries, and every missing target becomes constant.
For one common set E of size e the bill is **2de−e²**.

For the actual cone adapter, let enc be an m-bit index code on the full
N-bit cube with transpose demand. Suppose the old cones lie in the new
cones plus a raw set U, and the new cones have row cover ρ except at E.
Let T transpose entry addresses without changing bit lanes, and let F_E
contain all bits in rows or columns E. Fix the observation

$$(\operatorname{enc}(x),\operatorname{enc}(Tx),
  x|_{\,U\cup T(U)\cup F_E}).$$

The existing entry-word lemma applies to x and Tx separately. Every fibre
is a complete two-sided code for ρ, so a bound q^a, q=2^b, gives

$$N\le2m+|U\cup T(U)\cup F_E|+ba
 \le2m+2|U|+b(2de-e^2)+ba.$$

This uses the full-cube index-code predicate, not machine correctness or
equality of the two messages.

An even shorter route is Section 1: convert the two-sided cardinality
hypothesis to the existing one-sided hypothesis at half the deficit,
then reuse all geometry and cone proofs unchanged:

- A common two-sided deficit δ₂ along canonical alphabets gives Paper 14's
  literal **Crux at δ₂/2**. Uniformity over positive bit widths gives
  the corresponding CruxOn statement.
- At the explicit window of
  [wholeRow_window_bound_excludes](../RowSpreadCrux.lean), exclusion follows if

  $$\delta_2>\frac{169}{32}\varepsilon.$$

  The window remains rowSpreadWindow(k,β,genieDepth(k,β,C,ε),C,ε);
  it is not doubled, and the original machine hypotheses remain.

Indeed the raw-cone route has |U|≤(63/64)εN and e≤(21/32)εd, yielding
N≤2m+(105/32)εN+ba. The direct machine route has U empty and
m≤(127/64)εN. Its two messages and two exception bills total (169/32)εN.
The geometric guards remain d≥4, b≥1, C≥1, ε>0, the stated time/depth
bounds and a complete output prefix. The overlap term −be² may sharpen
a finite bill but is unnecessary for this implication.

**Formalization boundary.** [TwoSidedCodeTransfer](../TwoSidedCodeTransfer.lean)
proves the coordinate definition equivalent to recovery on C and Cᵀ. Its
`wholeRow_card_sq_le_of_twoSided` proves the relation-specific finite form:
if every two-sided code D has |D|≤A, then |C|²≤q^(d²)A for every one-sided C.
It allows q≥1, empty C, d=0 and arbitrary real A. The exponent adapter needs
no sign assumption. This formalizes the upper-bound consequence of Section 1;
the separate existence of a large translated intersection is proved in writing above.

`commonDeficit_iff_twoSided` verifies the equivalence along the canonical growing
alphabets. The uniform all-alphabet implication is also proved. The native endpoints
`uniformTwoSidedWholeRowRateCanonicalBits_crux`,
`uniformTwoSidedWholeRowRate_cruxOn`,
`uniformTwoSidedWholeRowRateCanonicalBits_excludes` and
`twoSidedWholeRow_window_bound_excludes` reuse
[RowSpreadCrux](../RowSpreadCrux.lean) at half the deficit. The alternative direct
pair-message invoice above and the paid symmetry proof below remain written proofs.
All checked declarations depend only on Lean's standard axioms. No capacity bound
or unconditional machine exclusion is asserted.

Check with the repository's pinned dependencies:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py TwoSidedCodeTransfer
```

The original row-spread modules must already have been checked; running the same
command without the module argument checks that full chain.

### Symmetric helper relations suffice after a small payment

The existing paid reverse-degree normalization extends to both directions.
For an integer R≥0 let H be the indices with reverse degree greater than R.
Since there are at most wd incidences, |H|≤wd/(R+1). Freeze all entries in
rows H or columns H, costing 2d|H|−|H|². Within every fibre both decoders
may discard these fixed helpers. Thus the fibre is two-sided for
ρ₀(r)=ρ(r)∖H, whose forward and reverse degrees are at most w and R.

Enlarge to the symmetric relation σ=ρ₀∪ρ₀⁻¹, of window at most w+R.
Granting additional helpers preserves both recovery directions. Therefore,
if every symmetric two-sided code at window w+R has size at most q^a,
every original two-sided code satisfies

$$|C|\le q^{\,a+2d|H|-|H|^2}
       \le q^{\,a+2wd^2/(R+1)}.$$

For a common asymptotic rate bound, fix R from w and the desired slack
before taking d large. This preserves the alphabet quantifiers and makes
the payment arbitrarily small. **Symmetric and unrestricted two-sided
codes have the same best common asymptotic rate bound.** One may also
add all diagonal incidences, increasing the window by at most one.

Consequently a common deficit for symmetric, even reflexive, two-sided
hosts suffices for the native question through Section 1. This does not
preserve a literal finite bound with no slack, nor automatically transfer
a deficit that shrinks with the enlarged window. The reduction uses only
conditioning and relation enlargement; it does not make codes symmetric
or their decoders linear.

## 3. The cyclic host is exactly pairing plus one

**Theorem.** For every d≥2 and every q≥2, the host
ρ(r)={r,r+1 mod d} has two-sided maximum code size

$$\boxed{q^{\,d(d+1)/2+1}.}$$

Its full two-sided Shannon value is the same exponent.

**Upper bound.** Purchase every entry on or above the diagonal and the
additional cell (1,0). Rows 0 and 1 are complete, so forward recovery
supplies column 0. Column d−1 was already purchased; reverse recovery
from columns d−1 and 0 supplies row d−1. Descend through r=d−2,…,2:
column r is complete from its purchased upper entries and the recovered
rows below it, so columns r and r+1 supply row r. Rows 0 and 1 were
complete initially. This generates the array from d(d+1)/2+1 entries.
For d=2 the purchase already is the whole array. Zero conditional ranks
and singleton caps make this a Shannon proof as well.

**Lower bound.** In the cyclic group Q, choose an arbitrary symmetric
array S and an independent symbol t. Put X=S+tA, where A is 1 strictly
above the diagonal and 0 elsewhere. The upper-minus-lower difference
of any off-diagonal pair is t. Helpers r and r+1 expose such a pair,
including the wrap pair {d−1,0}. Having recovered t, row r determines
column r by its known transpose correction; the helper columns similarly
determine row r. The map is injective: t=X[0,1]−X[1,0], then S=X−tA.
No division or field assumption is used. ∎

Thus d=5 has value **16**, below one-sided 19 but above pairing 15.
For general d, the one-sided excess over pairing is d−1; the two-sided
excess is exactly one. This is a shared-symbol gain, not a positive-density
counterexample. For d≥3 only the diagonal is freely adjoinable in both
directions; the 2d one-sided loop cells cannot all be treated as free.
At d=2 every cell is a self-helper in both directions.

## 4. Symmetric hosts and the second calibration

Each member of a pair (p,c),(q,m) is a helper for the other in both directions precisely when
q∈ρ(c), p∈ρ(m), c∈ρ(q), and m∈ρ(p). On a symmetric incidence relation,
every mutual-helper clique therefore serves both directions with its
same sum-zero relation. The chosen code need not be transpose-invariant.

The basis host at d=8 has an existing partition into 24 free loop cells,
16 disjoint mutual pairs and two four-cell mutual cliques. Its
all-alphabet code has q^(24+16+2·3)=q^46 words and is two-sided. The
existing 18-cell acyclic witness bounds the larger one-sided class and
its Shannon relaxation by 64−18=46. Hence **two-sided capacity and Shannon
value are exactly 46**, above pairing 44.

Fano indexed by the polarity i·j=0 is symmetric too. Its triangle lane
code remains two-sided, so its two-sided Shannon value is 119/3.
Attainment uses three lanes over any base alphabet, equivalently
cube-sized cell alphabets; scalar attainment for every q is not asserted.
On ρ(r)=[d]∖{r}, one diagonal sum-zero check gives d²−1 symbols in both
directions. Growing-window counterexamples therefore still apply.

The [exact controls](../tools/two_sided_controls.py) replay the cyclic
recovery/generator certificates, the saved basis partition and acyclic
upper witness, and the Fano lane-support check. No new LP was needed.

## 5. Finite inequalities and their limits

**Rows without a symmetric incidence.** Put ρ²(p)=⋃_{c∈ρ(p)}ρ(c),
R={p:p∉ρ²(p)}, and a_p=|ρ²(p)∩R|. Row p is determined by columns ρ(p),
hence by rows ρ²(p). Consequently

$$\log_q|C|\le d^2-d\sum_{p\in R}\frac1{a_p+1}
 \le d^2-\frac{d|R|}{w^2+1}.$$

Order R uniformly at random and keep p when it precedes all its
out-neighbours in R. The kept set is acyclic and has expected size
Σ_p1/(a_p+1). One such set is recoverable in reverse topological order
from the other rows. This improves the independent-set denominator
2w²+1 in the initial proposal.

Absence of symmetric incidences alone does not force vanishing rate.
For d=3m, let ρ advance each index around one of m disjoint directed
three-cycles. Assign an independent symbol to each unordered pair of
cycles, constant on the corresponding matrix block or transposed blocks.
This gives a two-sided code of size q^(m(m+1)/2), with limiting rate 1/18.
Random relabelling preserves it. This is not the iid random w-choice
model; that model is not decided here. The single estimate s^(w²)
for a potential closure step proves no vanishing-rate claim.

**Common functions and the rectangle bound.** With singleton entropy
caps one, put Δ=d²−H(X). For row set S and column set T put U=S×T and

$$V=\{(p,c):\rho(c)\subseteq S,\ \rho(p)\subseteq T\}\setminus U,
 \qquad \Delta_U=|U|-H(X_U).$$

X_V is a common function of the rows S and columns T. The sharper bound is

$$|V|\le\Delta-\Delta_U+
 I(X_{\mathrm{rows}\ S};X_{\mathrm{columns}\ T}\mid X_U)
 \le2(\Delta-\Delta_U)\le2\Delta.$$

Write the bundles as U∪A and U∪B with A,B disjoint. Unit caps and
completion outside their union give I(A;B|U)≤Δ−Δ_U. Since V∩U=∅,
completion also gives H(V|U)≥|V|−Δ+Δ_U. The common-function condition
bounds H(V|U) by I(A;B|U). These are Shannon inequalities. If one bundle
contains the other, the conditional mutual information is zero and the
stronger |V|≤Δ−Δ_U follows.

For a single target (p,c), the bundle intersection is **ρ(c)×ρ(p)**.
The original one-sided mutual-helper block is instead ρ(c)×ρ⁻¹(p),
where ρ⁻¹(p)={j:p∈ρ(j)}. These coincide for symmetric ρ, but not in
general. The earlier unqualified identification was false. Localisation
into either common block remains a proposed step, not a consequence
of the two recovery identities.

## 6. Consequences and next gate

Both requested tests are settled: cyclic drops from 19 to 16; basis
stays 46. The transfer survives, but the common-deficit question has not
become qualitatively weaker. The general cyclic theorem shows that its
additional constraint nevertheless has real finite content.

A next step needs an inequality using both directions beyond their
separate order bounds. By the paid normalization, symmetric relations
suffice for a common deficit. Their bundle intersection is the mutual
block, so localisation there is a concrete candidate tied to the full
question, not a further unbridged host restriction.
No such estimate, common deficit or unconditional native exclusion is
proved here. Once a capacity bound is available the existing native
transfer can be reused.

Repository searches found no prior same-helper-map two-advice reduction.
The “two-sided rules” in Paper 17 concern linear offsets on a line and
are different. The elementary translated-intersection counting identity
itself is not claimed as a new general combinatorial theorem.

## 7. Transported recovery, its closure limit, and a localisation consumer

Written by Fable and Astra, reviewed 14 November; not Lean-verified.

### 7.1 Transported intersections

Let C be any code on N coordinates over an alphabet of size q≥2. Identify
the alphabet with a cyclic group. For arbitrary coordinate permutations
Φ₁,…,Φ_{m−1}, where m≥1, some translated intersection

D = C ∩ ⋂ᵢ(zᵢ+Φᵢ(C))

has |D|≥|C|^m/q^((m−1)N). Count tuples of m codewords by their m−1
differences from the first. The intersection obeys all original and transported
recovery rules; coordinatewise translations preserve functional determination.
Consequently, if s coordinates generate the combined recovery closure, then

log_q|C| ≤ ((m−1)N+s)/m.

This concerns an intersection selected from C, not additional invariances of C
or of an unchanged native fibre.

**Cyclic intervals.** If ρ(r)={r,…,r+w−1} modulo d, one transported copy suffices
with s≤d·min(d,2w−1), for 1≤w≤d. Use Φ(i,j)=(j+2w−1,i). The transported
rule recovers row r+2w−1 from columns r,…,r+w−1. Seed the first 2w−1 rows
(or all rows if fewer exist). If rows 0,…,L are known, the original rules
recover columns 0,…,L−w+1; the transported rule at r=L−2w+2 then gives
row L+1. Continue without wrapping until all rows are known. Thus

log_q|C| ≤ (d²+d·min(d,2w−1))/2.

For w=1 this gives the exact pairing value. At w=2 the sharper exact one-sided
and two-sided results cited earlier retain their separate content.

**Triangle correction.** Two partitions into disjoint triples form a cubic
bipartite incidence multigraph, with cells as edges. If it has c components,
the combined triangle-recovery closure needs exactly N/3+c seeds. A spanning
forest leaves that many non-tree edges; knowing them allows leaf elimination.
For the lower bound, orient the bipartite incidence matrix: the common sum-zero
code has dimension N/3+c over every field. In particular a connected arrangement
gives 2N/3+1/2 through the intersection invoice, not exactly 2N/3. The original
triangle code itself still has rate 2/3. The earlier exact calibration omitted
this additive term.

### 7.2 A uniform limit of transported closure counting

**Proposition.** Suppose a d×d helper incidence graph has no empty r×r rectangle,
where 1≤r≤d. Put m arbitrarily permuted copies of its whole-column recovery
rules on the same N=d² cells. Every generating seed S for their combined closure
satisfies

|S| ≥ N−(m+1)d(r−1)+(r−1)².

**Proof.** If a grid already has d−r+1 complete rows in S, then
|S|≥d(d−r+1), which is stronger. Otherwise add recovered cells one at a time,
and stop the first time any grid has d−r+1 complete rows. Before that instant
every grid has at least r incomplete rows. In each grid at most r−1 columns
can have all their helper rows complete: r such columns and r incomplete rows
would give an empty rectangle. Readiness is monotone, so all cells recovered
up to and including the stopping step belong to at most m(r−1) ready columns,
one group of at most r−1 in each grid. Their union has at most md(r−1) cells.
For the sharper count, restrict to the d−r+1 complete rows in the first grid
that reaches the threshold. Its own used columns cover at most (d−r+1)(r−1)
cells there; the other grids cover at most (m−1)d(r−1). Subtract these from
d(d−r+1) to obtain the displayed bound. ∎

Thus every m-copy intersection bound obtained **only from these closure rules**
is at least

N−(1+1/m)d(r−1)+(r−1)²/m,

and at least (1−1/m)N since seed size is nonnegative. For m copies of a two-sided
code there are 2m grids, giving instead N−(2+1/m)d(r−1)+(r−1)²/m,
hence at least N−3d(r−1). These are lower bounds on what this proof method can certify,
not lower bounds on actual capacity or on the full Shannon optimum.

**Fixed-window witnesses.** For each fixed ε∈(0,1), let r=⌈εd⌉. A union of t
independent uniform perfect matchings misses a specified r×r rectangle with
probability at most exp(−tr²/d). There are at most 4^d rectangles, so for fixed
t with tε²>2 ln 2 some such graph has no empty r×r rectangle for every sufficiently
large d. Add its transpose and diagonal: the relation is symmetric and reflexive,
its window is at most 2t+1, and the rectangle property persists. Since ε can be
arbitrarily small, transported closure counting cannot establish a common
positive deficit even on these normalized hosts, allowing arbitrarily many copies
and arbitrary coordinate permutations. This replaces the earlier unproved
percolation heuristic. It says nothing against submodularity across closure
intersections, extra code identities, or other tools beyond closure generation.

A subsequent [assigned-rule theorem](transported-closure-native-audit.md#1-assign-each-recovered-coordinate-to-the-rule-that-supplied-it)
shows, for every helper graph, that transported closure counting cannot improve its
optimal original acyclic-set bound. The rectangle argument above additionally gives
its stated m-dependent quantitative bound on the same witnesses.

### 7.3 Odd mutual walks and the proposed clique obstruction

On a symmetric relation G, the **full, loop-allowing** mutual relation on cells
is (p,c)∼(q,m) iff q∈N(c) and m∈N(p). A closed walk of odd length ℓ through
(p,c) exists exactly when G has a length-ℓ walk from p to c. Each step moves two
tokens along G and exchanges their roles. After odd ℓ, closing the cell walk
requires one G-walk from p to c and another from c to p; reverse the first to
obtain the second.

The equivalence need not survive deleting incident cells or loops. The direction
needed for an upper-bound argument does survive: an odd closed walk in any
induced far-cell relation implies the corresponding G-walk. Thus cells at distance
more than L lie on no odd cycle of length at most L. If G is bipartite, cells with
both indices on the same side lie on no odd closed walk.

The proposed chained-clique example does **not**, as stated, rule out a paid
localisation estimate. Equating the sums of L disjoint k-cliques gives L−1
independent checks and rate 1−1/k+1/(kL); adjacent sum-zero checks instead have
rank depending on parity and characteristic. Moreover, revealing the one common
clique sum makes each cell recoverable from its other clique coordinates. Such
examples may obstruct an unconditioned estimate, but do not force a large constant
when a suitably charged record Z is permitted. No general localisation obstruction
is proved by this example.

### 7.4 Conditional entropy gives an exact subcode

The proposed localisation premise is

Σ_v H(X_v | X_{H_v},Z) ≤ K·Δ,

where H_v is the desired helper set (for example the mutual block), Δ=N−H(X),
and all entropies use base q. Here is its precise consumer.

**Subcode selection lemma.** For any finite random array X and helper sets H_v,
there is an exact storage code D contained in supp(X) such that

log_q|D| ≥ H(X)−Σ_v H(X_v | X_{H_v}).

For each v and each helper pattern h, independently choose a decoder value
with distribution P(X_v | X_{H_v}=h). A source word x satisfies all chosen decoders
with probability a_x=∏_v P(X_v=x_v | X_{H_v}=x_{H_v}). Therefore the expected
number of accepted words is Σ_x a_x. With p_x=P(X=x), the log-sum inequality gives

log_q Σ_x a_x ≥ Σ_x p_x log_q(a_x/p_x)
             = H(X)−Σ_v H(X_v | X_{H_v}).

Some decoder choice has at least this many accepted words, which form D. ∎

With a finite record Z, choose a fibre maximizing the difference of these
conditional quantities. The same proof gives a subcode of one fibre with

log_q|D| ≥ H(X)−H(Z)−Σ_v H(X_v | X_{H_v},Z).

This is an existential large subcode, not an advice scheme recovering every
original source word. If near coordinates are deleted, freeze them first and
include their entropy in the payment. The lemma preserves the specified helper
relation but need not preserve linearity, coefficient bounds or decoder symmetries.
Thus the general mutual-only capacity question remains open: the bounded-weight
complex theorem is not an automatic consumer, and hyperfiniteness or bounded
sector components must be independently established when those theorems are used.
Localisation alone does not settle the native crux.
