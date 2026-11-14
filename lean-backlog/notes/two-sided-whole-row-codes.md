# Two-sided whole-row codes and the one-sided deficit

Claude Fable 5.2 and GPT-6 Astra, directed by Hans Brende, 14 November 2026.
**Status: independently reviewed written proofs, not Lean-verified.**
The transfer reuses the existing Lean theorem after a new, still unformalized
finite adapter. No literature novelty claim. Front D10 of the [roadmap](../wall.md).

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

**Formalization boundary.** [ConeCodeTransfer](../ConeCodeTransfer.lean)
and [RowSpreadCrux](../RowSpreadCrux.lean) are Lean-verified. The new
two-sided predicate and Section 1's adapter are not yet formalized.
The existing real fibre-counting lemma can be reused on C×C and
(x,y)↦x−yᵀ; no new native-machine development is needed.

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

## 7. The intersection lemma in general, odd walks, and the localisation gate (Fable, 14 November; unreviewed)

**7.1 Transported intersections.** Let C be any code on N coordinates over a cyclic alphabet of
size q, with recovery rules "the cells T are determined by the cells H". Let Φ₁, …, Φ_k be
arbitrary bijections of the coordinate set. Then for some z₁, …, z_k the code
D = C ∩ ⋂ᵢ (zᵢ + Φᵢ(C)) has |D| ≥ |C|^{k+1}/q^{kN}, and it obeys every rule of C together with
every transported rule "Φᵢ(T) is determined by Φᵢ(H)". (Count tuples in C^{k+1} by their
differences.) So, with gen the least size of a generating set of the combined closure system,

log_q |C| ≤ (kN + gen)/(k + 1).

Transposition is one Φ. Independent relabellings of rows and of columns are others, and they are
also symmetries of the transposition problem, so native fibres have them too.

*Calibrations.* (i) Window one, ρ(c) = {c}: take Φ = transposition followed by a relabelling for
which "row r is determined by row r+1". One row generates everything, gen = d, and the bound is
d(d+1)/2, the exact value. (ii) Disjoint triangles: a second triangle system can be chosen so that
a third of the cells generate the rest; the bound is 2N/3, exact. (iii) Cyclic intervals
ρ(c) = [c, c+w): a shifted transposed copy cascades from 2w−1 rows; the bound is d²/2 + O(wd).

*Limit.* A transported column rule outputs full lines of its own grid, which are thin in the rows
of that grid and freely placeable in the others. If m rows contain at most λm columns (λ < 1 on
expanding hosts, about 1/(w−1) for tree-like clusters), the number of new complete rows per round
is multiplied by kλ with k+1 grids. Percolation needs k + 1 of order w, and the bound is then
of order 1 − 1/w again. **So transported intersections give normal forms and exact values on
Følner-type hosts, and no window-independent deficit on expanders.**

**7.2 Odd walks in the mutual graph.** On a symmetric relation G the mutual graph on cells is
(p,c) ~ (q,m) iff q ∈ N(c) and m ∈ N(p). A closed walk of odd length ℓ through (p,c) exists iff
G has a walk of length ℓ from p to c. So a cell with dist_G(p,c) > L lies on no odd cycle of
length ≤ L, for every symmetric host; if G is bipartite, cells with both indices on one side lie
on no odd cycle at all. This is the sector-walk statement without a group.

**7.3 The localisation gate is not passed.** The target was Σ_v H(X_v | block of v, Z) ≤ K·Δ for
a record Z of small entropy and K independent of the window.

- It needs the record: the cyclic code X = S + tA is local only given t.
- *Chained half-cliques.* Let Q₀, …, Q_{L−1} be mutual k-cliques of cells with every row of Q_{i+1}
  adjacent to every column of Q_i, and impose one check on each Q_i ∪ Q_{i+1} (indices mod L,
  L ≥ 3). Each cell is recovered row-wise from one check and column-wise from the other; the code
  has rate 1 − 1/k, and a cell is determined by its block only up to the sum over its clique,
  which is carried along the chain. So K ≥ k whenever such chains cover the cells, and the
  record costs N/(kL).
- With K ≥ w + 1 the inequality follows from the order bound. So a useful statement has to be
  restricted to cells far from the diagonal, where mutual cliques are pairs, and I have no proof
  there: Shearer over the bundles is vacuous, and 7.1 does not help.

**7.4 What would consume it.** Given localisation at far cells, a code of rate 1 − ε is within
K·ε·d² + H(Z) of a mutual-only storage code on the far part of the mutual graph, which by 7.2 has
odd girth tending to infinity. Consumers we have: bounded-weight linear codes over ℂ (item A,
Lean), hyperfinite G, groups with bounded sector coupling. For general mutual-only codes on these
graphs the half bound is the old open problem (I2, D8), and its abstract analogue is false
(papers 13, 15). So localisation would remove one-way help but not the remaining hypotheses.
