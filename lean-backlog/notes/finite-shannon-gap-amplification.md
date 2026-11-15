# Finite Shannon gaps persist at fixed window

14 November 2026. GPT-6 Astra, following the Fano certificate developed
with Claude Fable. **Status: deterministic macro projection and conditional
comparison against every induced acyclic-set invoice Lean-verified; random existence and the girth refinement
remain written proofs, independently reviewed.** No claim of literature
novelty is made. The general order/acyclic-set identification from Paper 17
is now Lean-verified, strengthened to containment on rectangular arrays.

A finite gap between Shannon and order bounds need not disappear as the
matrix grows, even when both incidence degrees stay fixed. This note
proves a general amplification theorem and applies it to the
[Fano gap](fano-shannon-certificate.md). The resulting improvement exceeds
one percent of all cells. It separates the strength of two proof methods;
these particular hosts already have a constant order-based deficit.

## 1. Definitions and statement

Logarithms in the matching and probability estimates are natural logs.
Entropy units are specified separately when used.

A whole-row host of dimension s has a helper set ρ(j) of rows for each
column j. Every cell of column j is recoverable from the entries in
those rows. Write Sh(ρ) for the maximum rank of the full grid over
normalized, monotone, submodular set functions with singleton ranks at
most one and the column-recovery equalities. This includes normalized
entropy of every whole-row code over every finite alphabet.

The order bound is

$$\sigma(\rho)=\min_{\pi}\sum_j\max_{i\in\rho(j)}\pi(i),$$

where π is a bijection from the rows to {1,…,s}, and max ∅=0. By
[Paper 17's whole-row order proposition, part (b)](../../Order-Symmetry-and-the-Swap-A-Synthesis-of-Matrix-Transposition-on-Tapes/paper/sections/symmetry.tex),
this is s² minus the maximum size of an induced acyclic set of cells.
Thus optimizing the row order already gives the best acyclic-set bound.

**Finite-gap amplification theorem.** Fix a base host ρ₀ with s rows,
e₀ incidences, forward degree at most w₀ and reverse degree at most w′₀.
Suppose Sh(ρ₀)≤U<S=σ(ρ₀). Choose η∈(0,1) and an integer t such that

$$ (1-\eta)^2S>U,\qquad t\eta>2\log(\mathrm e/\eta). $$

For every sufficiently large n there is a host ρₙ of dimension d=sn,
with forward and reverse degrees at most tw₀ and tw′₀, satisfying

$$\boxed{\operatorname{Sh}(\rho_n)\le n^2U,
\qquad (n-\lceil\eta n\rceil+1)^2S
       \le\sigma(\rho_n)\le n^2S.}$$

The hosts can also be chosen so that their **bipartite incidence girth
is Ω(log n)**, at the same degree bounds. In particular their residual
cell relation has no mutual triangle for all sufficiently large n.

In particular,

$$\sigma(\rho_n)-\operatorname{Sh}(\rho_n)
\ge\frac{(1-\eta)^2S-U}{s^2}\,d^2.$$

The construction below succeeds with probability tending to one. The
Shannon upper bound requires neither linearity nor symmetry of a code
or its decoder. It does **not** assert that the base capacity, or the
base upper bound, is attained on the sparse host.

## 2. Sparse incidences and a mixing condition

Replace each base row i by a group Rᵢ of n rows and each base column j
by a group Cⱼ of n columns. For each base incidence i∈ρ₀(j), take t
independent uniformly random perfect matchings between Rᵢ and Cⱼ.
Their union specifies which fine rows help each fine column. Repeated
edges are discarded; both degree bounds follow immediately.

Put r=⌈ηn⌉. We require the following property on each base incidence:
**every r rows of Rᵢ and every r columns of Cⱼ have an edge between
them.** For fixed r-subsets, the probability that one matching avoids
the rectangle is

$$\frac{\binom{n-r}{r}}{\binom nr}
\le (1-r/n)^r\le\exp(-r^2/n),$$

with probability zero when 2r>n. A union bound therefore gives

$$\Pr[\text{some required rectangle is empty}]
\le e_0\binom nr^2\exp(-tr^2/n).$$

Let τ=r/n. The estimate binom(n,r)≤(e/τ)^(τn) bounds this by

$$e_0\exp\{-n\tau[t\tau-2\log(\mathrm e/\tau)]\}
\le e_0\exp\{-n\eta[t\eta-2\log(\mathrm e/\eta)]\}.$$

The last inequality holds because τ≥η and the bracket is positive at
η and increases with τ. Our assumption makes the final exponent a
negative constant times n. Hence all sufficiently large sizes admit
the required mixing property. No expander theorem or computational
search is needed.

### Removing short cycles without changing the degree bound

The strict assumption on t lets us choose a fixed η₀<η with
tη₀>2 log(e/η₀). First impose the rectangle property at
r₀=⌈η₀n⌉ instead of r=⌈ηn⌉. We will isolate o(n) vertices while
retaining every row and column label. The final rectangles of size r
will still contain rectangles of size r₀ on unisolated vertices.

Put K=4st and g=⌊log n/(4 log K)⌋. Count simple cycles of length
ℓ≤g in the underlying simple incidence graph, assigning each cycle
edge one of its witnessing matching colors. There are at most
(2s)^ℓ choices of base vertices, t^ℓ choices of colors, and n^ℓ
choices of fine vertices. In a valid simple cycle the constraints on
any one random matching are either inconsistent or prescribe m
distinct images at distinct arguments, with probability 1/(n)_m.
For n≥2g this is at most (2/n)^m. Multiplying over the independent
matchings bounds the probability of the ℓ prescribed edges by
(2/n)^ℓ. Thus the expected number of simple ℓ-cycles is at most K^ℓ.
This overcounts orientations and starting vertices, which only helps
the upper bound. Repeated edges and length-two walks are not cycles
in this simple graph.

Summing over 4≤ℓ≤g gives expectation at most
[K/(K−1)] n^(1/4). By Markov's inequality there are fewer than √n
such cycles with probability tending to one. Simultaneously the r₀
rectangle property holds with probability tending to one. Choose one
vertex from each short cycle and delete all edges incident with these
chosen vertices, keeping the vertices as isolated labels. No short
cycle remains and no new cycle is created.

For sufficiently large n, any r rows and r columns of an incident
clone-group pair retain at least r−√n≥r₀ unisolated vertices on each
side. Their original mixing edge has unisolated endpoints and survives.
Consequently the final host has the r-rectangle property needed below,
girth greater than g, the same degree bounds, and the same coarse
helper containment. All Shannon and order conclusions therefore survive.

A mutual triangle of nonincident cells must have three distinct point
rows and three distinct column labels; otherwise two of its cells
could not mutually help. Its six cross-incidences form a simple
six-cycle in the incidence graph. Girth greater than six excludes
such triangles. This removes fine-scale triangles; an optional coarse
quotient can still contain triangles, as the Fano quotient does.

## 3. Aggregating cells preserves the Shannon upper bound

Partition the fine grid into s² blocks Bᵢⱼ=Rᵢ×Cⱼ, each containing n²
cells. Given a feasible fine polymatroid h, define

$$g(A)=\frac1{n^2}h\left(\bigcup_{(i,j)\in A}B_{ij}\right).$$

Because these blocks form a partition, unions and intersections are
preserved. Thus g is normalized, monotone and submodular. Subadditivity
and the fine singleton caps give g({(i,j)})≤1.

For a base column j, every fine column in Cⱼ has all its helper rows
in the union of Rᵢ over i∈ρ₀(j). Call the full set of cells in those
rows Qⱼ. A zero conditional rank stays zero after enlarging the
conditioning set, by submodularity. Each fine column is consequently
determined by Qⱼ, and so is their union. These are exactly the base
column-recovery equalities for g. Therefore g(full)≤U, proving
h(full)≤n²U.

This step grants each fine column all the information in its macro
helper rows. That is valid for an upper bound; there is no converse
claim that a base code can be recovered from the sparse fine helpers.

## 4. Every fine row order still pays almost the base order cost

Set a=n−r+1 and fix any order of the fine rows. Let τᵢ be the position
of the a-th visited row in Rᵢ. These distinct thresholds induce an
order π of the s row groups. If π(i)=k, then at least a rows have been
visited in each of k groups by time τᵢ. Hence τᵢ≥ka.

For a base column j with nonempty helper set, put
τⱼ*=maxᵢ∈ρ₀(j) τᵢ and choose a group attaining this maximum. **Just
before** τⱼ*, that group still has r unvisited rows. There can be at
most r−1 columns of Cⱼ whose fine helpers have all been visited: r
such columns and the r missing rows would be an empty rectangle.

At least n−r+1=a columns in Cⱼ therefore have last-helper position at
least τⱼ*. Their combined order cost is at least

$$a\tau_j^*\ge a^2\max_{i\in\rho_0(j)}\pi(i).$$

Empty helper sets contribute zero. Summing over j gives cost at least
a²S for every fine order. Since a≥(1−η)n, this also proves the claimed
density bound. The strict-before convention is the reason for the +1
in a=n−r+1.

Conversely, order whole fine row groups contiguously in a base order
attaining S. Every column of Cⱼ then has last helper at position at
most n maxᵢ∈ρ₀(j)π(i). Summing over its n columns gives σ(ρₙ)≤n²S.
This last upper bound does not require mixing.

The mixing condition also rules out a small-separator explanation. If
η<1/2, one cannot delete o(n) vertices of the bipartite helper-incidence
graph and leave only components of size o(n). Indeed, fix a base edge
and color the remaining components independently red or blue. Each of
its two clone groups retains n−o(n) vertices. If the largest component
has size M=o(n), the variance of its red count is at most nM/4=o(n²),
and the same holds for the blue count. With positive probability at
least r row clones are red and r column clones are blue. There is no
edge between them, contradicting mixing. This is a statement about
this incidence graph, not about every possible cell or cone graph.

## 5. Fano: a gap greater than one percent

For the Fano base take

$$s=7,\quad U=119/3,\quad S=41,\quad e_0=21,
\quad w_0=w'_0=3,\quad\eta=1/100,\quad t=1200.$$

For the unaltered construction, the mixing failure probability is at most

$$21\exp\{-n(10-2\log100)/100\},$$

which tends to zero. The resulting hosts have both incidence degrees
at most **3600**, and, with d=7n,

$$\operatorname{Sh}(\rho_n)\le\frac{17}{21}d^2,
\qquad
\sigma(\rho_n)-\operatorname{Sh}(\rho_n)
\ge\frac{15523}{1470000}d^2>\frac1{100}d^2.$$

These are finite inequalities for every successful lift, not only
limiting rates. The exact coefficient follows from
41(99/100)²−119/3=15523/30000 and d²=49n².

The growing-girth version keeps the same degree 3600 and the same gap:
one may take η₀=1/105 in the short-cycle deletion argument. Indeed,
1200η₀=80/7>2 log(105e). No new host search or stronger degree budget
is needed for this additional property. The modified family has girth
Ω(log d) and has no residual mutual triangles eventually.

The new conclusion is a positive-density improvement over the **best**
order bound on a growing fixed-window family. The same hosts already
obey σ≤(41/49)d², so ordinary order arguments already exclude rates
above 41/49 there. The theorem does not newly rule out rates approaching
one on an otherwise unrestricted family. It refutes an asymptotic
Shannon/order-equality claim for every fixed-window family, not the
possibility of near-order witnesses on other families.

## 6. Paid aggregation and the remaining premise

The [soft-recovery inequality](fano-soft-recovery.md) also applies to
the macro blocks when they are not exactly recoverable. Let Z collect
the 21 incident Fano blocks, each of size n², and write Xᵥ for each of
the 28 residual blocks. Let Hᵥ be the twelve residual blocks in its
three macro helper rows, and set εᵥ=H(Xᵥ∣X_Hᵥ,Z), in logarithm-base-q units.
Then, for any joint distribution on the fine grid,

$$H(X)\le\frac{119}{3}n^2+\frac13\sum_v\varepsilon_v.$$

Here the cells have alphabet size at most q, and q≥2. Shared outside
advice may instead be conditioned once and charged by its joint
entropy, as in that note. This gives a precise hypothesis for an
imperfect coarse Fano pattern; it does not supply a cheap error budget.

What remains for the transposition problem is a property of a much
broader family of hosts or native cone systems that supplies such
structure with small enough cost. In particular, the theorem supplies
no Fano quotient for arbitrary native schedules. Another useful route
would be bases whose order rates approach one while their Shannon
rates have a uniform deficit. The projective-plane conjecture would
provide such bases, but is proved here only for Fano.

## 7. Lean coverage and remaining effort

The deterministic stages are complete. The series and installed Lean
libraries were checked before implementation. No new host search or
numerical work was used; permutation counting and girth are stopped at
their existing written proofs.

[`MacroProjection.lean`](../MacroProjection.lean) proves `upper_of_projection`
for arbitrary row and column maps with a common positive bound on macro-cell
fibre size. The maps need not be onto and fibre sizes need not be equal.
`fano_upper_of_projection` also permits cap zero, and `fano_clone_upper`
allows rectangular clone counts n,m, giving 3h(full)≤119nm.

[`LiftOrder.lean`](../../lean-machine/LeanMachine/WholeRow/LiftOrder.lean)
proves `cost_ge_base_order` and `cost_ge_of_base_bound`. Both use one-based
last-helper positions, with zero cost for an empty helper set. With n clones
per group and 1≤r≤n, rectangle mixing above each base incidence gives the
lower bound a²S for **every** fine order, where a=n−r+1. The proof constructs
the induced base order from distinct arrival thresholds; the statement
does not assume that order or its threshold inequalities. Helper containment
is not needed for this lower bound. `rectangleMixing_iff_exact` identifies
the at-least-r rectangle interface with exactly r rows and r columns.
`cost_clone_order_le` proves the converse n² comparison by a contiguous
clone-group order under helper containment, without mixing.

[`FanoLift.lean`](../FanoLift.lean) connects these statements to the actual
Fano incidence and its checked order value 41. It proves the finite gap

$$\operatorname{cost}(\pi)-h(\mathrm{full})
\ge41(n-r+1)^2-\frac{119}{3}n^2$$

for every feasible fine polymatroid h and every fine order π. Under
99n≤100(n−r+1), `conditional_gap_one_percent` gives 15523n²/30000,
and `gap_coefficient_gt_one_percent` proves that this exceeds (7n)²/100
for n>0. `conditional_acyclic_gap` and its strict one-percent corollary
make the same comparison against every induced acyclic-set invoice, using
the shared exact identification below. These are not a lower bound on the
fine Shannon value or a fixed-degree construction.

For non-vacuity, `completeLift` takes all clones of every incident base point.
Lean proves containment, rectangle mixing at r=1, width exactly 3n, and
gap at least (4/3)n² for n≥1. The two predicates `FanoOrder.line` and
`FanoCertificate.incident` are the same base incidence. This explicit lift
has growing window and does not replace the sparse existence argument.

The entropy aggregation has a direct existing consumer. Paper 4's
[polymatroid library](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/lean/MotionDepthCodes/Polymatroid.lean)
already proves `IsPolymatroid.pushRank`, `IsValid.pushRank` and
`pushRank_univ`: map each fine cell to its macro cell and take preimages
of sets. Helper containment is exactly the validity-transfer premise.
A macro singleton has n² cells, so its rank is at most n². Applying
[`FanoFull.full_upper_of_cap`](../FanoFull.lean) with cap n² gives
3h(full)≤119n² directly. No new partition-submodularity argument or
normalization by n² is needed for this first endpoint. For a base already
supplied with a homogeneous weighted rate bound, Paper 4's
`RateBound.of_hom` transfers that bound directly. An arbitrary unit-cap base
bound U is transferred by the scalar rescaling in `upper_of_projection`.

| Milestone | Actual reuse and missing work | Relative effort and completion criterion |
|---|---|---|
| Deterministic macro upper bound | Paper 4 push-forward/validity, scalar rescaling, finite fibre sizes, checked Fano cap | **Lean, complete:** `MacroProjection`. Arbitrary supplied helper-containment maps and bounded fibres. |
| Every-order comparison, conditional on rectangle mixing | Finite arrival-threshold counting in shared `LiftOrder`; [`FanoOrder.exact_last_helper_value`](../FanoOrder.lean) supplies 41 | **Lean, complete:** induced base order and a² lower comparison; separate contiguous-order n² upper comparison. |
| Existence of bounded-degree mixing lifts | [`FiniteUniformProbability`](../../lean-machine/LeanMachine/FiniteUniformProbability.lean) supplies finite product averages and union bounds. [`BlockRanking`](../../lean-machine/LeanMachine/BlockRanking.lean) counts other permutation events, but not rectangle avoidance. New work: uniform restriction/image counts for permutations, the product construction, both degree bounds and the eventual failure estimate. | Substantial. First prove the exact avoidance probability, then the finite failure bound and eventual existence without the girth refinement. |
| Same-degree logarithmic girth | Reuse the permutation restriction count. New work: finite colored cycle witnesses, repeated matching colors, expected short-cycle count, isolation, and survival of larger rectangles. | Largest uncertainty; a separate substantial stage after existence. Use no-short-cycle or extended-girth predicates, since ordinary Mathlib girth is zero for acyclic graphs. |
| Fano constants and comparison | Existing Fano upper/order endpoints and exact rational arithmetic | **Lean, complete conditional gap:** `FanoLift`. Degree 3600, eventual existence and the needed logarithmic estimates remain in the written construction. |

The installed Mathlib has finite permutation and embedding counts,
falling factorials, factorial/binomial estimates, finite uniform laws and
graph girth. The bounded audit found no theorem that already combines
them into this random-matching or random-lift construction. In particular,
independent-edge random graphs do not supply the required degree bounds.
The crude bound binom(n,r)≤2ⁿ could give a weaker existence theorem with
larger degree, but does not prove the displayed degree-3600 result.

The general Paper 17 identification is now checked in shared
[`AcyclicOrder.lean`](../../lean-machine/LeanMachine/WholeRow/AcyclicOrder.lean),
with a stronger rectangular containment statement: every acyclic cell set
lies in one induced by a row order. The maximum acyclic-set size is exactly
total cells minus minimum cost. Directed acyclicity is defined by absence
of nonempty closed walks, including loops; its equivalence with a rank
certificate is proved in `RecoveryAcyclic`. Thus the comparison with
**every acyclic-set bound** has no remaining written dependency.
The optional small-separator argument and paid macro-error extension are
separate from the first milestone. Neither supplies a native quotient or
an error budget.

**Stopping point.** Stages 1 and 2 are banked; do not start permutation or
cycle counting without a new decision. Full B3 remains partially formalized.
The conditional deterministic theorem banks the existing method separation
and reusable machinery without advancing the common deficit on arbitrary
hosts. The sparse lifts still inherit their base's constant order deficit,
and their Shannon upper bound is not asserted to be attained.
