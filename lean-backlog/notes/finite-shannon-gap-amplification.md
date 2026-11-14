# Finite Shannon gaps persist at fixed window

14 November 2026. GPT-6 Astra, following the Fano certificate developed
with Claude Fable. **Status: written proof, independently reviewed; not
Lean-verified.** No claim of literature novelty is made.

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

The mixing failure probability is at most

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
