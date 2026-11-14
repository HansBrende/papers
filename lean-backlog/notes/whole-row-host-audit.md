# The linear whole-row host: blocks and finite benchmarks

Hans Brende and GPT-6 Astra, 14 November 2026. Front D1.

This audit distinguishes the unrestricted linear host from prescribed
sparse supports. The block arguments and cyclic-family construction
are **written proofs, not Lean-verified**; the finite results retain
their original scopes. No new optimizer was run, and no new asymptotic
capacity bound is claimed. The host is one restriction from the wall
(linearity); scalar entries impose an additional restriction when the
native alphabet consists of several bits.

## 1. Which linear problem is unrestricted

For a row relation $\rho$, let $x_r$ be column $r$ of $X$ and $y_i$ its
row $i$. As proved in [row spread §17.2][host], every linear whole-row
code is contained in a kernel with equations

$$x_r=\sum_{i\in\rho(r)}\Phi_{r,i}y_i.$$

The full kernel is itself a code, so optimizing its dimension over all
blocks gives exactly the maximum linear dimension. The blocks are
arbitrary $d\times d$ matrices for scalar entries, or $db\times db$
matrices for $b$ scalar lanes. Binary-linear recovery on $b$-bit entries
need not be scalar-linear over $\mathbb F_{2^b}$.

Three restrictions must be kept distinct: a preselected sparse support;
one freely chosen weighted partial-permutation block per edge of $\rho$;
and just one helper scalar coordinate **in total** per output scalar
coordinate. The second allows one helper scalar coordinate in each of
up to $w$ helper rows. At scalar width these are matrix entries; with
lanes, they are individual lane coordinates. A weighted partial
permutation has at most one nonzero in each row and column; zeros and
arbitrary field weights are permitted.

## 2. What reduction to permutation-like blocks is valid

**Proposition.** A square matrix with at most $q$ nonzeros in each row
and column is a sum of $q$ weighted partial-permutation matrices, over
every field. Thus a host block can be replaced by parallel summands of
this kind without changing the host, decoder or code.

*Proof.* The support is a bipartite graph of maximum degree $q$.
For $q>0$, add dummy edges, allowing parallel dummy edges, until all
degrees are $q$. The two sides have equal total degree deficit.
Hall's condition follows by counting the $q|S|$ edges from any vertex
set $S$ into its neighbourhood, whose total degree is $q|N(S)|$.
Delete a perfect matching and repeat. The original edges are partitioned
into $q$ matchings; give each its original matrix weight and discard
the dummy edges. The case $q=0$ is the empty sum. ∎

This is the usual bipartite matching argument; it uses the same
[Hall theorem][Hall] as the simultaneous-row criterion. A support with
both actual degrees at most $\Delta$ has $q\le\Delta$ in every block.
An arbitrary dense block may need $q=d$, or $q=db$ with lanes: a fully
nonzero row cannot be a sum of fewer than that many one-entry rows.
Separate per-block degree bounds need not bound the whole decoder's
degrees by the same constant. Nor does a bound on the kernels of the
individual summands give a bound for their sum.

**A code-preserving one-block reduction is false.** Over every field,
take

$$C=\left\{\begin{pmatrix}a&b\\a+b&0\end{pmatrix}:a,b\in F\right\},
       \qquad \rho(1)=\rho(2)=\{1\}.$$

Row one ranges freely over $F^2$, so its maps to the two columns are
forced to be

$$\Phi_{1,1}=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
  \Phi_{2,1}=\begin{pmatrix}0&1\\0&0\end{pmatrix}.$$

Their full kernel is exactly $C$. The entry $a+b$ cannot be recovered
from either $a$ alone or $b$ alone, even by a nonlinear function with
a fixed single-helper choice. Thus no one-entry-per-block-row decoder,
and in particular no weighted partial-permutation block, preserves this
code on this host.

This does **not** separate optimal capacities of the two decoder
classes. Both columns are determined by row one, so the host has maximum
dimension two. The different code
$\{\left(\begin{smallmatrix}a&b\\b&a\end{smallmatrix}\right):a,b\in F\}$
attains two with an identity block and a swap block. Whether an optimal
code on every host can be chosen with one weighted partial permutation
per host edge is not decided here.

## 3. What the earlier experiments actually certify

| Host or experiment | Certified conclusion | Scope |
|---|---|---|
| Initial shear controls, $d=7,11,13$, windows $3,4,5$ | 29 of 30 exact capacities; one interval remains | Prescribed sparse helper graphs, every finite alphabet; no dense coefficient search |
| Fano incidence, $d=7,w=3$ | Scalar-linear dimension exactly 39 over $\mathbb F_2$ and $\mathbb F_3$ | Unrestricted dense blocks; computer-assisted proofs, not Lean |
| Same Fano host, three binary lanes | 119 free bits out of 147; normalized exponent $119/3$ | Vector construction; general alphabet-eight upper bound 41 |
| Basis hosts on $\mathbb F_2^s$, $s=2,3,4$, $w=s$ | Exponents exactly 12, 46, 176 | Full hosts, every finite alphabet, nonlinear recovery allowed |
| Cyclic $\rho(r)=\{r,r+1\}$, every $d\ge2$ | Exponent exactly $d(d+3)/2-1$ | Every finite alphabet; attains the universal whole-row window-two upper bound |
| Clebsch host, $d=16,w=5$ | Binary exponent at least 210; all-alphabet upper 211 | General cross-diagonal gain remains open |
| Projective-plane host, $d=13,w=4$ | Exponent at least 130 | Exact optimum for disjoint clique gadgets only |

**Sparse shear controls.** Their arcs are
$(c,r)\to(i_a(r),c+j_a(r))$. An induced acyclic set in this graph need
not stay acyclic when every entry of row $i_a(r)$ is made available.
Therefore its upper bound does not transfer to the dense host. In the
saved P/N comparison the row maps $i_a$ are identical; only the offsets
differ. P and N consequently define the **same** dense host.
The [note and certificate][shear] specify the residual interval and
reproduction command. Its 30 DAG/cycle-packing certificates were replayed
in this audit; 29 have matching bounds.

**Fano.** There are 21 free loop cells and 28 nonincident cells.
The residual fitting matrix is $28\times28$, with every allowed
coefficient free. Its exact minimum rank is 10 over both fields.
The lower code is eight disjoint triangles and two pairs, plus the
loops; the rank-nine exclusions have checked Boolean proof traces.
The [proof and certificate instructions][simplex] distinguish scalar
39, vector $119/3$, and nonlinear upper 41. The rank-ten control and the
13,964-addition binary proof were replayed in this audit. The large
ternary trace was not replayed anew; its prior verification record was read.

The optimal scalar Fano construction already uses one weighted partial
permutation per host edge: each gadget has distinct rows and columns,
and the gadgets are coordinate-disjoint. Thus dense blocks give no
larger scalar optimum than this sparse class on that host over either
certified field. Coding does beat single-helper-total copying: with 21
loop cells, that class has at most $21+\lfloor28/2\rfloor=35$ free
symbols, since every nonloop functional cycle uses at least two cells.
This is a different comparison.

The [basis and Clebsch certificates][diagonal] likewise attain their
lower bounds with partial translation-permutation blocks. Their
restricted two-sector enumeration is not an unrestricted dense search.
Individual irreducible-sector gains and the earlier generic twisted-block
numerics also do not certify a full-array host code without one shared
decoder realizing all sectors.

**Cyclic window two.** The [difference construction][cyclic] attains
Paper 17's universal whole-row upper bound over every finite alphabet.
Its rows are trees of differences between shared pair variables; two
helper rows recover a target by subtracting two path sums. At $d=5$
its graphic rank agrees with every subset value of the previous
Shannon witness, so the full capacity is 19. These decoders can use
growing scalar support inside their two helper rows. They do not settle
the sparse one-class problem with two scalar helpers per entry, or show
that sparse and dense optimal capacities differ. Their gain over
ordinary pairing is $d-1$.

## 4. What remains undecided

No result in this audit supplies, at fixed window three, a family whose
excess over an exhibited pairing-and-loop baseline divided by $d$ tends
to infinity. A single finite instance cannot establish that assertion.
Ordinary transpose pairing presupposes $r\in\rho(r)$; a general host
requires an explicitly supported pairing or another stated baseline.

Small hosts have many near cells. If the row relation has forward and
reverse degrees at most $w,w'$, its number $N_3$ of row/column pairs at
incidence distance at most three satisfies

$$N_3\le dw\,[1+(w-1)(w'-1)].$$

Indeed a column reaches at most $w$ rows, then at most $w'-1$ new
columns per row, then at most $w-1$ new rows per such column. At
$w=w'=3$ the bound is $15d$, becoming less than ten percent of $d^2$
only for $d>150$. This is a sufficient counting threshold, not a
proposed search size or a capacity bound. All Fano and projective-plane
cells are near; the basis host at $d=8,w=3$ has 32 of its 64 cells near.

A prospective global rank inequality must accommodate these finite
benchmarks and vector lanes. An optimal-capacity reduction to sparse
blocks would itself require a new theorem; an exact, code-preserving
one-block reduction is already false. No further tower-layout or dense
optimization search is justified by the reformulations alone.

[host]: row-spread-of-cones.md#17-swap-lifts-and-the-limit-of-fixed-radius-statistics
[shear]: shear-loop-controls.md
[simplex]: ../tools/simplex-calibration/README.md
[diagonal]: diagonal-code-calibration.md#4-the-finite-diagonal-coupling-test
[cyclic]: row-spread-of-cones.md#27-exact-capacity-at-window-two
[Hall]: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Combinatorics/Hall/Finite.lean
