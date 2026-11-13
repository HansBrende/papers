# Far cells and the Clebsch control

Hans Brende and GPT-6 Astra, 13 November 2026.

**Fronts D1/D9.** The Clebsch code from Paper 4 gives a whole-row code with
ten independent bits on sixteen far cells while all near cells are fixed.
The diagonal embedding, exact near/far partition, recovery and cardinality
are Lean-verified in [FarClebsch.lean](../FarClebsch.lean). The geometric
distance-five explanation and the other scope statements below have
written proofs. This reuses an established code; it is not a new capacity
calculation or a counterexample to the full-array near-cell conjecture.

## 1. The precise counterexample

For a helper-row relation $\rho$, put an undirected incidence edge between
row $i$ and column $c$ when $i\in\rho(c)$. A cell $(i,c)$ is *near* when
these two vertices have distance at most three. Equivalently,

$$i\in\rho(c)\quad\text{or}\quad
\exists a,j:\ a\in\rho(c),\ a\in\rho(j),\ i\in\rho(j).$$

This is the literal Lean predicate `NearThree`. A *far* cell is any other
cell; disconnected pairs are also far. In the example every far distance
is exactly five.

Let $H$ be the Clebsch graph on $\mathbb F_2^4$, with
$i\sim j$ when $i\mathbin\oplus j\in\{1,2,4,8,15\}$. Set $d=16$ and
$\rho(c)=N_H(c)$. Both forward and reverse degrees are five.

**Proposition 1 (far-half fails).** There is a binary whole-row code of
cardinality $2^{10}$ for this relation. Its far set consists of the sixteen
diagonal cells, and every one of the 240 near cells is zero throughout the
code. Thus its far-set information exceeds $16/2=8$ bits.

*Outline of the formal proof.* Paper 4's
[`clebschCode`](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/lean/MotionDepthCodes/Clebsch.lean)
has $2^{10}$ words and satisfies
$x_c=\sum_{i\in N_H(c)}x_i$ over $\mathbb F_2$. Put $x_i$ in cell $(i,i)$
and zero everywhere else. The supplied rows $\rho(c)$ contain every
diagonal entry used to recover $(c,c)$; the other entries of column $c$
are constant. The generic lemma `diagonalCode_isWholeRow` formalizes this
embedding for any alphabet and any storage code, with no symmetry or
linearity premise. The embedding is injective and preserves cardinality.

The finite kernel-checked lemma `clebsch_nearThree_iff` proves that
`NearThree clebschNbhd i c` holds exactly when $i\ne c$.
`clebsch_farCells_card`, `farClebschCode_near_zero` and
`farClebschCode_exceeds_half` give the claimed count, freezing and strict
inequality. No new axiom or unproved premise is introduced. ∎

For the distance interpretation, the integer adjacency matrix satisfies

$$A^2=3I-2A+2J,\qquad A^3=7A-6I+6J.$$

No diagonal pair has a length-one or length-three walk. The Cayley steps
$1,2,4,8,15$ give a length-five walk from each row vertex to its same-index
column vertex. For unequal indices, adjacency gives distance one and
nonadjacency gives $(A^3)_{ij}=6$, hence distance three. These identities
also follow by the exact control script below.

The helper graph on the far cells is precisely undirected Clebsch: every
used helper is mutual. The matching $i\leftrightarrow i\mathbin\oplus1$
has eight pairs, but the code has dimension ten. A mutual-helper graph
need not have the capacity of its pair-matching construction.
This does not show an advantage from adding one-way helpers to the full
mutual-helper graph.

Paper 4, [Corollary H4](../../Curved-Motion-Depth-Reduction-and-Storage-Codes-for-Matrix-Transposition-on-Tapes/paper/sections/codes.tex),
also bounds every Clebsch storage code over $q$ symbols by $q^{10}$.
After fixing all off-diagonal cells, the diagonal projection of any code
for this relation is a Clebsch storage code. Thus ten is the exact binary
far-code dimension, with the corresponding upper bound over all alphabets.
Four independent binary lanes give 40 bits on the 64 far bits at the
canonical width $b(16)=4$.

The incidence host has a four-cycle
$R_0,C_1,R_3,C_2,R_0$. It is neither cubic nor of girth ten or twelve;
the separately restricted high-girth question remains open.

## 2. What the counterexample does not imply

Write $N=N_3$ for the number of near cells and $F=d^2-N$ for the number
of far cells. The following two proposed statements differ:

- **Conditioned far-half:** after fixing all near coordinates, every
  resulting code has at most $q^{F/2}$ words. Proposition 1 refutes this.
- **Global near-cell allowance:** some absolute $C_0$ satisfies
  $|C|\le q^{d^2/2+C_0N}$ for all whole-row codes. This single gadget leaves the assertion undecided; the later
  [hypercube construction](diagonal-code-calibration.md) refutes a constant
  independent of the helper window. A window-dependent additive bound
  remains open.

The first would imply the second with $C_0=1/2$ by counting at most
$q^N$ fibres. The converse does not follow. A code with near cells fixed
and $F/2+e$ independent symbols has full-array exponent
$d^2/2+e-N/2$; it violates the proposed global bound only if
$e>(C_0+1/2)N$. In the Clebsch example $e=2$ and $N=240$, and the full
code dimension ten is far below $d^2/2=128$.

Nor does a finite far gadget automatically amplify to positive-density
excess at a fixed window or at any specified window exponent. That needs
compatible embeddings, an accounting of all other cells, controlled
helper windows and control of newly created short incidence paths.
Distance five alone supplies none of these obligations.

An equivalent global formulation makes the missing compensation explicit.
For a uniform random word $X$ of a nonempty code, measure entropy in
base-$q$ units and define

$$D_N=N-H_q(X_{\rm near}),\qquad
E_F=H_q(X_{\rm far}\mid X_{\rm near})-F/2.$$

The chain rule gives

$$\log_q|C|=d^2/2+N/2+E_F-D_N.$$

Thus the global bound asks for
$E_F\le D_N+(C_0-1/2)N$, not $E_F\le0$. Clebsch has $E_F=2$ and
$D_N=240$. This is a reformulation, not a new entropy bound. The native
program ultimately needs a common positive deficit across fixed windows;
it does not require proving this particular stronger quantitative bound.

## 3. Counting near cells and interpreting the component theorem

If forward degree is at most $w\ge1$ and reverse degree at most $w'\ge1$,
nonbacktracking paths of length one or three give

$$N_3\le\min\{d^2,\;dw[1+(w'-1)(w-1)]\}.$$

This is an upper bound, not an asymptotic equality. Forward degree alone
does not give $N_3=O(d)$: the relation $\rho(c)=\{0,c\}$ has forward
degree at most two, but every row-column pair is within distance three
via the common hub row. Its reverse degree is unbounded.

The now-refuted global conjecture with $C_0\ge0$ would nevertheless imply the fixed-forward-window
half-rate limit using the existing paid reverse-degree reduction. This
conditional implication does not rescue the refuted premise. Fix an
integer $R\ge1$. Freeze
rows used by more than $R$ columns, costing at most $wd^2/(R+1)$ symbols,
and remove these rows from every helper set. Each conditional code remains
on the full balanced grid and has reverse degree at most $R$. Applying the
conjecture to its fibres would give

$$\log_q|C|\le d^2/2+\frac{wd^2}{R+1}
 +C_0dw[1+(R-1)(w-1)].$$

Fix $w,R$, let $d$ grow, then let $R$ grow. This yields half rate in the
limit, but does not give an additive $O_w(d)$ error from forward degree
alone.

Our [small-component theorem](grid-labellings-and-amplified-codes.md)
charges distances beyond three. If every coordinate component has size at
most $s$, its two incidence ports, when connected, are joined by a path
of length at most $2s-1$. For a balanced grid of $L=d^2b$ coordinates,
let $N_r$ count row-column pairs at distance at most $r$. Its proof gives
the direct radius bound

$$\log_q|C|\le\frac{L+bN_{2s-1}}2.$$

Indeed, freeze the coordinates with connected paired ports (at most
$bN_{2s-1}$), then apply Paper 5's
[separated-components lemma](../../Directed-Recovery-Structures-in-Tape-Computations/paper/sections/directed-coding.tex)
(`lem:dc-components`, Lean `storageCode_card_le_of_separated_components`). This does
not replace $N_{2s-1}$ by $N_3$. The Clebsch diagonal example explicitly
uses connected paired ports at distance five.

For completeness, the window-one baseline also depends on the relation.
If each helper set is empty or a singleton, let $n_i$ count the columns
whose helper is row $i$, sorted as $n_{(1)}\ge\cdots\ge n_{(d)}$.
The exact maximum cardinality over $q$ symbols is

$$q^{\sum_{j=1}^d jn_{(j)}}
=q^{\sum_i n_i+\sum_{i<j}\min(n_i,n_j)}.$$

To prove the upper bound, order rows by decreasing $n_i$. In every column
whose helper is the $j$th row, retain its first $j$ entries; the remaining
entries can be recovered in row order. Empty-helper columns are constant.
For attainment, keep the $n_i$ self-readable entries in row $i$ free and,
for each unordered pair of rows, pair $\min(n_i,n_j)$ entries across their
two column groups. Set unmatched entries to a constant. Each pair reads
its mate from the permitted helper row. Thus the pairing value
$d(d+1)/2$ is attained by a bijective singleton relation; a constant
singleton relation has exponent only $d$. This is elementary order-bound
bookkeeping, not a new general capacity theorem.

## 4. Reproduction and reuse

From the repository root, the standard-library control checks the
integer adjacency identities, all row-column distances, exact binary rank
and the eight-pair baseline:

```sh
python3 lean-backlog/tools/clebsch_far_control.py
```

Check the formal wrapper with the existing pinned dependencies:

```sh
cd High-Rate-Separated-Storage-Codes-and-Tape-Transposition/lean
lake env python3 ../../lean-backlog/check.py FarClebsch
```

As with other single-module checks, `StatementsRowSpread` must already be
built; the full `check.py` command builds the chain in order. The script
also checks Paper 4's small Clebsch module directly, without duplicating
its proof. The new formal endpoints use only `propext`, `Classical.choice`
and `Quot.sound`.
