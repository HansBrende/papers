# A robust Fano pattern and its counting limit

Hans Brende and GPT-6 Astra, 14 November 2026.
**Status: written proofs, independently reviewed, not Lean-verified.**
This records the bounded test of the paid macro approach. It gives a
relation-only sufficient condition beyond an exact coarse Fano quotient,
and shows why counting that condition cannot yield a deficit uniform in
the window. It makes no claim of a lower bound on actual code capacity.

## 1. A certificate from the columns that fit

Let d=7n. Partition both the rows and columns of a d×d whole-row host
into seven labelled groups of size n. Label row groups by Fano points
and column groups by Fano lines. A fine column in line group ℓ is
**good** when every one of its actual helper rows lies in a point
group incident with ℓ. Let G be the number of good fine columns,
and B=d−G the number of other columns. No symmetry, code linearity,
or bound on the helpers of a bad column is assumed.

Then the full Shannon value satisfies

$$\boxed{\operatorname{Sh}\le d^2-\frac4{21}dG.}$$

To prove this, group the cells into n×n macro blocks and condition on
the 21 incident blocks, denoted Z. For a residual block in line group
ℓ, all coordinates of its good fine columns are determined by the
three macro helper rows. They are therefore determined after
conditioning on the twelve residual helper blocks and Z. If B_ℓ of
the n columns in that group are bad, its conditional recovery error
is at most nB_ℓ by the singleton capacities. There are four residual
blocks in each line group, so the sum of the 28 block errors is at
most 4nB. The [paid Fano inequality](fano-soft-recovery.md) gives

$$h(\text{full})\le \frac{119}{3}n^2+\frac43nB
 =d^2-\frac4{21}dG.$$

This argument uses only polymatroid inequalities. It is uniform in
the alphabet and applies to arbitrary nonlinear codes. In particular,
a code of rate at least 1−δ forces G≤(21/4)δd **in every** balanced
Fano layout. An exact quotient is the special case G=d.

The premise in information terms is the residual base inequality
c_Sh(Fano)=3, applied to the 28 macro variables with conditioning Z.
The [grid inequality](triangle-free-shannon-gap.md#3-a-paid-inequality-and-an-information-constant)
similarly supplies c_Sh(grid)≤30/11. These are constants of the
specified residual bases; a macro projection does not establish the
same constant for arbitrary fine-variable distributions on the entire
host. The incident blocks are separately charged.

## 2. High-order random hosts evade every such counting invoice

Fix ε,γ∈(0,1), and choose a fixed integer w large enough that

$$w\varepsilon^2>2\log2,\qquad
w\gamma\log(7/3)>\log98.$$

Here logarithms are natural. For each d divisible by seven, let each
column independently choose w uniformly random row indices, with
replacement; its helper set contains the distinct choices. The maximum
forward window is at most w. No bounded reverse-degree or native-machine
realization claim is made.

**Few good columns, in every balanced layout.** For a fixed layout,
each column is good with probability (3/7)^w, independently of other
columns. There are at most 7^(2d) row/column label assignments. For any
chosen set of at least γd columns, the probability that all are good
is at most (3/7)^(wγd). A union bound over at most 2^d possible sets
of columns gives

$$\Pr[\text{some balanced layout has }G\ge\gamma d]
\le[98(3/7)^{w\gamma}]^d\longrightarrow0.$$

**Order rate close to one.** Put r=⌈εd⌉. For fixed r rows and r columns,
the probability of an empty incidence rectangle is
(1−r/d)^(wr)≤exp(−wr²/d). There are at most 4^d such rectangle choices,
so the probability of any empty rectangle is at most

$$\exp[(2\log2-w\varepsilon^2)d]\longrightarrow0.$$

In any row order, take its final r rows. At most r−1 columns can have
all their helpers outside those rows; otherwise there would be an empty
r×r rectangle. Thus at least d−r+1 columns have last-helper position
at least d−r+1, giving

$$\sigma\ge(d-r+1)^2\ge(1-\varepsilon)^2d^2.$$

Both properties hold simultaneously with probability tending to one.
Consequently, for arbitrarily high order rates, there are fixed-window
families on which even the best balanced Fano layout has G<γd.
Optimizing the certificate in Section 1 can then certify a deficit of
at most 4γ/21. Since γ can be arbitrarily small as w increases, this
**good-column-count relaxation** cannot prove a deficit uniform in w.

This does not say that the recovery-error sum itself must be large:
correlations in an actual code or polymatroid may make it much smaller
than the singleton count used above. Neither Sh nor c_Sh is lower-bounded
by this argument. It closes the proposed counting shortcut, not the
paid inequality, the Shannon program or the transposition question.

## 3. Consequence for the next target

The finite and high-girth gaps show that Shannon methods have more
power than order without local triangles. The remaining task needs
information about conditional errors or a different incidence identity
on high-order hosts. An exact Fano quotient, or the number of columns
that nearly fit one, is not a universal substitute. The plane conjecture
remains a concrete route to high-order bases; the counting pass here
supplies no reason to enlarge a finite search.
